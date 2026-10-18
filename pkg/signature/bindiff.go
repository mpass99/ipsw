package signature

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"io/fs"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"

	"github.com/apex/log"
	"github.com/glebarez/sqlite"
	"gorm.io/gorm"
	"gorm.io/gorm/logger"

	"github.com/blacktop/go-macho"
	"github.com/blacktop/go-macho/types"
	"github.com/blacktop/go-plist"
	"github.com/blacktop/ipsw/internal/magic"
)

// binDiffFunction is a matched function pair (KDK address, kernelcache address).
type binDiffFunction struct {
	Address1   int64
	Address2   int64
	Similarity float64
}

// binDiffInsn is a single matched instruction pair (KDK address, kernelcache address)
// together with the similarity of the function pair it belongs to.
type binDiffInsn struct {
	Function1  int64
	Address1   int64
	Address2   int64
	Similarity float64
}

// SymbolAliases holds further names of addresses in a SymbolMap.
type SymbolAliases map[uint64][]string

type binDiffFile struct {
	Filename    string
	Exefilename string
	Hash        string
}

// SymbolicateMachOWithBinDiff symbolicates a kernelcache using a KDK-like directory that
// contains a BinDiff database (KDK Mach-O vs. kernelcache fileset entry) next to every Mach-O.
//
// Function symbols come from the BinDiff function matches. Imported and exported symbols
// (including data symbols) are recovered from a cross-fileset dependency graph: every
// import of a kext must resolve to an address inside the providing fileset entry, and
// every importer that references it in a matched instruction votes for that address.
func (sm SymbolMap) SymbolicateMachOWithBinDiff(kc *macho.File, kdkPath string, quiet bool) (SymbolAliases, error) {
	if kc.FileTOC.FileHeader.Type != types.MH_FILESET {
		return nil, fmt.Errorf("BinDiff symbolication requires an MH_FILESET kernelcache")
	}
	bundleIDs := listBundleIDs(kc)
	pathsForBundles, err := walkKDK(kdkPath, bundleIDs)
	if err != nil {
		return nil, err
	}
	for id := range bundleIDs {
		if _, ok := pathsForBundles[id]; !ok {
			log.Warnf("No KDK Mach-O found for kernelcache fileset entry %s", id)
		}
	}

	g, err := newDepGraph(kc, pathsForBundles)
	if err != nil {
		return nil, err
	}
	defer g.Close()

	if err := g.recover(quiet); err != nil {
		return nil, err
	}

	primary := g.symbolMap()
	for addr, name := range primary {
		if err := sm.Add(addr, name); err != nil {
			log.WithError(err).Debug("Skipping conflicting BinDiff symbol")
		}
	}

	return g.extraNames(primary), nil
}

func listBundleIDs(kc *macho.File) map[string]bool {
	bundleIDs := make(map[string]bool)
	for _, entry := range kc.FileSets() {
		bundleIDs[entry.EntryID] = true
	}
	return bundleIDs
}

func isMachOFile(path string) bool {
	ok, err := magic.IsMachO(path)
	return err == nil && ok
}

func isVariantBuild(name string) bool {
	return strings.Contains(name, "_development") || strings.Contains(name, "_kasan")
}

// walkKDK maps every bundle ID of the kernelcache to the release Mach-O in the KDK.
// The executable is taken from CFBundleExecutable, so additional Mach-Os in a bundle
// (e.g. tools, _development or _kasan variants) are ignored.
func walkKDK(kdkPath string, bundleIDs map[string]bool) (map[string]string, error) {
	bundlePathMap := make(map[string]string)
	var kernels []string

	err := filepath.WalkDir(kdkPath, func(path string, d fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			if strings.HasSuffix(d.Name(), ".dSYM") || d.Name() == "Resources" {
				return filepath.SkipDir
			}
			return nil
		}

		if (d.Name() == "kernel" || strings.HasPrefix(d.Name(), "kernel.")) && filepath.Base(filepath.Dir(path)) == "Kernels" {
			if !isVariantBuild(d.Name()) && filepath.Ext(d.Name()) != ".BinDiff" && filepath.Ext(d.Name()) != ".BinExport" && isMachOFile(path) {
				kernels = append(kernels, path)
			}
			return nil
		}

		if d.Name() != "Info.plist" {
			return nil
		}

		content, err := os.ReadFile(path)
		if err != nil {
			log.Warnf("Failed to read %s: %v", path, err)
			return nil
		}
		var infoPlist map[string]any
		if err := plist.NewDecoder(bytes.NewReader(content)).Decode(&infoPlist); err != nil {
			log.Warnf("Failed to decode %s: %v", path, err)
			return nil
		}
		bundleID, _ := infoPlist["CFBundleIdentifier"].(string)
		executable, _ := infoPlist["CFBundleExecutable"].(string)
		if bundleID == "" || executable == "" || !bundleIDs[bundleID] {
			return nil
		}

		dir := filepath.Dir(path)
		for _, candidate := range []string{filepath.Join(dir, "MacOS", executable), filepath.Join(dir, executable)} {
			if isMachOFile(candidate) {
				if prev, ok := bundlePathMap[bundleID]; ok && prev != candidate {
					log.Warnf("Multiple KDK Mach-Os for %s: %s and %s", bundleID, prev, candidate)
				}
				bundlePathMap[bundleID] = candidate
				break
			}
		}
		return nil
	})
	if err != nil {
		return nil, err
	}

	if kernel := selectKernel(kernels); kernel != "" && bundleIDs["com.apple.kernel"] {
		bundlePathMap["com.apple.kernel"] = kernel
	}

	return bundlePathMap, nil
}

// selectKernel picks the KDK kernel that a BinDiff database was created for.
func selectKernel(kernels []string) string {
	if len(kernels) == 0 {
		return ""
	}
	for _, kernel := range kernels {
		if _, err := findBinDiffForMachO(kernel, "com.apple.kernel"); err == nil {
			return kernel
		}
	}
	sort.Strings(kernels)
	log.Warnf("No BinDiff database references any of the KDK kernels, using %s", kernels[0])
	return kernels[0]
}

// openBinDiffDB opens a BinDiff database read-only.
func openBinDiffDB(path string) (*gorm.DB, error) {
	return gorm.Open(sqlite.Open(path+"?_pragma=query_only(1)"), &gorm.Config{Logger: logger.Default.LogMode(logger.Silent)})
}

func closeBinDiffDB(db *gorm.DB) {
	sqlDB, err := db.DB()
	if err == nil {
		err = sqlDB.Close()
	}
	if err != nil {
		log.Debugf("Failed to close BinDiff database: %v", err)
	}
}

// findBinDiffForMachO returns the BinDiff database in the Mach-O's directory that compares
// the Mach-O with the kernelcache fileset entry bundleID. File names are unreliable (BinDiff
// truncates them), so the decision is made on the database's file table.
func findBinDiffForMachO(file, bundleID string) (string, error) {
	dir := filepath.Dir(file)
	entries, err := os.ReadDir(dir)
	if err != nil {
		return "", err
	}

	type candidate struct {
		path    string
		score   int
		modTime int64
	}
	var candidates []candidate
	for _, entry := range entries {
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".BinDiff") {
			continue
		}
		path := filepath.Join(dir, entry.Name())
		db, err := openBinDiffDB(path)
		if err != nil {
			continue
		}
		var files []binDiffFile
		err = db.Raw("SELECT filename as Filename, exefilename as Exefilename, hash as Hash FROM file ORDER BY id").Scan(&files).Error
		closeBinDiffDB(db)
		if err != nil {
			log.Warnf("Failed to read BinDiff database %s: %v", path, err)
			continue
		}
		if len(files) != 2 || files[1].Filename != bundleID {
			continue
		}
		c := candidate{path: path}
		// The SHA-256 identifies the Mach-O even after it was renamed.
		if files[0].Hash != "" && files[0].Hash == fileSHA256(file) {
			c.score += 4
		}
		if filepath.Base(files[0].Exefilename) == filepath.Base(file) {
			c.score += 2
		}
		if files[0].Filename == filepath.Base(file) {
			c.score++
		}
		if c.score == 0 {
			continue
		}
		if info, err := entry.Info(); err == nil {
			c.modTime = info.ModTime().UnixNano()
		}
		candidates = append(candidates, c)
	}
	if len(candidates) == 0 {
		return "", fmt.Errorf("%w: no BinDiff for %s (%s)", os.ErrNotExist, bundleID, file)
	}
	sort.Slice(candidates, func(i, j int) bool {
		if candidates[i].score != candidates[j].score {
			return candidates[i].score > candidates[j].score
		}
		return candidates[i].modTime > candidates[j].modTime
	})
	return candidates[0].path, nil
}

var fileHashes sync.Map // path -> hex SHA-256

func fileSHA256(path string) string {
	if h, ok := fileHashes.Load(path); ok {
		return h.(string)
	}
	f, err := os.Open(path)
	if err != nil {
		return ""
	}
	defer f.Close()
	hash := sha256.New()
	if _, err := io.Copy(hash, f); err != nil {
		return ""
	}
	h := hex.EncodeToString(hash.Sum(nil))
	fileHashes.Store(path, h)
	return h
}

func readBinDiffFunctions(path string) ([]binDiffFunction, error) {
	db, err := openBinDiffDB(path)
	if err != nil {
		return nil, fmt.Errorf("failed to open BinDiff database %s: %w", path, err)
	}
	defer closeBinDiffDB(db)
	var functions []binDiffFunction
	if err := db.Raw("SELECT address1 as Address1, address2 as Address2, similarity as Similarity FROM function").Scan(&functions).Error; err != nil {
		return nil, fmt.Errorf("failed to read functions of %s: %w", path, err)
	}
	return functions, nil
}

func readBinDiffInstructions(path string) ([]binDiffInsn, error) {
	db, err := openBinDiffDB(path)
	if err != nil {
		return nil, fmt.Errorf("failed to open BinDiff database %s: %w", path, err)
	}
	defer closeBinDiffDB(db)
	var insns []binDiffInsn
	if err := db.Raw(`SELECT f.address1 as Function1, i.address1 as Address1, i.address2 as Address2, f.similarity as Similarity
		FROM instruction i JOIN basicblock b ON i.basicblockid = b.id JOIN function f ON b.functionid = f.id`).Scan(&insns).Error; err != nil {
		return nil, fmt.Errorf("failed to read instructions of %s: %w", path, err)
	}
	return insns, nil
}
