package signature

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"io"
	"math"
	"slices"
	"sort"
	"strings"

	"github.com/apex/log"
	"github.com/blacktop/go-macho"
	"github.com/blacktop/go-macho/pkg/fixupchains"
	"github.com/blacktop/go-macho/types"
)

// Symbol sources. A recovered symbol remembers which sources voted for its address.
const (
	srcBinDiff uint16 = 1 << iota // BinDiff function match
	srcInsn                       // matched instruction referencing the symbol
	srcVtable                     // aligned vtable slot
	srcGraph                      // elimination over the inter-fileset pointer graph
	srcKmod                       // kmod_info structure scan
	srcLinear                     // linear alignment of a recovered function BinDiff did not match
	srcPtr                        // data symbol located by the pointers it contains
	srcOrder                      // GOT slot order between recovered anchors
	srcLayout                     // same relative position between recovered neighbors
)

var sourceNames = []struct {
	bit  uint16
	name string
}{
	{srcBinDiff, "bindiff"},
	{srcInsn, "insn"},
	{srcVtable, "vtable"},
	{srcGraph, "graph"},
	{srcKmod, "kmod"},
	{srcLinear, "linear"},
	{srcPtr, "ptr"},
	{srcOrder, "order"},
	{srcLayout, "layout"},
}

/* ARM64 reference scanner */

type refKind uint8

const (
	refCall   refKind = iota + 1 // BL
	refBranch                    // B
	refAddr                      // ADRP + ADD
	refLoad                      // ADRP + LDR
	refStore                     // ADRP + STR
)

type codeRef struct {
	kind   refKind
	ptr    bool // 64-bit integer load, i.e. potentially a pointer (GOT) load
	target uint64
}

func (r codeRef) isFlow() bool { return r.kind == refCall || r.kind == refBranch }

// scanCodeRefs records every direct branch and every ADRP based memory reference.
// The reference of an ADRP pair is recorded at the address of the ADD/LDR/STR, which is
// the instruction that BinDiff matches together with the ADRP.
func scanCodeRefs(data []byte, base uint64, out map[uint64]codeRef) {
	var page [32]uint64
	var valid uint32
	for i := 0; i+4 <= len(data); i += 4 {
		pc := base + uint64(i)
		insn := binary.LittleEndian.Uint32(data[i:])
		rd := insn & 31
		switch {
		case insn&0x9F000000 == 0x90000000: // ADRP
			imm := uint32((insn>>5)&0x7FFFF)<<2 | (insn>>29)&3
			off := int64(int32(imm<<11)>>11) << 12
			page[rd] = uint64(int64(pc&^0xFFF) + off)
			valid |= 1 << rd
			continue
		case insn&0x7C000000 == 0x14000000: // B / BL
			off := int64(int32(insn<<6) >> 4)
			kind := refBranch
			if insn&0x80000000 != 0 {
				kind = refCall
				valid &^= 0x7FFFF // caller-saved registers
			} else {
				valid = 0
			}
			out[pc] = codeRef{kind: kind, target: uint64(int64(pc) + off)}
			continue
		case insn&0xFE000000 == 0xD6000000: // BR/BLR/RET (+ authenticated variants)
			valid = 0
			continue
		case insn&0xFFC00000 == 0x91000000: // ADD (immediate, 64-bit, no shift)
			rn := (insn >> 5) & 31
			if valid&(1<<rn) != 0 {
				out[pc] = codeRef{kind: refAddr, target: page[rn] + uint64((insn>>10)&0xFFF)}
			}
		case insn&0x3B000000 == 0x39000000: // LDR/STR (unsigned immediate)
			rn := (insn >> 5) & 31
			size := insn >> 30
			simd := (insn>>26)&1 == 1
			opc := (insn >> 22) & 3
			scale := size
			if simd && opc >= 2 {
				scale = 4
			}
			if valid&(1<<rn) != 0 {
				ref := codeRef{kind: refStore, target: page[rn] + uint64((insn>>10)&0xFFF)<<scale}
				if opc != 0 {
					ref.kind = refLoad
					ref.ptr = size == 3 && !simd && opc == 1
				}
				out[pc] = ref
			}
			if opc == 0 || simd { // store or SIMD register: no general purpose register written
				continue
			}
		case insn&0x7E000000 == 0x34000000, insn&0x7E000000 == 0x36000000, insn&0xFF000010 == 0x54000000:
			continue // CBZ/CBNZ, TBZ/TBNZ, B.cond: no register written
		case insn&0x0A000000 == 0x08000000 && (insn>>22)&1 == 0:
			continue // other stores
		}
		if rd != 31 {
			valid &^= 1 << rd
		}
	}
}

/* KDK images */

type kdkFixup struct {
	bind      bool
	name      string
	addend    int64
	target    uint64 // rebase target
	auth      bool
	diversity uint64
}

type kdkImage struct {
	id     string
	m      *macho.File
	closer io.Closer

	exports      map[string]uint64 // defined external symbols
	exportIsText map[string]bool
	symsByAddr   map[uint64][]string // all defined symbols
	symAddrs     []uint64            // sorted keys of symsByAddr
	funcStarts   []uint64            // sorted LC_FUNCTION_STARTS
	sparse       bool                // most functions have no symbol (e.g. an extracted KDK)

	// only populated for images taking part in the graph
	fixups   map[uint64]kdkFixup
	imports  map[string][]kdkFixup
	stubSlot map[uint64]uint64
	refs     map[uint64]codeRef
}

func openKDKImage(id, path string) (*kdkImage, error) {
	img := &kdkImage{
		id:           id,
		exports:      make(map[string]uint64),
		exportIsText: make(map[string]bool),
		symsByAddr:   make(map[uint64][]string),
	}

	if fat, err := macho.OpenFat(path); err == nil {
		for _, arch := range fat.Arches {
			if arch.CPU != types.CPUArm64 {
				continue
			}
			if img.m == nil || arch.SubCPU&types.CpuSubtypeMask == types.CPUSubtypeArm64E {
				img.m = arch.File
			}
		}
		if img.m == nil {
			fat.Close()
			return nil, fmt.Errorf("no arm64 slice in %s", path)
		}
		img.closer = fat
	} else {
		m, err := macho.Open(path)
		if err != nil {
			return nil, fmt.Errorf("failed to open %s: %w", path, err)
		}
		img.m = m
		img.closer = m
	}

	if img.m.Symtab != nil {
		for _, sym := range img.m.Symtab.Syms {
			if sym.Name == "" || sym.Type.IsDebugSym() || !sym.Type.IsDefinedInSection() || sym.Sect == 0 {
				continue
			}
			img.symsByAddr[sym.Value] = append(img.symsByAddr[sym.Value], sym.Name)
			if sym.Type.IsExternalSym() && !sym.Type.IsPrivateExternalSym() {
				img.exports[sym.Name] = sym.Value
				if int(sym.Sect) <= len(img.m.Sections) {
					img.exportIsText[sym.Name] = img.m.Sections[sym.Sect-1].Seg == "__TEXT_EXEC"
				}
			}
		}
	}
	for addr := range img.symsByAddr {
		img.symAddrs = append(img.symAddrs, addr)
	}
	sort.Slice(img.symAddrs, func(i, j int) bool { return img.symAddrs[i] < img.symAddrs[j] })
	for _, fn := range img.m.GetFunctions() {
		img.funcStarts = append(img.funcStarts, fn.StartAddr)
	}
	sort.Slice(img.funcStarts, func(i, j int) bool { return img.funcStarts[i] < img.funcStarts[j] })
	named := 0
	for _, fn := range img.funcStarts {
		if _, ok := img.symsByAddr[fn]; ok {
			named++
		}
	}
	img.sparse = len(img.funcStarts) > 0 && named*2 < len(img.funcStarts)

	return img, nil
}

func (img *kdkImage) Close() {
	if img.closer != nil {
		img.closer.Close()
	}
}

// loadFixups parses the chained fixups of the KDK image (binds = imports).
func (img *kdkImage) loadFixups() error {
	img.fixups = make(map[uint64]kdkFixup)
	img.imports = make(map[string][]kdkFixup)
	if !img.m.HasDyldChainedFixups() {
		return nil
	}
	dcf, err := img.m.DyldChainedFixups()
	if err != nil {
		return err
	}
	if _, err := dcf.Parse(); err != nil {
		return err
	}
	base := img.m.GetBaseAddress()
	for _, start := range dcf.Starts {
		for _, fx := range start.Fixups {
			addr, err := img.m.GetVMAddress(fx.Offset())
			if err != nil {
				continue
			}
			var f kdkFixup
			switch v := fx.(type) {
			case fixupchains.Bind:
				f.bind = true
				f.name = v.Name()
				if s, ok := fx.(interface{ SignExtendedAddend() int64 }); ok {
					f.addend = s.SignExtendedAddend()
				} else {
					f.addend = int64(v.Addend())
				}
			case fixupchains.Rebase:
				f.target = v.Target()
				if f.target < base { // offset from the preferred load address
					f.target += base
				}
			default:
				continue
			}
			if a, ok := fx.(fixupchains.Auth); ok {
				f.auth = true
				f.diversity = a.Diversity()
			}
			img.fixups[addr] = f
			if f.bind {
				img.imports[f.name] = append(img.imports[f.name], f)
			}
		}
	}
	return nil
}

func isGotSection(sec *types.Section) bool {
	return sec != nil && (sec.Name == "__got" || sec.Name == "__auth_got")
}

// loadRefs scans the code of the KDK image and resolves the stubs to their GOT slots.
func (img *kdkImage) loadRefs() error {
	img.refs = make(map[uint64]codeRef)
	img.stubSlot = make(map[uint64]uint64)
	for _, sec := range img.m.Sections {
		if sec.Seg != "__TEXT_EXEC" && !sec.Flags.IsPureInstructions() {
			continue
		}
		data, err := sec.Data()
		if err != nil {
			return fmt.Errorf("failed to read %s.%s of %s: %w", sec.Seg, sec.Name, img.id, err)
		}
		if strings.Contains(sec.Name, "stubs") {
			stubSize := uint64(sec.Reserved2)
			if stubSize == 0 {
				stubSize = 16
			}
			refs := make(map[uint64]codeRef)
			scanCodeRefs(data, sec.Addr, refs)
			for pc, ref := range refs {
				if ref.kind == refAddr || ref.kind == refLoad {
					stub := sec.Addr + (pc-sec.Addr)/stubSize*stubSize
					img.stubSlot[stub] = ref.target
				}
			}
			continue
		}
		scanCodeRefs(data, sec.Addr, img.refs)
	}
	return nil
}

// resolveRef translates a code reference of the KDK image into either an import
// (name + addend) or an internal address. viaSlot is set if the reference loads a
// pointer from a GOT slot (directly or through a stub).
func (img *kdkImage) resolveRef(ref codeRef) (name string, addend int64, internal uint64, viaSlot bool) {
	fromSlot := func(slot uint64) (string, int64, uint64, bool) {
		f, ok := img.fixups[slot]
		if !ok {
			return "", 0, 0, false
		}
		if f.bind {
			return f.name, f.addend, 0, true
		}
		return "", 0, f.target, true
	}
	if ref.isFlow() {
		if slot, ok := img.stubSlot[ref.target]; ok {
			if n, a, t, ok := fromSlot(slot); ok {
				return n, a, t, false // calls through stubs become direct calls in the kernelcache
			}
		}
		return "", 0, ref.target, false
	}
	if ref.kind == refLoad && ref.ptr && isGotSection(img.m.FindSectionForVMAddr(ref.target)) {
		if n, a, t, ok := fromSlot(ref.target); ok {
			return n, a, t, true
		}
	}
	return "", 0, ref.target, false
}

// containingSymbol returns the symbol the address belongs to (the closest symbol at or
// before addr in the same section).
func (img *kdkImage) containingSymbol(addr uint64) (uint64, []string, bool) {
	i := sort.Search(len(img.symAddrs), func(i int) bool { return img.symAddrs[i] > addr }) - 1
	if i < 0 {
		return 0, nil, false
	}
	start := img.symAddrs[i]
	sec := img.m.FindSectionForVMAddr(start)
	if sec == nil || addr >= sec.Addr+sec.Size {
		return 0, nil, false
	}
	// An unnamed function between the symbol and addr owns addr (KDKs
	// made from extracted kernelcaches only name some functions).
	j := sort.Search(len(img.funcStarts), func(j int) bool { return img.funcStarts[j] > start })
	if j < len(img.funcStarts) && img.funcStarts[j] <= addr {
		return 0, nil, false
	}
	return start, img.symsByAddr[start], true
}

func (img *kdkImage) symbolEnd(start uint64) uint64 {
	end := uint64(math.MaxUint64)
	i := sort.Search(len(img.symAddrs), func(i int) bool { return img.symAddrs[i] > start })
	if i < len(img.symAddrs) {
		end = img.symAddrs[i]
	}
	if sec := img.m.FindSectionForVMAddr(start); sec != nil && sec.Addr+sec.Size < end {
		end = sec.Addr + sec.Size
	}
	return end
}

/* kernelcache side */

type kcPtr struct {
	target    uint64
	auth      bool
	diversity uint64
}

type kcEntry struct {
	id       string
	m        *macho.File
	sections []*types.Section
	refs     map[uint64]codeRef
}

type addrRange struct {
	start, end uint64
	entry      int
}

/* dependency graph */

type depGraph struct {
	kc       *macho.File
	entries  []*kcEntry
	entryIdx map[string]int
	ranges   []addrRange

	images    map[string]*kdkImage
	binDiffs  map[string]string // bundle ID -> BinDiff database
	providers map[string][]string
	importers map[string][]string // only images in the graph scope
	scope     map[string]bool     // KDK images with fixups that take part in the graph

	kcPtrs  map[uint64]kcPtr
	outPtrs map[string]map[int]map[uint64][]uint64 // importer -> provider entry -> target -> diversities

	// base votes (BinDiff, instruction matches, kmod) and votes derived from the current
	// resolution (recomputed in every iteration)
	votes      map[string]map[uint64]float64
	voteSrc    map[string]map[uint64]uint16
	derived    map[string]map[uint64]float64
	derivedSrc map[string]map[uint64]uint16
	deriving   bool
	ctxBundle  string // origin of the current derived vote (bundle, KDK address)
	ctxLoc     uint64
	seen       map[derivedKey]bool // derived votes are counted once per origin

	funcVotes map[funcKey][]voteRec      // base votes per BinDiff function match
	funcPair  map[funcKey]uint64         // BinDiff function match: KDK function -> kernelcache address
	rejected  map[funcKey]bool           // BinDiff function matches whose votes were removed
	curFunc   *funcKey                   // function match currently voting
	covered   map[string]map[uint64]bool // KDK functions with a trusted BinDiff match
	ptrIndex  map[uint64][]uint64        // kernelcache pointer target -> locations

	resolved map[string]uint64
	resSrc   map[string]uint16
}

type derivedKey struct {
	name   string
	addr   uint64
	src    uint16
	bundle string
	loc    uint64
}

type funcKey struct {
	bundle string
	addr   uint64
}

type voteRec struct {
	key    string
	addr   uint64
	weight float64
	src    uint16
}

func newDepGraph(kc *macho.File, paths map[string]string) (*depGraph, error) {
	g := &depGraph{
		kc:        kc,
		entryIdx:  make(map[string]int),
		images:    make(map[string]*kdkImage),
		binDiffs:  make(map[string]string),
		providers: make(map[string][]string),
		importers: make(map[string][]string),
		scope:     make(map[string]bool),
		kcPtrs:    make(map[uint64]kcPtr),
		outPtrs:   make(map[string]map[int]map[uint64][]uint64),
		votes:     make(map[string]map[uint64]float64),
		voteSrc:   make(map[string]map[uint64]uint16),
		funcVotes: make(map[funcKey][]voteRec),
		funcPair:  make(map[funcKey]uint64),
		rejected:  make(map[funcKey]bool),
		covered:   make(map[string]map[uint64]bool),
		ptrIndex:  make(map[uint64][]uint64),
	}

	for _, fs := range kc.FileSets() {
		m, err := openFilesetEntry(kc, fs)
		if err != nil {
			log.Warnf("Failed to open fileset entry %s: %v", fs.EntryID, err)
			continue
		}
		if text := m.Segment("__TEXT"); text == nil || text.Addr != fs.Addr {
			log.Warnf("Fileset entry lookup for %s returned a different entry, skipping", fs.EntryID)
			continue
		}
		idx := len(g.entries)
		g.entries = append(g.entries, &kcEntry{id: fs.EntryID, m: m, sections: m.Sections})
		g.entryIdx[fs.EntryID] = idx
		for _, seg := range m.Segments() {
			if seg.Name == "__LINKEDIT" || seg.Memsz == 0 {
				continue
			}
			g.ranges = append(g.ranges, addrRange{start: seg.Addr, end: seg.Addr + seg.Memsz, entry: idx})
		}
	}
	sort.Slice(g.ranges, func(i, j int) bool { return g.ranges[i].start < g.ranges[j].start })

	for _, id := range sortedKeys(pathIDs(paths)) {
		path := paths[id]
		if _, ok := g.entryIdx[id]; !ok {
			continue
		}
		img, err := openKDKImage(id, path)
		if err != nil {
			log.Warnf("%v", err)
			continue
		}
		g.images[id] = img
		if bd, err := findBinDiffForMachO(path, id); err == nil {
			g.binDiffs[id] = bd
		} else {
			log.Warnf("No BinDiff database for %s (%s)", id, path)
		}
		for name := range img.exports {
			g.providers[name] = append(g.providers[name], id)
		}
	}

	for _, id := range sortedKeys(imageIDs(g.images)) {
		img := g.images[id]
		if err := img.loadFixups(); err != nil {
			log.Warnf("Failed to parse chained fixups of %s: %v", id, err)
			continue
		}
		g.scope[id] = true
		for name := range img.imports {
			g.importers[name] = append(g.importers[name], id)
		}
	}

	if err := g.loadKCPointers(); err != nil {
		g.Close()
		return nil, err
	}

	return g, nil
}

func (g *depGraph) Close() {
	for _, img := range g.images {
		img.Close()
	}
}

func (g *depGraph) entryOf(addr uint64) int {
	i := sort.Search(len(g.ranges), func(i int) bool { return g.ranges[i].start > addr }) - 1
	if i >= 0 && addr < g.ranges[i].end {
		return g.ranges[i].entry
	}
	return -1
}

func (g *depGraph) kcSection(addr uint64) *types.Section {
	idx := g.entryOf(addr)
	if idx < 0 {
		return nil
	}
	for _, sec := range g.entries[idx].sections {
		if addr >= sec.Addr && addr < sec.Addr+sec.Size {
			return sec
		}
	}
	return nil
}

func (g *depGraph) kcIsText(addr uint64) bool {
	sec := g.kcSection(addr)
	return sec != nil && sec.Seg == "__TEXT_EXEC"
}

// loadKCPointers decodes all chained fixups of the kernelcache that are located in a
// fileset entry of the graph scope.
func (g *depGraph) loadKCPointers() error {
	dcf, err := g.kc.DyldChainedFixups()
	if err != nil {
		return fmt.Errorf("failed to get kernelcache chained fixups: %w", err)
	}
	if _, err := dcf.Parse(); err != nil {
		return fmt.Errorf("failed to parse kernelcache chained fixups: %w", err)
	}
	inScope := make(map[int]string)
	for _, id := range sortedKeys(g.scope) {
		inScope[g.entryIdx[id]] = id
	}
	base := g.kc.GetBaseAddress()
	for _, start := range dcf.Starts {
		for _, fx := range start.Fixups {
			rebase, ok := fx.(fixupchains.Rebase)
			if !ok {
				continue
			}
			loc, err := g.kc.GetVMAddress(fx.Offset())
			if err != nil {
				continue
			}
			from := g.entryOf(loc)
			importer, ok := inScope[from]
			if !ok {
				continue
			}
			p := kcPtr{target: base + rebase.Target()}
			if a, ok := fx.(interface{ IsAuth() uint64 }); ok && a.IsAuth() == 1 {
				p.auth = true
				if d, ok := fx.(fixupchains.Auth); ok {
					p.diversity = d.Diversity()
				}
			}
			g.kcPtrs[loc] = p
			g.ptrIndex[p.target] = append(g.ptrIndex[p.target], loc)

			to := g.entryOf(p.target)
			if to < 0 || to == from || !g.scope[importer] {
				continue
			}
			if g.outPtrs[importer] == nil {
				g.outPtrs[importer] = make(map[int]map[uint64][]uint64)
			}
			if g.outPtrs[importer][to] == nil {
				g.outPtrs[importer][to] = make(map[uint64][]uint64)
			}
			g.outPtrs[importer][to][p.target] = append(g.outPtrs[importer][to][p.target], p.diversity)
		}
	}
	return nil
}

func (g *depGraph) loadEntryRefs(e *kcEntry) error {
	e.refs = make(map[uint64]codeRef)
	for _, sec := range e.sections {
		if sec.Seg != "__TEXT_EXEC" || sec.Size == 0 {
			continue
		}
		data := make([]byte, sec.Size)
		if _, err := g.kc.ReadAtAddr(data, sec.Addr); err != nil {
			return fmt.Errorf("failed to read %s.%s of %s: %w", sec.Seg, sec.Name, e.id, err)
		}
		scanCodeRefs(data, sec.Addr, e.refs)
	}
	return nil
}

func (g *depGraph) interesting(name string) bool {
	return len(g.providers[name]) > 0 || len(g.importers[name]) > 0
}

// key separates symbols that are defined by several bundles (e.g. _kmod_info) by the
// fileset entry the address belongs to.
func (g *depGraph) key(name string, addr uint64) string {
	if len(g.providers[name]) <= 1 {
		return name
	}
	if idx := g.entryOf(addr); idx >= 0 {
		return name + "\x00" + g.entries[idx].id
	}
	return name
}

func baseName(key string) string {
	if i := strings.IndexByte(key, 0); i >= 0 {
		return key[:i]
	}
	return key
}

// addrOf returns the recovered address of a symbol, as seen from bundle (used for
// symbols that are defined by several bundles).
func (g *depGraph) addrOf(name, bundle string) (uint64, bool) {
	if addr, ok := g.resolved[name]; ok {
		return addr, true
	}
	addr, ok := g.resolved[name+"\x00"+bundle]
	return addr, ok
}

// strongAddrOf is addrOf restricted to symbols that are not only vouched for by BinDiff.
func (g *depGraph) strongAddrOf(name, bundle string) (uint64, bool) {
	addr, ok := g.addrOf(name, bundle)
	if !ok || g.resSrc[g.key(name, addr)] == srcBinDiff {
		return 0, false
	}
	return addr, true
}

func (g *depGraph) vote(name string, addr uint64, weight float64, src uint16) {
	name = g.key(name, addr)
	votes, srcs := g.votes, g.voteSrc
	if g.deriving {
		k := derivedKey{name, addr, src, g.ctxBundle, g.ctxLoc}
		if g.seen[k] {
			return
		}
		g.seen[k] = true
		votes, srcs = g.derived, g.derivedSrc
	} else if g.curFunc != nil {
		g.funcVotes[*g.curFunc] = append(g.funcVotes[*g.curFunc], voteRec{name, addr, weight, src})
	}
	if votes[name] == nil {
		votes[name] = make(map[uint64]float64)
		srcs[name] = make(map[uint64]uint16)
	}
	votes[name][addr] += weight
	srcs[name][addr] |= src
}

// providerAllows checks that addr lies in the fileset entry of a bundle exporting name
// (in the KDK) and that function symbols point into code and data symbols into data.
func (g *depGraph) providerAllows(name string, addr uint64) bool {
	provs := g.providers[name]
	if len(provs) == 0 {
		return true // provider unknown (not in the KDK)
	}
	idx := g.entryOf(addr)
	for _, p := range provs {
		if g.entryIdx[p] == idx {
			return g.images[p].exportIsText[name] == g.kcIsText(addr)
		}
	}
	return false
}

// recover runs all recovery steps:
//
//  1. base votes: BinDiff function matches and matched instructions referencing symbols
//     (imports are resolved through the KDK stubs/GOT, so every importer votes for the
//     address of the symbol in its provider), plus kmod_info
//  2. rejection of BinDiff function matches whose references contradict the consensus
//  3. derived votes until the resolution is stable: layout between recovered neighbors,
//     vtable slots, linear alignment of functions BinDiff missed, data symbols located by
//     their pointers, GOT order, elimination over the inter-fileset pointer graph, and
//     rejection of BinDiff matches that contradict strongly placed functions
func (g *depGraph) recover(quiet bool) error {
	g.voteBinDiffFunctions()

	for _, id := range sortedKeys(g.scope) {
		if err := g.alignInstructions(id); err != nil {
			log.Warnf("Instruction alignment of %s failed: %v", id, err)
		}
	}
	g.voteKmodInfo()
	g.resolve()

	rejected := g.rejectInconsistentFunctions()
	if !quiet {
		log.Infof("Rejected %d inconsistent BinDiff function matches", rejected)
	}
	g.resolve()

	g.derived = make(map[string]map[uint64]float64)
	g.derivedSrc = make(map[string]map[uint64]uint16)
	g.seen = make(map[derivedKey]bool)
	for iter := 0; iter < 10; iter++ {
		prev := g.resolved
		g.deriving = true
		g.alignLayout()
		g.resolve()
		g.alignVtables()
		g.resolve()
		g.alignLinear()
		g.alignPointers()
		g.alignGotOrder()
		g.resolve()
		g.eliminate()
		g.deriving = false
		g.resolve()
		if g.rejectMisplacedFunctions() > 0 {
			g.resolve()
		}
		if sameResolution(prev, g.resolved) {
			break
		}
	}

	return nil
}

// voteBinDiffFunctions adds the BinDiff function matches of exported functions (all bundles).
func (g *depGraph) voteBinDiffFunctions() {
	for _, id := range sortedKeys(imageIDs(g.images)) {
		img := g.images[id]
		bd, ok := g.binDiffs[id]
		if !ok {
			continue
		}
		functions, err := readBinDiffFunctions(bd)
		if err != nil {
			log.Warnf("%v", err)
			continue
		}
		g.covered[id] = make(map[uint64]bool)
		for _, fn := range functions {
			fk := funcKey{id, uint64(fn.Address1)}
			g.covered[id][fk.addr] = true
			g.funcPair[fk] = uint64(fn.Address2)
			g.curFunc = &fk
			for _, name := range img.symsByAddr[fk.addr] {
				if _, exported := img.exports[name]; exported {
					g.vote(name, uint64(fn.Address2), math.Max(fn.Similarity, 0.1), srcBinDiff)
				}
			}
		}
		g.curFunc = nil
	}
}

// alignInstructions walks the BinDiff instruction matches of a bundle. Every matched pair
// of instructions that reference memory (calls, ADRP pairs) yields a vote: the KDK side
// tells which symbol is referenced, the kernelcache side tells its address.
func (g *depGraph) alignInstructions(id string) error {
	img := g.images[id]
	entry := g.entries[g.entryIdx[id]]
	if err := img.loadRefs(); err != nil {
		return err
	}
	if err := g.loadEntryRefs(entry); err != nil {
		return err
	}
	bd, ok := g.binDiffs[id]
	if !ok {
		return nil
	}
	insns, err := readBinDiffInstructions(bd)
	if err != nil {
		return err
	}
	for _, p := range insns {
		fk := funcKey{id, uint64(p.Function1)}
		g.curFunc = &fk
		g.voteRefPair(id, uint64(p.Address1), uint64(p.Address2), math.Max(p.Similarity, 0.1), srcInsn)
	}
	g.curFunc = nil
	return nil
}

// voteRefPair votes for the symbol referenced by the KDK instruction at kdkAddr, located at
// the address referenced by the matching kernelcache instruction at kcAddr.
func (g *depGraph) voteRefPair(id string, kdkAddr, kcAddr uint64, weight float64, src uint16) bool {
	g.ctxBundle, g.ctxLoc = id, kdkAddr
	img := g.images[id]
	entry := g.entries[g.entryIdx[id]]
	kr, ok := img.refs[kdkAddr]
	if !ok {
		return false
	}
	cr, ok := entry.refs[kcAddr]
	if !ok || kr.isFlow() != cr.isFlow() {
		return false
	}
	name, addend, internal, viaSlot := img.resolveRef(kr)
	target := cr.target
	if viaSlot && cr.kind == refLoad && cr.ptr {
		ptr, ok := g.kcPtrs[target]
		if !ok {
			return false
		}
		target = ptr.target
	}
	if name != "" {
		if g.entryOf(target) == g.entryIdx[id] {
			return false
		}
		g.vote(name, uint64(int64(target)-addend), weight, src)
		return true
	}
	start, names, ok := img.containingSymbol(internal)
	if !ok {
		return false
	}
	delta := internal - start
	if delta != 0 && img.sparse {
		// The reference may belong to an unnamed object after the symbol.
		return false
	}
	for _, n := range names {
		if g.interesting(n) {
			g.vote(n, target-delta, weight, src)
		}
	}
	return true
}

// rejectInconsistentFunctions removes the votes of BinDiff function matches whose
// references contradict the consensus of all other votes (e.g. swapped look-alike functions).
func (g *depGraph) rejectInconsistentFunctions() int {
	rejected := 0
	for fk, recs := range g.funcVotes {
		consistent, inconsistent := 0, 0
		for _, r := range recs {
			if r.src != srcInsn {
				continue
			}
			addr, ok := g.resolved[r.key]
			switch {
			case ok && addr == r.addr:
				consistent++
			case ok, !g.providerAllows(baseName(r.key), r.addr):
				inconsistent++
			}
		}
		if inconsistent == 0 || inconsistent < consistent {
			continue
		}
		rejected++
		g.rejectFunction(fk)
	}
	return rejected
}

// rejectFunction removes all base votes of a BinDiff function match.
func (g *depGraph) rejectFunction(fk funcKey) {
	if g.rejected[fk] {
		return
	}
	g.rejected[fk] = true
	delete(g.covered[fk.bundle], fk.addr)
	for _, r := range g.funcVotes[fk] {
		if box := g.votes[r.key]; box != nil {
			box[r.addr] -= r.weight
			if box[r.addr] <= 1e-9 {
				delete(box, r.addr)
				delete(g.voteSrc[r.key], r.addr)
			}
		}
	}
}

// rejectMisplacedFunctions removes the votes of BinDiff function matches that pair a KDK
// function with a kernelcache address other than the one the function was placed at with
// more evidence than BinDiff alone (e.g. look-alike functions of different classes).
func (g *depGraph) rejectMisplacedFunctions() int {
	rejected := 0
	for fk, addr2 := range g.funcPair {
		if g.rejected[fk] {
			continue
		}
		img := g.images[fk.bundle]
		for _, n := range img.symsByAddr[fk.addr] {
			if addr, ok := g.strongAddrOf(n, fk.bundle); ok && addr != addr2 {
				g.rejectFunction(fk)
				rejected++
				break
			}
		}
	}
	return rejected
}

// voteKmodInfo locates the kmod_info_t of the KDK images by its name field.
func (g *depGraph) voteKmodInfo() {
	for _, id := range sortedKeys(g.scope) {
		if _, ok := g.images[id].exports["_kmod_info"]; !ok {
			continue
		}
		e := g.entries[g.entryIdx[id]]
		needle := append([]byte(id), 0)
		for _, sec := range e.sections {
			if !strings.HasPrefix(sec.Seg, "__DATA") || sec.Size == 0 || sec.Flags.IsZerofill() {
				continue
			}
			data := make([]byte, sec.Size)
			if _, err := g.kc.ReadAtAddr(data, sec.Addr); err != nil {
				continue
			}
			for off := 0; ; {
				i := bytes.Index(data[off:], needle)
				if i < 0 {
					break
				}
				pos := off + i
				off = pos + 1
				if pos < 16 || binary.LittleEndian.Uint32(data[pos-8:]) != 1 { // info_version == KMOD_INFO_VERSION
					continue
				}
				g.vote("_kmod_info", sec.Addr+uint64(pos-16), 5, srcKmod)
			}
		}
	}
}

// resolve picks the best address for every voted symbol and resolves address conflicts.
func (g *depGraph) resolve() {
	type pick struct {
		name  string
		addr  uint64
		score float64
	}
	byAddr := make(map[uint64][]pick)
	consider := func(name string, scores map[uint64]float64) {
		var best, second float64
		var bestAddr uint64
		for addr, score := range scores {
			if !g.providerAllows(baseName(name), addr) {
				continue
			}
			if score > best || (score == best && addr < bestAddr) {
				second = best
				best, bestAddr = score, addr
			} else if score > second {
				second = score
			}
		}
		if best == 0 || best < 1.5*second {
			return // no or ambiguous evidence
		}
		byAddr[bestAddr] = append(byAddr[bestAddr], pick{name, bestAddr, best})
	}
	for name, box := range g.votes {
		if extra := g.derived[name]; len(extra) > 0 {
			merged := make(map[uint64]float64, len(box)+len(extra))
			for addr, score := range box {
				merged[addr] = score
			}
			for addr, score := range extra {
				merged[addr] += score
			}
			consider(name, merged)
		} else {
			consider(name, box)
		}
	}
	for name, box := range g.derived {
		if _, ok := g.votes[name]; !ok {
			consider(name, box)
		}
	}

	g.resolved = make(map[string]uint64)
	g.resSrc = make(map[string]uint16)
	for addr, picks := range byAddr {
		sort.Slice(picks, func(i, j int) bool {
			if picks[i].score != picks[j].score {
				return picks[i].score > picks[j].score
			}
			return picks[i].name < picks[j].name
		})
		for _, p := range picks {
			if p.name != picks[0].name && !g.aliases(baseName(p.name), baseName(picks[0].name)) {
				continue
			}
			g.resolved[p.name] = addr
			g.resSrc[p.name] = g.voteSrc[p.name][addr] | g.derivedSrc[p.name][addr]
		}
	}
}

func sameResolution(a, b map[string]uint64) bool {
	if len(a) != len(b) {
		return false
	}
	for k, v := range a {
		if w, ok := b[k]; !ok || w != v {
			return false
		}
	}
	return true
}

// aliases reports whether two symbols share their address in a providing KDK image.
func (g *depGraph) aliases(a, b string) bool {
	for _, p := range g.providers[a] {
		img := g.images[p]
		addrA := img.exports[a]
		if addrB, ok := img.exports[b]; ok && addrA == addrB {
			return true
		}
	}
	return false
}

// alignVtables aligns the slots of every vtable whose address has been recovered. A slot
// matches if the PAC diversity of the KDK pointer equals the one in the kernelcache.
func (g *depGraph) alignVtables() {
	type pending struct {
		name string
		addr uint64
		loc  uint64
	}
	for _, id := range sortedKeys(g.scope) {
		img := g.images[id]
		for start, names := range img.symsByAddr {
			var kcStart uint64
			found := false
			for _, n := range names {
				if strings.HasPrefix(n, "__ZTV") {
					if addr, ok := g.addrOf(n, id); ok {
						kcStart, found = addr, true
						break
					}
				}
			}
			if !found {
				continue
			}
			end := img.symbolEnd(start)
			var votes []pending
			match, mismatch := 0, 0
			for loc := start; loc+8 <= end; loc += 8 {
				kf, ok := img.fixups[loc]
				if !ok {
					continue
				}
				kp, ok := g.kcPtrs[kcStart+(loc-start)]
				if !ok {
					mismatch++
					continue
				}
				if kf.auth && kp.auth {
					if kf.diversity != kp.diversity {
						mismatch++
						continue
					}
					match++
				}
				if kf.bind {
					if !strings.Contains(kf.name, "_RESERVED") { // padding slots are patched in the kernelcache
						votes = append(votes, pending{kf.name, uint64(int64(kp.target) - kf.addend), loc})
					}
				} else {
					for _, n := range img.symsByAddr[kf.target] {
						if g.interesting(n) {
							votes = append(votes, pending{n, kp.target, loc})
						}
					}
				}
			}
			if match == 0 || mismatch*10 > match+mismatch {
				continue
			}
			for _, v := range votes {
				g.ctxBundle, g.ctxLoc = id, v.loc
				g.vote(v.name, v.addr, 2, srcVtable)
			}
		}
	}
}

// eliminate resolves the remaining imports with the inter-fileset pointer graph: an import X
// of kext A provided by kext D must be one of the pointers from A into D that are not yet
// explained by another import. All importers of X must agree.
func (g *depGraph) eliminate() {
	for iter := 0; iter < 10; iter++ {
		explained := make(map[string]map[uint64]bool)
		for _, id := range sortedKeys(g.scope) {
			explained[id] = make(map[uint64]bool)
			for name, binds := range g.images[id].imports {
				if addr, ok := g.resolved[name]; ok {
					for _, b := range binds {
						explained[id][uint64(int64(addr)+b.addend)] = true
					}
				}
			}
		}

		changed := false
		for name, importers := range g.importers {
			if _, ok := g.resolved[name]; ok {
				continue
			}
			provs := g.providers[name]
			if len(provs) != 1 {
				continue
			}
			counts := make(map[uint64]int)
			for _, imp := range importers {
				binds := g.images[imp].imports[name]
				seen := make(map[uint64]bool)
				for _, p := range provs {
					targets := g.outPtrs[imp][g.entryIdx[p]]
					for target, divs := range targets {
						if explained[imp][target] {
							continue
						}
						for _, b := range binds {
							addr := uint64(int64(target) - b.addend)
							if seen[addr] || !g.providerAllows(name, addr) || !divMatch(b, divs) {
								continue
							}
							seen[addr] = true
							counts[addr]++
						}
					}
				}
			}
			var best, second int
			var bestAddr uint64
			for addr, c := range counts {
				if c > best || (c == best && addr < bestAddr) {
					second = best
					best, bestAddr = c, addr
				} else if c > second {
					second = c
				}
			}
			if best == 0 || best == second || 2*best < len(importers) {
				continue
			}
			g.ctxBundle, g.ctxLoc = "", 0
			g.vote(name, bestAddr, 1, srcGraph)
			g.resolved[name] = bestAddr
			g.resSrc[name] = srcGraph
			changed = true
		}
		if !changed {
			break
		}
	}
}

func divMatch(b kdkFixup, divs []uint64) bool {
	if !b.auth {
		return true
	}
	for _, d := range divs {
		if d == b.diversity {
			return true
		}
	}
	return false
}

// extraNames returns the names resolved to an address besides the one symbolMap
// picked (e.g. a function imported under different names by different KEXTs).
func (g *depGraph) extraNames(smap SymbolMap) SymbolAliases {
	extra := make(SymbolAliases)
	for key, addr := range g.resolved {
		name := baseName(key)
		if smap[addr] == name || slices.Contains(extra[addr], name) {
			continue
		}
		extra[addr] = append(extra[addr], name)
	}
	for addr := range extra {
		sort.Strings(extra[addr])
	}
	return extra
}

// symbolMap converts the recovered symbols into an address -> name map. Of several
// names at one address, an imported one wins, then the lexicographically first.
func (g *depGraph) symbolMap() SymbolMap {
	smap := NewSymbolMap()
	rank := func(name string) int {
		if len(g.importers[name]) > 0 {
			return 1
		}
		return 0
	}
	for key, addr := range g.resolved {
		name := baseName(key)
		if prev, ok := smap[addr]; ok {
			if rank(prev) > rank(name) || (rank(prev) == rank(name) && prev < name) {
				continue
			}
		}
		smap[addr] = name
	}
	return smap
}

// alignLinear aligns recovered functions without a trusted BinDiff match instruction by
// instruction (e.g. tiny thunks BinDiff ignores). The instructions must be identical except
// for the operands of references, which then vote like matched instructions.
func (g *depGraph) alignLinear() {
	for _, id := range sortedKeys(g.scope) {
		img := g.images[id]
		if img.refs == nil {
			continue
		}
		entry := g.entries[g.entryIdx[id]]
		if entry.refs == nil {
			continue
		}
		for _, start := range img.symAddrs {
			if g.covered[id][start] {
				continue
			}
			sec := img.m.FindSectionForVMAddr(start)
			if sec == nil || sec.Seg != "__TEXT_EXEC" || strings.Contains(sec.Name, "stubs") {
				continue
			}
			var kcStart uint64
			found := false
			for _, n := range img.symsByAddr[start] {
				if addr, ok := g.addrOf(n, id); ok {
					kcStart, found = addr, true
					break
				}
			}
			if !found || g.entryOf(kcStart) != g.entryIdx[id] {
				continue
			}
			size := min(img.symbolEnd(start)-start, 0x4000)
			kdata := make([]byte, size)
			cdata := make([]byte, size)
			if _, err := img.m.ReadAtAddr(kdata, start); err != nil {
				continue
			}
			if _, err := g.kc.ReadAtAddr(cdata, kcStart); err != nil {
				continue
			}
			for off := uint64(0); off+4 <= size; off += 4 {
				_, kref := img.refs[start+off]
				_, cref := entry.refs[kcStart+off]
				if kref || cref {
					if !g.voteRefPair(id, start+off, kcStart+off, 1, srcLinear) {
						break
					}
					continue
				}
				kw := binary.LittleEndian.Uint32(kdata[off:])
				cw := binary.LittleEndian.Uint32(cdata[off:])
				if kw == cw || (kw&0x9F000000 == 0x90000000 && kw&0x9F00001F == cw&0x9F00001F) { // equal or ADRP to the same register
					continue
				}
				break
			}
		}
	}
}

// expectedPointer returns the kernelcache value of the KDK pointer at loc, if its target
// has been recovered with more evidence than BinDiff alone.
func (g *depGraph) expectedPointer(img *kdkImage, id string, loc uint64) (uint64, bool) {
	f, ok := img.fixups[loc]
	if !ok {
		return 0, false
	}
	if f.bind {
		if strings.Contains(f.name, "_RESERVED") {
			return 0, false
		}
		for _, p := range g.providers[f.name] {
			if addr, ok := g.strongAddrOf(f.name, p); ok {
				return uint64(int64(addr) + f.addend), true
			}
		}
		return 0, false
	}
	start, names, ok := img.containingSymbol(f.target)
	if !ok {
		return 0, false
	}
	for _, n := range names {
		if addr, ok := g.strongAddrOf(n, id); ok {
			return addr + (f.target - start), true
		}
	}
	return 0, false
}

// alignPointers locates data symbols (vtables, metaClass/superClass pointers, ...) by the
// pointers they contain: the expected kernelcache values of their KDK fixups are looked up
// in the kernelcache pointers of the same fileset entry.
func (g *depGraph) alignPointers() {
	type known = struct {
		off   int64
		value uint64
	}
	for _, id := range sortedKeys(g.scope) {
		img := g.images[id]
		self := g.entryIdx[id]
		for _, start := range img.symAddrs {
			todo := false
			for _, n := range img.symsByAddr[start] {
				if g.interesting(n) {
					if _, ok := g.addrOf(n, id); !ok {
						todo = true
					}
				}
			}
			if !todo {
				continue
			}
			sec := img.m.FindSectionForVMAddr(start)
			if sec == nil || !strings.HasPrefix(sec.Seg, "__DATA") || isGotSection(sec) {
				continue
			}
			end := min(img.symbolEnd(start), start+0x10000)
			var inside []known
			for loc := start; loc+8 <= end && len(inside) < 16; loc += 8 {
				if v, ok := g.expectedPointer(img, id, loc); ok {
					inside = append(inside, known{int64(loc - start), v})
				}
			}
			if len(inside) == 0 {
				continue
			}
			// candidates must match (almost) all pointers inside the symbol
			var cands []uint64
			seen := make(map[uint64]bool)
			for _, seed := range inside[:min(2, len(inside))] {
				for _, loc := range g.ptrIndex[seed.value] {
					c := uint64(int64(loc) - seed.off)
					if seen[c] || g.entryOf(c) != self {
						continue
					}
					seen[c] = true
					if 5*g.pointerHits(c, inside) >= 4*len(inside) {
						cands = append(cands, c)
					}
				}
			}
			if len(cands) > 1 { // disambiguate with the neighboring pointers
				var around []known
				for _, loc := range []uint64{start - 16, start - 8, end, end + 8} {
					if v, ok := g.expectedPointer(img, id, loc); ok {
						around = append(around, known{int64(loc) - int64(start), v})
					}
				}
				best, bestHits, tie := uint64(0), 0, false
				for _, c := range cands {
					hits := g.pointerHits(c, around)
					if hits > bestHits {
						best, bestHits, tie = c, hits, false
					} else if hits == bestHits {
						tie = true
					}
				}
				if bestHits > 0 && !tie {
					cands = []uint64{best}
				}
			}
			if len(cands) != 1 {
				continue
			}
			g.ctxBundle, g.ctxLoc = id, start
			for _, n := range img.symsByAddr[start] {
				if g.interesting(n) {
					g.vote(n, cands[0], 1, srcPtr)
				}
			}
		}
	}
}

func (g *depGraph) pointerHits(c uint64, ks []struct {
	off   int64
	value uint64
}) int {
	hits := 0
	for _, k := range ks {
		if p, ok := g.kcPtrs[uint64(int64(c)+k.off)]; ok && p.target == k.value {
			hits++
		}
	}
	return hits
}

// alignGotOrder pairs the GOT slots of a KDK image and its fileset entry in order. Slots of
// recovered imports with a unique counterpart are anchors; between two anchors the slots are
// paired if both sides have the same number of slots. Only the relative order is used, so
// imports added or removed elsewhere do not matter.
func (g *depGraph) alignGotOrder() {
	type anchor struct{ i, j int }
	for _, id := range sortedKeys(g.scope) {
		img := g.images[id]
		entry := g.entries[g.entryIdx[id]]
		for _, ksec := range img.m.Sections {
			if !isGotSection(ksec) {
				continue
			}
			var csec *types.Section
			for _, sec := range entry.sections {
				if sec.Seg == ksec.Seg && sec.Name == ksec.Name {
					csec = sec
				}
			}
			if csec == nil {
				continue
			}
			nk, nc := int(ksec.Size/8), int(csec.Size/8)
			kvals := make([]uint64, nk)
			kknown := make([]bool, nk)
			kcount := make(map[uint64]int)
			for i := range kvals {
				if kvals[i], kknown[i] = g.expectedPointer(img, id, ksec.Addr+uint64(i)*8); kknown[i] {
					kcount[kvals[i]]++
				}
			}
			cptrs := make([]kcPtr, nc)
			cpos := make(map[uint64][]int)
			for j := range cptrs {
				if p, ok := g.kcPtrs[csec.Addr+uint64(j)*8]; ok {
					cptrs[j] = p
					cpos[p.target] = append(cpos[p.target], j)
				}
			}
			var anchors []anchor
			for i := range kvals {
				if kknown[i] && kcount[kvals[i]] == 1 && len(cpos[kvals[i]]) == 1 {
					anchors = append(anchors, anchor{i, cpos[kvals[i]][0]})
				}
			}
			// keep the longest chain of anchors that is increasing on both sides
			js := make([]int, len(anchors))
			for k, a := range anchors {
				js[k] = a.j
			}
			chain := []anchor{{-1, -1}}
			for _, k := range longestIncreasing(js) {
				chain = append(chain, anchors[k])
			}
			chain = append(chain, anchor{nk, nc})

			for a := 0; a+1 < len(chain); a++ {
				lo, hi := chain[a], chain[a+1]
				if hi.i-lo.i != hi.j-lo.j {
					continue
				}
				for k := 1; k < hi.i-lo.i; k++ {
					i, j := lo.i+k, lo.j+k
					f, ok := img.fixups[ksec.Addr+uint64(i)*8]
					if !ok || !f.bind || kknown[i] || cptrs[j].target == 0 {
						continue
					}
					addr := uint64(int64(cptrs[j].target) - f.addend)
					if g.providerAllows(f.name, addr) && divMatch(f, []uint64{cptrs[j].diversity}) {
						g.ctxBundle, g.ctxLoc = id, ksec.Addr+uint64(i)*8
						g.vote(f.name, addr, 1, srcOrder)
					}
				}
			}
		}
	}
}

// longestIncreasing returns the indices of a longest strictly increasing subsequence.
func longestIncreasing(vals []int) []int {
	tails := []int{} // indices into vals
	prev := make([]int, len(vals))
	for i, v := range vals {
		k := sort.Search(len(tails), func(k int) bool { return vals[tails[k]] >= v })
		if k > 0 {
			prev[i] = tails[k-1]
		} else {
			prev[i] = -1
		}
		if k == len(tails) {
			tails = append(tails, i)
		} else {
			tails[k] = i
		}
	}
	out := make([]int, len(tails))
	for k, i := len(tails)-1, -1; k >= 0; k-- {
		if k == len(tails)-1 {
			i = tails[k]
		}
		out[k] = i
		i = prev[i]
	}
	return out
}

// codeMatches compares the KDK function at kdkAddr with the kernelcache code at kcAddr: all
// instructions must be identical except for the operands of references (calls, ADRP pairs).
func (g *depGraph) codeMatches(img *kdkImage, id string, kdkAddr, kcAddr uint64) bool {
	entry := g.entries[g.entryIdx[id]]
	size := min(img.symbolEnd(kdkAddr)-kdkAddr, 0x4000)
	if size < 4 {
		return false
	}
	kdata := make([]byte, size)
	cdata := make([]byte, size)
	if _, err := img.m.ReadAtAddr(kdata, kdkAddr); err != nil {
		return false
	}
	if _, err := g.kc.ReadAtAddr(cdata, kcAddr); err != nil {
		return false
	}
	for off := uint64(0); off+4 <= size; off += 4 {
		kr, kref := img.refs[kdkAddr+off]
		cr, cref := entry.refs[kcAddr+off]
		if kref || cref {
			if kref != cref || kr.isFlow() != cr.isFlow() {
				return false
			}
			continue
		}
		kw := binary.LittleEndian.Uint32(kdata[off:])
		cw := binary.LittleEndian.Uint32(cdata[off:])
		if kw != cw && !(kw&0x9F000000 == 0x90000000 && kw&0x9F00001F == cw&0x9F00001F) {
			return false
		}
	}
	return true
}

// dataMatches compares the KDK data symbol at kdkAddr with the kernelcache data at kcAddr.
// Bytes must be equal, pointers must point to the expected (recovered) targets.
func (g *depGraph) dataMatches(img *kdkImage, id string, kdkAddr, kcAddr uint64, sec *types.Section) bool {
	ksec := g.kcSection(kcAddr)
	if ksec == nil || ksec.Seg != sec.Seg {
		return false
	}
	if sec.Flags.IsZerofill() || ksec.Flags.IsZerofill() {
		return sec.Flags.IsZerofill() == ksec.Flags.IsZerofill()
	}
	size := min(img.symbolEnd(kdkAddr)-kdkAddr, 0x1000)
	kdata := make([]byte, size)
	cdata := make([]byte, size)
	if _, err := img.m.ReadAtAddr(kdata, kdkAddr); err != nil {
		return false
	}
	if _, err := g.kc.ReadAtAddr(cdata, kcAddr); err != nil {
		return false
	}
	for off := uint64(0); off < size; {
		if _, ok := img.fixups[kdkAddr+off]; ok {
			p, ok := g.kcPtrs[kcAddr+off]
			if !ok {
				return false
			}
			if want, known := g.expectedPointer(img, id, kdkAddr+off); known && want != p.target {
				return false
			}
			off += 8
			continue
		}
		if kdata[off] != cdata[off] {
			return false
		}
		off++
	}
	return true
}

// alignLayout uses the relative layout between recovered neighbors: if the distance between
// the recovered symbols around a symbol is the same in the KDK and in the kernelcache, the
// symbol keeps its relative offset. The candidate must match (code: identical instructions
// except for reference operands; data: identical bytes and pointer targets). This finds
// look-alike functions BinDiff confuses or ignores and data nothing refers to.
func (g *depGraph) alignLayout() {
	type anchor struct{ kdk, kc uint64 }
	for _, id := range sortedKeys(g.scope) {
		img := g.images[id]
		entry := g.entries[g.entryIdx[id]]
		if img.refs == nil || entry.refs == nil {
			continue
		}
		self := g.entryIdx[id]
		// all anchors, and strong anchors (not only vouched for by BinDiff)
		var all, strong []anchor
		for _, sec := range img.m.Sections {
			for _, ks := range entry.sections {
				if ks.Seg == sec.Seg && ks.Name == sec.Name {
					all = append(all, anchor{sec.Addr, ks.Addr}, anchor{sec.Addr + sec.Size, ks.Addr + ks.Size})
					strong = append(strong, anchor{sec.Addr, ks.Addr}, anchor{sec.Addr + sec.Size, ks.Addr + ks.Size})
				}
			}
		}
		for _, a := range img.symAddrs {
			for _, n := range img.symsByAddr[a] {
				kc, ok := g.addrOf(n, id)
				if !ok || g.entryOf(kc) != self {
					continue
				}
				all = append(all, anchor{a, kc})
				if g.resSrc[g.key(n, kc)] != srcBinDiff {
					strong = append(strong, anchor{a, kc})
				}
				break
			}
		}
		for _, anchors := range [][]anchor{all, strong} {
			sort.Slice(anchors, func(i, j int) bool { return anchors[i].kdk < anchors[j].kdk })
		}
		// interpolate returns the kernelcache address of f between its neighboring anchors
		interpolate := func(anchors []anchor, f uint64, sec *types.Section) (uint64, bool) {
			i := sort.Search(len(anchors), func(i int) bool { return anchors[i].kdk >= f })
			if i < len(anchors) && anchors[i].kdk == f && f == sec.Addr { // section start
				return anchors[i].kc, true
			}
			j := i
			for j < len(anchors) && anchors[j].kdk == f {
				j++ // the symbol itself is no anchor
			}
			if i == 0 || j == len(anchors) {
				return 0, false
			}
			lo, hi := anchors[i-1], anchors[j]
			if lo.kdk < sec.Addr || hi.kdk > sec.Addr+sec.Size || hi.kc < lo.kc || hi.kdk-lo.kdk != hi.kc-lo.kc {
				return 0, false
			}
			return lo.kc + (f - lo.kdk), true
		}

		for _, f := range img.symAddrs {
			interesting := false
			for _, n := range img.symsByAddr[f] {
				interesting = interesting || g.interesting(n)
			}
			sec := img.m.FindSectionForVMAddr(f)
			if !interesting || sec == nil || strings.Contains(sec.Name, "stubs") || isGotSection(sec) {
				continue
			}
			for _, anchors := range [][]anchor{all, strong} {
				if cand, ok := interpolate(anchors, f, sec); ok && g.layoutVote(img, id, f, cand, sec) {
					break
				}
			}
		}
	}
}

func (g *depGraph) layoutVote(img *kdkImage, id string, f, cand uint64, sec *types.Section) bool {
	if g.entryOf(cand) != g.entryIdx[id] {
		return false
	}
	weight := 3.0
	if sec.Seg == "__TEXT_EXEC" {
		if !g.codeMatches(img, id, f, cand) {
			return false
		}
	} else {
		if !g.dataMatches(img, id, f, cand, sec) {
			return false
		}
		if sec.Flags.IsZerofill() {
			weight = 1 // nothing to verify
		}
	}
	g.ctxBundle, g.ctxLoc = id, f
	for _, n := range img.symsByAddr[f] {
		if g.interesting(n) {
			g.vote(n, cand, weight, srcLayout)
		}
	}
	return true
}

func imageIDs(images map[string]*kdkImage) map[string]bool {
	ids := make(map[string]bool, len(images))
	for id := range images {
		ids[id] = true
	}
	return ids
}

func sortedKeys(m map[string]bool) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

// openFilesetEntry opens a fileset entry. GetFileSetFileByName returns the first entry
// whose ID ends with the given one, so the wanted entry is moved to the front first.
func openFilesetEntry(kc *macho.File, entry *macho.FilesetEntry) (*macho.File, error) {
	first, selected := -1, -1
	for i, load := range kc.Loads {
		if _, ok := load.(*macho.FilesetEntry); ok && first == -1 {
			first = i
		}
		if load == entry {
			selected = i
		}
	}
	if selected == -1 {
		return nil, fmt.Errorf("fileset entry %s not found", entry.EntryID)
	}
	kc.Loads[first], kc.Loads[selected] = kc.Loads[selected], kc.Loads[first]
	defer func() { kc.Loads[first], kc.Loads[selected] = kc.Loads[selected], kc.Loads[first] }()
	return kc.GetFileSetFileByName(entry.EntryID)
}

func pathIDs(paths map[string]string) map[string]bool {
	ids := make(map[string]bool, len(paths))
	for id := range paths {
		ids[id] = true
	}
	return ids
}
