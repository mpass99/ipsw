package signature

import (
	"encoding/binary"
	"os"
	"path/filepath"
	"testing"

	"github.com/glebarez/sqlite"
	"gorm.io/gorm"
	"gorm.io/gorm/logger"
)

func TestScanCodeRefs(t *testing.T) {
	code := []uint32{
		0xB0000028, // 0x1000 adrp x8, 0x6000
		0xF9400D00, // 0x1004 ldr  x0, [x8, #0x18]
		0xB9400503, // 0x1008 ldr  w3, [x8, #0x4]
		0xB0000033, // 0x100c adrp x19, 0x6000
		0x940003FC, // 0x1010 bl   0x2000 (clobbers x8, keeps x19)
		0x91008101, // 0x1014 add  x1, x8, #0x20
		0x91002262, // 0x1018 add  x2, x19, #0x8
		0xF9000A60, // 0x101c str  x0, [x19, #0x10]
		0x17FFFFF8, // 0x1020 b    0x1000
		0x91000664, // 0x1024 add  x4, x19, #0x1
	}
	data := make([]byte, 4*len(code))
	for i, insn := range code {
		binary.LittleEndian.PutUint32(data[4*i:], insn)
	}
	refs := make(map[uint64]codeRef)
	scanCodeRefs(data, 0x1000, refs)

	want := map[uint64]codeRef{
		0x1004: {kind: refLoad, ptr: true, target: 0x6018},
		0x1008: {kind: refLoad, target: 0x6004},
		0x1010: {kind: refCall, target: 0x2000},
		0x1018: {kind: refAddr, target: 0x6008},
		0x101c: {kind: refStore, target: 0x6010},
		0x1020: {kind: refBranch, target: 0x1000},
	}
	if len(refs) != len(want) {
		t.Errorf("got %d references, want %d: %+v", len(refs), len(want), refs)
	}
	for pc, w := range want {
		if got, ok := refs[pc]; !ok || got != w {
			t.Errorf("reference at %#x = %+v (found %v), want %+v", pc, got, ok, w)
		}
	}
}

func TestLongestIncreasing(t *testing.T) {
	vals := []int{3, 1, 2, 5, 4, 6}
	idx := longestIncreasing(vals)
	if len(idx) != 4 {
		t.Fatalf("got %v, want 4 indices", idx)
	}
	for i := 1; i < len(idx); i++ {
		if idx[i] <= idx[i-1] || vals[idx[i]] <= vals[idx[i-1]] {
			t.Fatalf("indices %v do not form an increasing subsequence of %v", idx, vals)
		}
	}
}

func TestFindBinDiffForMachO(t *testing.T) {
	dir := t.TempDir()
	machO := filepath.Join(dir, "Foo")
	if err := os.WriteFile(machO, []byte{0xcf, 0xfa, 0xed, 0xfe}, 0o644); err != nil {
		t.Fatal(err)
	}
	// BinDiff truncates file names, so only the file table may decide.
	writeBinDiffFiles(t, filepath.Join(dir, "a.BinDiff"), "Foo", "com.apple.other")
	writeBinDiffFiles(t, filepath.Join(dir, "b.BinDiff"), "Foo", "com.apple.foo")

	got, err := findBinDiffForMachO(machO, "com.apple.foo")
	if err != nil {
		t.Fatal(err)
	}
	if filepath.Base(got) != "b.BinDiff" {
		t.Errorf("got %s, want b.BinDiff", got)
	}
	if _, err := findBinDiffForMachO(machO, "com.apple.missing"); err == nil {
		t.Error("expected an error for a bundle without BinDiff database")
	}
}

func writeBinDiffFiles(t *testing.T, path, primary, secondary string) {
	t.Helper()
	db, err := gorm.Open(sqlite.Open(path), &gorm.Config{Logger: logger.Default.LogMode(logger.Silent)})
	if err != nil {
		t.Fatal(err)
	}
	defer closeBinDiffDB(db)
	for _, stmt := range []string{
		"CREATE TABLE file (id INTEGER PRIMARY KEY, filename TEXT, exefilename TEXT, hash TEXT)",
		"INSERT INTO file (id, filename, exefilename, hash) VALUES (1, '" + primary + "', '/kdk/" + primary + "', '')",
		"INSERT INTO file (id, filename, exefilename, hash) VALUES (2, '" + secondary + "', '" + secondary + "', '')",
	} {
		if err := db.Exec(stmt).Error; err != nil {
			t.Fatal(err)
		}
	}
}
