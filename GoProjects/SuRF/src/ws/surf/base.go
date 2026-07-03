package surf

import (
	"bufio"
	"fmt"
	"log"
	"os"
	"runtime/pprof"
	"testing"
	"time"
)

func assertTrue(t *testing.T, value bool) {
	if !value {
		if t != nil {
			t.Helper()
			t.Error("False")
		} else {
			log.Println("False")
		}
	}
}

func assertEqualsUint8(t *testing.T, v1 uint8, v2 uint8) {
	if v1 != v2 {
		if t != nil {
			t.Helper()
			t.Error(v1, "!=", v2)
		} else {
			log.Println(v1, "!=", v2)
		}
	}
}

func assertEquals(t *testing.T, v1 uint64, v2 uint64) {
	if v1 != v2 {
		if t != nil {
			t.Helper()
			t.Error(v1, "!=", v2)
		} else {
			log.Println(v1, "!=", v2)
		}
	}
}

func assertBoolEquals(t *testing.T, v1 bool, v2 bool) {
	if v1 != v2 {
		if t != nil {
			t.Helper()
			t.Error(v1, "!=", v2)
		} else {
			log.Println(v1, "!=", v2)
		}
	}
}

const const1OfUInt64 uint64 = 1 << 63

// pos在[0,255]的范围内,不过,好像这是傻话,uint8本来就是这个范围
func uint256Mark1(node []uint64, pos uint8) {
	bean := _QuickLookupTable[pos]
	node[bean.indexOfArray] |= (const1OfUInt64 >> (bean.indexOfPos))
}

func uint256IsMarked(node []uint64, pos uint8) bool {
	bean := _QuickLookupTable[pos]
	return (node[bean.indexOfArray] & (const1OfUInt64 >> (bean.indexOfPos))) != 0
}

func uint256IndexOfNode(node []uint64, pos uint8) uint8 {
	bean := _QuickLookupTable[pos]
	res := uint8(0)
	for i, inode := range node {
		if uint8(i) < bean.indexOfArray {
			res += _Popcount64(inode)
		} else {
			res += _Popcount64(inode >> (64 - bean.indexOfPos))
			break
		}
	}

	return res
}

func uint256PosOf1(node []uint64, indexOf1 uint8) (bool, uint8) {
	countOf1Found := uint8(0)
	for pos := uint8(0); pos <= 0xFF; pos++ {
		if uint256IsMarked(node, pos) {
			if countOf1Found == indexOf1 {
				return true, pos
			}
			countOf1Found++
		}
		if pos == 0xFF {
			break
		}
	}

	return false, 0
}

// Uint256OnePositions Uint256OnePositions
func Uint256OnePositions(node []uint64) []uint8 {
	res := make([]uint8, 0)
	for i, number := range node {
		checkPos := uint8(0)
		for number != 0 {
			if number&const1OfUInt64 != 0 {
				res = append(res, checkPos+uint8(i<<6))
			}

			number <<= 1
			checkPos++
		}
	}

	return res
}

var pc = func() (pc [256]byte) {
	for i := range pc {
		pc[i] = pc[i/2] + byte(i&1)
	}
	return
}()

func _Popcount64M1(x uint64) uint8 {
	return uint8(pc[byte(x>>0)] +
		pc[byte(x>>8)] +
		pc[byte(x>>16)] +
		pc[byte(x>>24)] +
		pc[byte(x>>32)] +
		pc[byte(x>>40)] +
		pc[byte(x>>48)] +
		pc[byte(x>>56)])
}

var _L8 uint64 = 0x0101010101010101 // Every lowest 8th bit set: 00000001...
var _G2 uint64 = 0xAAAAAAAAAAAAAAAA // Every highest 2nd bit: 101010...
var _G4 uint64 = 0x3333333333333333 // 00110011 ... used to group the sum of 4 bits.
var _G8 uint64 = 0x0F0F0F0F0F0F0F0F

func _Popcount64(x uint64) uint8 {
	// Step 1:  00 - 00 = 0;  01 - 00 = 01; 10 - 01 = 01; 11 - 01 = 10;
	x = x - ((x & _G2) >> 1)
	// step 2:  add 2 groups of 2.
	x = (x & _G4) + ((x >> 2) & _G4)
	// 2 groups of 4.
	x = (x + (x >> 4)) & _G8
	// Using a multiply to collect the 8 groups of 8 together.
	x = x * _L8 >> 56
	return uint8(x)
}

func _Popcount64M3(x uint64) uint8 {
	return _Popcount32(uint32(x&0xFFFFFFFF)) + _Popcount32(uint32(x>>32))
}

func _Popcount32(x uint32) uint8 {
	x -= (x >> 1) & 0x55555555
	x = (x & 0x33333333) + ((x >> 2) & 0x33333333)
	x = (x + (x >> 4)) & 0x0F0F0F0F
	x += x >> 8
	return uint8((x + (x >> 16)) & 0x3F)
}

type _PosBean struct {
	indexOfArray uint8
	indexOfPos   uint8
}

func newPos(i1 uint8, i2 uint8) *_PosBean {
	pos := _PosBean{}
	pos.indexOfArray = i1
	pos.indexOfPos = i2

	return &pos
}

var _QuickLookupTable = generateQuickLookupTable()

func generateQuickLookupTable() []*_PosBean {
	array := make([]*_PosBean, 0)
	for i := 0; i <= 0xFF; i++ {
		array = append(array, newPos(uint8(i>>6), uint8(i%64)))
	}

	return array
}

// Value key对应的Value
type Value struct {
	values []uint64
}

func newNodeValue() *Value {
	return &Value{
		values: make([]uint64, 0),
	}
}

func (me *Value) put(v uint64) {
	me.values = append(me.values, v)
}

func (me *Value) assertEquals(t *testing.T, com *Value) {
	if me != com {
		assertEquals(t, uint64(len(me.values)), uint64(len(com.values)))
		if len(me.values) == len(com.values) {
			for i := range me.values {
				assertEquals(t, me.values[i], com.values[i])
			}
		}
	}
}

// IProcesser 遍历文件的处理器
type IProcesser interface {
	nameOfProc() string
	beforeIterate()
	proc(lineNo uint64, bytes string)
}

type _GenerateOBProcesser struct {
	ob map[string]*Value
}

func (me *_GenerateOBProcesser) nameOfProc() string {
	return "build ob"
}
func (me *_GenerateOBProcesser) beforeIterate() {
	me.ob = make(map[string]*Value)
}
func (me *_GenerateOBProcesser) proc(lineNo uint64, bytes string) {
	key := bytes
	if v, ok := me.ob[key]; ok {
		v.put(lineNo)
	} else {
		newV := newNodeValue()
		me.ob[key] = newV
		newV.put(lineNo)
	}
}

type _GenerateListProcesser struct {
	list []string
}

func (me *_GenerateListProcesser) nameOfProc() string {
	return "build list"
}
func (me *_GenerateListProcesser) beforeIterate() {
	me.list = make([]string, 0)
}
func (me *_GenerateListProcesser) proc(lineNo uint64, bytes string) {
	me.list = append(me.list, bytes)
}

// IterateStringList IterateStringList
func IterateStringList(textList []string, proc IProcesser) {
	start := time.Now().UnixNano()
	proc.beforeIterate()

	for li := 0; li < len(textList); li++ {
		proc.proc(uint64(li), textList[li])
	}

	log.Println(proc.nameOfProc(), "time spent:", (time.Now().UnixNano()-start)/1000000)

}

// IterateFilename 遍历文件
func IterateFilename(filename string, maxLines uint64, proc IProcesser) {
	start := time.Now().UnixNano()
	proc.beforeIterate()

	lineNo := uint64(0)
	if f, err := os.Open(filename); err == nil {
		defer f.Close()

		reader := bufio.NewReader(f)
		for lineNo < maxLines {
			if buf, err := reader.ReadBytes('\n'); err == nil {
				proc.proc(lineNo, string(buf[:len(buf)-1]))
				lineNo++
			} else {
				break
			}
		}
	}

	log.Println(proc.nameOfProc(), " time spent:", (time.Now().UnixNano()-start)/1000000)
}

type _SpeedTest4OB struct {
	ob map[string]*Value
}

func (me *_SpeedTest4OB) nameOfProc() string {
	return "ob speed test"
}
func (me *_SpeedTest4OB) beforeIterate() {
}
func (me *_SpeedTest4OB) proc(lineNo uint64, bytes string) {
	if v, ok := me.ob[bytes]; ok {
		DoNothing(v)
	}
}

// DoNothing 就是do nothing
func DoNothing(ob interface{}) {
}

// CreateMemFile CreateMemFile
func CreateMemFile(filename string) {
	time.Sleep(time.Second * 3)
	memf, err := os.Create(filename)
	if err != nil {
		log.Fatal("could not create memory profile: ", err)
	}
	if err := pprof.WriteHeapProfile(memf); err != nil {
		log.Fatal("could not write memory profile: ", err)
	}
	memf.Close()
}

// ReadFileAsOb 用来与LOUDS做对比
func ReadFileAsOb(textList []string) map[string]*Value {
	proc := &_GenerateOBProcesser{}
	IterateStringList(textList, proc)
	return proc.ob
}

// ReadFileAsList 用来与LOUDS内存消耗对比
func ReadFileAsList(filename string, maxLines uint64) []string {
	proc := &_GenerateListProcesser{}
	IterateFilename(filename, maxLines, proc)
	return proc.list
}

// TestSpeedOfOB 测试OB的速度
func TestSpeedOfOB(textList []string, _ob map[string]*Value) {
	proc := &_SpeedTest4OB{
		ob: _ob,
	}
	for i := 0; i < 5; i++ {
		IterateStringList(textList, proc)
	}
}

func hash32(bytes []uint8) uint32 {
	var seed uint32 = 0xbc9f1d34
	var m uint32 = 0xc6a4a793
	bytes = append(bytes, uint8(len(bytes)))
	var h = seed ^ (m * uint32(len(bytes)))

	startIndex := 0
	for startIndex < len(bytes) {
		w := joint(bytes[startIndex:])
		startIndex += 4

		h += w
		h *= m
		h ^= (h >> 16)
	}

	if h == 0 {
		panic(fmt.Sprintln("发生了神秘事件:[", string(bytes), "]的hash32居然是0"))
	}
	return h
}

func joint(fourBytes []uint8) uint32 {
	var h uint32
	if len(fourBytes) > 0 {
		h |= uint32(fourBytes[0])
	}
	if len(fourBytes) > 1 {
		h |= (uint32(fourBytes[1]) << 8)
	}
	if len(fourBytes) > 2 {
		h |= (uint32(fourBytes[2]) << 16)
	}
	if len(fourBytes) > 3 {
		h |= (uint32(fourBytes[3]) << 24)
	}

	return h
}

// SizeOfBytesAsString SizeOfBytesAsString
func SizeOfBytesAsString(size uint64) string {
	var stringUint = "B"
	fSzie := float64(size)
	if fSzie > 1024 {
		fSzie /= 1024
		stringUint = "KB"
	}
	if fSzie > 1024 {
		fSzie /= 1024
		stringUint = "MB"
	}
	if fSzie > 1024 {
		fSzie /= 1024
		stringUint = "GB"
	}

	return fmt.Sprintf("%.2f%s", fSzie, stringUint)
}

func uint64Mark1(bits []uint64, pos uint64) {
	indexOfBits := pos >> 6
	offsetOfBit := (pos & 0x3F)
	bits[indexOfBits] |= (const1OfUInt64 >> (offsetOfBit))
}

func uint64IsMarked(bits []uint64, pos uint64) bool {
	indexOfBits := pos >> 6
	offsetOfBit := pos & 0x3F
	return (bits[indexOfBits] & (const1OfUInt64 >> (offsetOfBit))) != 0
}

func uint64Select1(block uint64, nodNumber uint8) uint8 {
	return uint64Select1PopcountSearch(block, nodNumber)
	// return uint64Select1LinearSearch(block, nodNumber)
}

func uint64Select1LinearSearch(block uint64, nodNumber uint8) uint8 {
	count1 := uint8(0)
	for i := uint8(0); i < 64; i++ {
		if (block & (const1OfUInt64 >> i)) != 0 {
			count1++
			if count1 > nodNumber {
				return uint8(i)
			}
		}
	}

	panic("fuck uint64Select1LinearSearch")
}

func uint64Select1PopcountSearch(block uint64, nodNumber uint8) uint8 {
	loc := -1
	nodNumber++

	for testbits := 32; testbits > 0; testbits >>= 1 {
		lcount := _Popcount64(block >> uint(testbits))
		if nodNumber > lcount {
			block &= ((uint64(1) << uint(testbits)) - 1)
			loc = int(testbits) + loc
			nodNumber -= lcount
		} else {
			block >>= uint(testbits)
		}
	}
	return uint8(loc + int(nodNumber))
}

func select1(bits []uint64, nodNumber uint64) uint64 {
	countOfAll := uint64(0)
	for ib, block := range bits {
		count1OfBlock := uint64(_Popcount64(block))
		countOfAll += count1OfBlock
		if countOfAll > nodNumber {
			return uint64(ib)<<6 + uint64(uint64Select1(bits[ib], uint8(nodNumber-(countOfAll-count1OfBlock))))
		}
	}

	panic("fuck select1")
}

func searchGreaterThan(target uint64, array []uint64) (int, bool) {
	if len(array) < 4 {
		return linearSearchGreaterThan(target, array)
	}
	return binarySearchGreaterThan(target, array)
}

func linearSearchGreaterThan(target uint64, array []uint64) (int, bool) {
	for i := 0; i < len(array); i++ {
		if array[i] > target {
			return i, true
		}
	}

	return 0, false
}

func binarySearchGreaterThan(target uint64, array []uint64) (int, bool) {
	searchLen := len(array)
	l := 0
	r := searchLen

	for l < r {
		m := (l + r) >> 1
		if target < array[m] {
			r = m
		} else if target == array[m] {
			if m < searchLen-1 {
				return m + 1, true
			}
			return 0, false
		} else {
			l = m + 1
		}
	}

	if l < searchLen {
		return l, true
	}
	return 0, false
}
