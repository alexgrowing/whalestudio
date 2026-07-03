package surf

import "fmt"

type _BitVector struct {
	bits []uint64
}

func (me *_BitVector) malloc() {
	me.bits = append(me.bits, 0)
}

func (me *_BitVector) isMarked(pos uint64) bool {
	return uint64IsMarked(me.bits, pos)
}

func (me *_BitVector) mark1(pos uint64) {
	uint64Mark1(me.bits, pos)
}

func (me *_BitVector) memorySize() uint64 {
	return uint64(len(me.bits)) << 3
}

// BitVectorRank BitVectorRank
type BitVectorRank struct {
	_BitVector
}

// BitVectorSelect BitVectorSelect
type BitVectorSelect struct {
	_BitVector
	lut4Select []uint64
}

func newBitVectorSelect() *BitVectorSelect {
	return &BitVectorSelect{}
}

func (me *BitVectorSelect) initSelectLUT() {
	me.lut4Select = make([]uint64, 0, len(me._BitVector.bits))
	iBlock := 0
	popcount := uint64(0)
	countOfBlocks := len(me._BitVector.bits)
	for iBlock < countOfBlocks {
		popcount += uint64(_Popcount64(me._BitVector.bits[iBlock]))

		me.lut4Select = append(me.lut4Select, popcount)
		iBlock++
	}
}

func (me *BitVectorSelect) memorySize() uint64 {
	return me._BitVector.memorySize() + (uint64(len(me.lut4Select)) << 3)
}

func (me *BitVectorSelect) select1(nodNumber uint64) uint64 {
	if index, ok := searchGreaterThan(nodNumber, me.lut4Select); ok {
		lastNodNumber := uint64(0)
		if index > 0 {
			lastNodNumber = me.lut4Select[index-1]
		}

		iBlock := uint64(index)
		iPos := iBlock << 6
		offsetPos := uint64Select1(me._BitVector.bits[iBlock], uint8(nodNumber-lastNodNumber))
		return iPos + uint64(offsetPos)
	}

	panic(fmt.Sprint("fuck BitVectorSelect.select1 to find nodNumber:", nodNumber))
}
