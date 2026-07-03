package surf

import (
	"fmt"
	"log"
	"runtime"
	"sort"
	"time"
)

type _SuRFBuilder4Suffix struct {
	labelsTree [][]uint8 // 记录每一个byte
	loudsBits  [][]uint8 // 记录每个byte下面有多少个children

	suffixes [][][]uint8
}

func newSuRFBuilder4Suffix(suffixBytes [][]uint8) *_SuRFBuilder4Suffix {
	builder := &_SuRFBuilder4Suffix{
		labelsTree: make([][]uint8, 0),
		loudsBits:  make([][]uint8, 0),

		suffixes: make([][][]uint8, 0),
	}

	builder.build(suffixBytes)

	return builder
}

func (me *_SuRFBuilder4Suffix) build(suffixBytes [][]uint8) {
	countOfKeys := len(suffixBytes)
	for iKey := 0; iKey < countOfKeys; iKey++ {
		key2Store := suffixBytes[iKey]
		// log.Println("store suffix:[", string(key2Store), "]--", key2Store)

		level := me.skipStoredPrefix(key2Store)

		if iKey+1 == countOfKeys {
			me.storeKeyBytesToTrieUntilUnique(key2Store, []uint8{}, level)
		} else {
			me.storeKeyBytesToTrieUntilUnique(key2Store, suffixBytes[iKey+1], level)
		}

		key2Store = nil
	}

	// me.printMem()
}

func (me *_SuRFBuilder4Suffix) skipStoredPrefix(key []uint8) uint32 {
	level := uint32(0)

	for (level < uint32(len(key))) && me.isStoredPrefixByte(key[level], level) {
		countOfChildrenByLevel := me.loudsBits[level]
		level++
		if countOfChildrenByLevel[len(countOfChildrenByLevel)-1] == 0 {
			/*
				如果有children再往下调查,如果没有children往下调查,可能与前一个node的children匹配
				abaa
				ab
				aaa
			*/
			break
		}
	}

	return level
}

func (me *_SuRFBuilder4Suffix) isStoredPrefixByte(keyByte uint8, level uint32) bool {
	// 因为保存进来的byte是排好序的,所以只需要与每一层最后一个byte比较就可以了
	if level < me.getTreeHeight() {
		treeFlat := me.labelsTree[level]
		return keyByte == treeFlat[len(treeFlat)-1]
	}

	return false
}

func (me *_SuRFBuilder4Suffix) storeKeyBytesToTrieUntilUnique(currentKey []uint8, nextKey []uint8, startLevel uint32) {
	level := startLevel

	lengthOfCurrentKey := uint32(len(currentKey))

	if (level == lengthOfCurrentKey-1) || (level >= uint32(len(nextKey))) || !isSameKey(currentKey[0:level+1], nextKey[0:level+1]) {
		me.storeKeyByte(currentKey[level], level == lengthOfCurrentKey-1, currentKey[level+1:], level, currentKey)
		return
	}
	me.storeKeyByte(currentKey[level], level == lengthOfCurrentKey-1, nil, level, currentKey)
	level++

	for level < lengthOfCurrentKey {
		if (level == lengthOfCurrentKey-1) || (level >= uint32(len(nextKey))) || !isSameKey(currentKey[0:level+1], nextKey[0:level+1]) {
			me.storeKeyByte(currentKey[level], level == lengthOfCurrentKey-1, currentKey[level+1:], level, currentKey)
			return
		}
		me.storeKeyByte(currentKey[level], level == lengthOfCurrentKey-1, nil, level, currentKey)
		level++
	}
}

func (me *_SuRFBuilder4Suffix) storeKeyByte(keyByte uint8, isLastByte bool, suffix []uint8, level uint32, currentKey []uint8) {
	if level >= me.getTreeHeight() {
		me.addTreeLevel()
	}

	me.labelsTree[level] = append(me.labelsTree[level], keyByte)
	me.loudsBits[level] = append(me.loudsBits[level], 0)
	me.suffixes[level] = append(me.suffixes[level], suffix)

	if level > 0 {
		upperFlat := me.loudsBits[level-1]
		upperFlat[len(upperFlat)-1]++
	}
}

func (me *_SuRFBuilder4Suffix) addTreeLevel() {
	me.labelsTree = append(me.labelsTree, make([]uint8, 0))
	me.loudsBits = append(me.loudsBits, make([]uint8, 0))
	me.suffixes = append(me.suffixes, make([][]uint8, 0))
}

func (me *_SuRFBuilder4Suffix) getTreeHeight() uint32 {
	return uint32(len(me.labelsTree))
}

func (me *_SuRFBuilder4Suffix) printMem() {
	countOfBytes := uint64(0)
	countOfNodes := [0x100]uint64{}
	for iL, treeFlat := range me.labelsTree {
		countOfBytes += uint64(len(treeFlat))
		var countOfChildren []uint8
		if iL == 0 {
			countOfChildren = []uint8{uint8(len(me.labelsTree[0]))}
		} else {
			countOfChildren = me.loudsBits[iL-1]
		}

		for _, count := range countOfChildren {
			countOfNodes[count]++
		}
	}

	for _, count := range me.loudsBits[len(me.loudsBits)-1] {
		countOfNodes[count]++
	}

	log.Println("count of bytes by sparse:", countOfBytes)
	for i, c := range countOfNodes {
		if c > 0 {
			log.Println(i, "个byte的node有", c, "个")
		}
	}

	// me.display()
}

func (me *_SuRFBuilder4Suffix) preferredCutoffLevel() uint32 {
	return 4
}

// SuRF4Suffix SuRF4Suffix
type SuRF4Suffix struct {
	cutoffLevel uint32
	// Dense Nodes
	denseBitmapLabels         []uint64
	denseBitmapChildIndicator []uint64
	denseBitmapClosure        []uint64
	denseNodNumbers           uint32
	// Sparse Nodes
	// 每一个label对应一个childIndicator以及一个closure吗?这占的空间也不小啊,这样岂不是只有一个byte时用sparse才划算?这不对吧
	sparseLabels           []uint8
	sparseChildIndicator   []bool
	sparseClosure          []bool
	sparseStartIndexOfNode []uint64
	// Suffix
	suffix [][]uint8
	// LUT
	lookupTable4Child []uint32 // 保存每个nod-num对应的first-child的nod-num
	lookupTable4Value []uint32 //保存每个nod-num中first-value是第几个value

	lookupTable4ClosureIndex []uint32 // 保存第n个key所在的nod-num
	lookupTable4Parent       []uint32 // 保存每个nod-num对应的parent-nod-num,第0个nod-num的parent设为0
}

func newSuRF4Suffix() *SuRF4Suffix {
	return &SuRF4Suffix{
		denseBitmapLabels: make([]uint64, 0),

		denseBitmapChildIndicator: make([]uint64, 0),
		lookupTable4Child:         make([]uint32, 0), // nod-num为index,对应值表示如果有sub,那么first-sub是第几个nod-num

		denseBitmapClosure: make([]uint64, 0),
		lookupTable4Value:  make([]uint32, 0),

		sparseStartIndexOfNode:   []uint64{0},
		lookupTable4ClosureIndex: make([]uint32, 0),
		lookupTable4Parent:       []uint32{0},
	}
}

func (me *SuRF4Suffix) generateFromBuilder(builder *_SuRFBuilder4Suffix) {
	me.cutoffLevel = builder.preferredCutoffLevel()
	var countOfChildren = uint32(1)
	var countOfValues = uint32(0)
	var indexOfCurrentNodeInAllNodes = uint32(0)

	for iL := uint32(0); iL < builder.getTreeHeight(); iL++ {
		var nodesSep []uint8
		if iL == 0 {
			nodesSep = []uint8{uint8(len(builder.labelsTree[0]))}
		} else {
			nodesSep = builder.loudsBits[iL-1]
		}

		isDenseNodeLevel := iL < me.cutoffLevel

		startIndex := uint32(0)
		for _, nodeSize := range nodesSep {
			if nodeSize == 0 {
				continue
			}
			endIndex := startIndex + uint32(nodeSize)
			me.lookupTable4Child = append(me.lookupTable4Child, countOfChildren)
			me.lookupTable4Value = append(me.lookupTable4Value, countOfValues)

			if isDenseNodeLevel {
				me.buildDenseNode(builder, iL, startIndex, endIndex, &countOfChildren, &countOfValues)
			} else {
				me.buildSparseNode(builder, iL, startIndex, endIndex, &countOfChildren, &countOfValues)
			}

			countOfValuesInCurrentNode := countOfValues - me.lookupTable4Value[len(me.lookupTable4Value)-1]
			for i := uint32(0); i < countOfValuesInCurrentNode; i++ {
				me.lookupTable4ClosureIndex = append(me.lookupTable4ClosureIndex, indexOfCurrentNodeInAllNodes)
			}
			countOfChildrenInCurrentNode := countOfChildren - me.lookupTable4Child[len(me.lookupTable4Child)-1]
			for i := uint32(0); i < countOfChildrenInCurrentNode; i++ {
				me.lookupTable4Parent = append(me.lookupTable4Parent, indexOfCurrentNodeInAllNodes)
			}

			startIndex = endIndex
			indexOfCurrentNodeInAllNodes++
		}
	}

	me.lookupTable4Child = append(me.lookupTable4Child, countOfChildren)
	me.lookupTable4Value = append(me.lookupTable4Value, countOfValues)

	// log.Println(me.lookupTable4Child)
	// log.Println(me.lookupTable4Value)
	// for i := range me.suffix {
	// 	log.Println(string(me.suffix[i]), "=>", me.values[i])
	// }
}

func (me *SuRF4Suffix) buildDenseNode(builder *_SuRFBuilder4Suffix, indexOfLevel uint32, startIndex uint32, endIndex uint32, lut4ChildCount *uint32, lut4ValueCount *uint32) {
	labelLevel := builder.labelsTree[indexOfLevel]
	suffixesLevel := builder.suffixes[indexOfLevel]
	loudsBitsLevel := builder.loudsBits[indexOfLevel]

	labelBitmap := make([]uint64, 4)
	childIndicatorBitmap := make([]uint64, 4)
	closureBitmap := make([]uint64, 4)

	for i := startIndex; i < endIndex; i++ {
		b := labelLevel[i]
		uint256Mark1(labelBitmap, b)

		if suffixesLevel[i] != nil {
			uint256Mark1(closureBitmap, b)
			(*lut4ValueCount)++
			me.suffix = append(me.suffix, suffixesLevel[i])
		}
		if loudsBitsLevel[i] > 0 {
			uint256Mark1(childIndicatorBitmap, b)
			(*lut4ChildCount)++
		}
	}

	me.denseBitmapLabels = append(me.denseBitmapLabels, labelBitmap...)
	me.denseBitmapChildIndicator = append(me.denseBitmapChildIndicator, childIndicatorBitmap...)
	me.denseBitmapClosure = append(me.denseBitmapClosure, closureBitmap...)
	me.denseNodNumbers++
}

func (me *SuRF4Suffix) buildSparseNode(builder *_SuRFBuilder4Suffix, indexOfLevel uint32, startIndex uint32, endIndex uint32, lut4ChildCount *uint32, lut4ValueCount *uint32) {
	labelLevel := builder.labelsTree[indexOfLevel]
	suffixesLevel := builder.suffixes[indexOfLevel]
	loudsBitsLevel := builder.loudsBits[indexOfLevel]

	labels := make([]uint8, 0)
	childIndicator := make([]bool, 0)
	closure := make([]bool, 0)
	for i := startIndex; i < endIndex; i++ {
		b := labelLevel[i]
		labels = append(labels, b)
		if suffixesLevel[i] != nil {
			closure = append(closure, true)
			(*lut4ValueCount)++
			me.suffix = append(me.suffix, suffixesLevel[i])
		} else {
			closure = append(closure, false)
		}

		if loudsBitsLevel[i] > 0 {
			childIndicator = append(childIndicator, true)
			(*lut4ChildCount)++
		} else {
			childIndicator = append(childIndicator, false)
		}
	}

	me.sparseLabels = append(me.sparseLabels, labels...)
	me.sparseClosure = append(me.sparseClosure, closure...)
	me.sparseChildIndicator = append(me.sparseChildIndicator, childIndicator...)
	me.sparseStartIndexOfNode = append(me.sparseStartIndexOfNode, uint64(len(me.sparseLabels)))
}

// KeyByIndex KeyByIndex
func (me *SuRF4Suffix) KeyByIndex(index uint32) []uint8 {
	suffix := me.suffix[index]
	closureNodNumber := me.lookupTable4ClosureIndex[index]
	closureByteIndexInNode := uint8(0)
	for index > 0 {
		if me.lookupTable4ClosureIndex[index-1] == closureNodNumber {
			closureByteIndexInNode++
		} else {
			break
		}
		index--
	}
	found, byteIndexInNode := me.byteIndexOfClosureByteIndex(closureNodNumber, closureByteIndexInNode)
	if !found {
		return nil
	}
	if found, bytesFound := me.findBytesFrom(closureNodNumber, byteIndexInNode, suffix); found {
		return bytesFound
	}

	return nil
}

func (me *SuRF4Suffix) parentOfNodeNumber(nodeNumber uint32) (uint32, uint8) {
	parentNodeNumber := me.lookupTable4Parent[nodeNumber]
	if parentNodeNumber == nodeNumber {
		return parentNodeNumber, 0
	}

	firstChildNodeNumberOfParent := me.lookupTable4Child[parentNodeNumber]

	found, byteIndex := me.byteIndexOfChildByteIndex(parentNodeNumber, uint8(nodeNumber-firstChildNodeNumberOfParent))
	if !found {
		panic("impossible")
	}

	return parentNodeNumber, byteIndex
}

func (me *SuRF4Suffix) findBytesFrom(nodeNumber uint32, byteIndex uint8, suffixBytes []uint8) (bool, []uint8) {
	found, byteFound := me.findByte(nodeNumber, byteIndex)
	if !found {
		return false, nil
	}

	parentNodeNumber, indexInParentNode := me.parentOfNodeNumber(nodeNumber)
	newSuffixBytes := append([]uint8{byteFound}, suffixBytes...)
	if parentNodeNumber == nodeNumber {
		return true, newSuffixBytes
	}

	return me.findBytesFrom(parentNodeNumber, indexInParentNode, newSuffixBytes)
}

func (me *SuRF4Suffix) findByte(nodeNumber uint32, byteIndex uint8) (bool, uint8) {
	if nodeNumber >= me.denseNodNumbers {
		return me.sparseFindByte(nodeNumber, byteIndex)
	}

	return me.denseFindByte(nodeNumber, byteIndex)
}

func (me *SuRF4Suffix) byteIndexOfChildByteIndex(nodeNumber uint32, childIndex uint8) (bool, uint8) {
	if nodeNumber >= me.denseNodNumbers {
		return me.sparseByteIndexOfChildByteIndex(nodeNumber, childIndex)
	}

	return me.denseByteIndexOfChildByteIndex(nodeNumber, childIndex)
}

func (me *SuRF4Suffix) sparseByteIndexOfChildByteIndex(nodeNumber uint32, childIndex uint8) (bool, uint8) {
	startIndexOfNode := me.sparseStartIndexOfNode[nodeNumber-me.denseNodNumbers]
	endIndexOfNode := me.sparseStartIndexOfNode[nodeNumber+1-me.denseNodNumbers]

	for i := startIndexOfNode; i < endIndexOfNode; i++ {
		if me.sparseChildIndicator[i] {
			childIndex--
		}

		if childIndex == 0xFF {
			return true, uint8(i - startIndexOfNode)
		}
	}
	return false, 0
}

func (me *SuRF4Suffix) denseByteIndexOfChildByteIndex(nodeNumber uint32, childIndex uint8) (bool, uint8) {
	startIndexOfNode := nodeNumber << 2
	endIndexOfNode := (nodeNumber + 1) << 2

	found, pos := uint256PosOf1(me.denseBitmapChildIndicator[startIndexOfNode:endIndexOfNode], childIndex)
	if !found {
		return false, 0
	}

	return true, uint256IndexOfNode(me.denseBitmapLabels[startIndexOfNode:endIndexOfNode], pos)
}

func (me *SuRF4Suffix) byteIndexOfClosureByteIndex(nodeNumber uint32, closureByteIndex uint8) (bool, uint8) {
	if nodeNumber >= me.denseNodNumbers {
		return me.sparseByteIndexOfClosureByteIndex(nodeNumber, closureByteIndex)
	}

	return me.denseByteIndexOfClosureByteIndex(nodeNumber, closureByteIndex)
}

func (me *SuRF4Suffix) denseByteIndexOfClosureByteIndex(nodeNumber uint32, closureByteIndex uint8) (bool, uint8) {
	startIndexOfNode := nodeNumber << 2
	endIndexOfNode := (nodeNumber + 1) << 2

	found, pos := uint256PosOf1(me.denseBitmapClosure[startIndexOfNode:endIndexOfNode], closureByteIndex)
	if !found {
		return false, 0
	}

	return true, uint256IndexOfNode(me.denseBitmapLabels[startIndexOfNode:endIndexOfNode], pos)
}

func (me *SuRF4Suffix) sparseByteIndexOfClosureByteIndex(nodeNumber uint32, closureByteIndex uint8) (bool, uint8) {
	startIndexOfNode := me.sparseStartIndexOfNode[nodeNumber-me.denseNodNumbers]
	endIndexOfNode := me.sparseStartIndexOfNode[nodeNumber+1-me.denseNodNumbers]

	for i := startIndexOfNode; i < endIndexOfNode; i++ {
		if me.sparseClosure[i] {
			closureByteIndex--
		}

		if closureByteIndex == 0xFF {
			return true, uint8(i - startIndexOfNode)
		}
	}
	return false, 0
}

func (me *SuRF4Suffix) denseFindByte(nodeNumber uint32, byteIndex uint8) (bool, uint8) {
	startIndexOfNode := nodeNumber << 2
	endIndexOfNode := (nodeNumber + 1) << 2

	return uint256PosOf1(me.denseBitmapLabels[startIndexOfNode:endIndexOfNode], byteIndex)
}

func (me *SuRF4Suffix) sparseFindByte(nodeNumber uint32, byteIndex uint8) (bool, uint8) {
	startIndexOfNode := me.sparseStartIndexOfNode[nodeNumber-me.denseNodNumbers]
	// endIndexOfNode := me.sparseStartIndexOfNode[nodeNumber+1-me.denseNodNumbers]

	return true, me.sparseLabels[startIndexOfNode+uint64(byteIndex)]
}

// Lookup Lookup for index
func (me *SuRF4Suffix) Lookup(key []uint8) (bool, uint32) {
	return me._Lookup(0, 0, key)
}

func (me *SuRF4Suffix) _Lookup(nodeNumber uint32, byteIndexOfKey2Lookup uint32, key []uint8) (bool, uint32) {
	denseLookup := byteIndexOfKey2Lookup < me.cutoffLevel
	if denseLookup {
		return me.denseLookup(nodeNumber, byteIndexOfKey2Lookup, key)
	}

	return me.sparseLookup(nodeNumber, byteIndexOfKey2Lookup, key)
}

func (me *SuRF4Suffix) denseLookup(nodeNumber uint32, byteIndexOfKey2Lookup uint32, key []uint8) (bool, uint32) {
	startIndexOfNode := nodeNumber << 2
	endIndexOfNode := (nodeNumber + 1) << 2

	// 如果该byte有closure,那么查一下这个byte对应的suffix与当前key是否匹配
	if uint256IsMarked(me.denseBitmapClosure[startIndexOfNode:endIndexOfNode], key[byteIndexOfKey2Lookup]) {
		countOfValuesBeforeNode := me.lookupTable4Value[nodeNumber]
		countOfValuesBeforeByte := uint256IndexOfNode(me.denseBitmapClosure[startIndexOfNode:endIndexOfNode], key[byteIndexOfKey2Lookup])
		if isSameKey(me.suffix[countOfValuesBeforeNode+uint32(countOfValuesBeforeByte)], key[byteIndexOfKey2Lookup+1:]) {
			return true, countOfValuesBeforeNode + uint32(countOfValuesBeforeByte)
		}
	}

	// 如果当前byte作为closure与key不匹配,那么看一下当前byte下面的child去递归吧
	if (byteIndexOfKey2Lookup+1 < uint32(len(key))) && uint256IsMarked(me.denseBitmapChildIndicator[startIndexOfNode:endIndexOfNode], key[byteIndexOfKey2Lookup]) {
		indexOfChild := uint256IndexOfNode(me.denseBitmapChildIndicator[startIndexOfNode:endIndexOfNode], key[byteIndexOfKey2Lookup])
		nodeNumberOfChild := me.lookupTable4Child[nodeNumber] + uint32(indexOfChild)

		return me._Lookup(nodeNumberOfChild, byteIndexOfKey2Lookup+1, key)
	}

	return false, 0
}

func (me *SuRF4Suffix) sparseLookup(nodeNumber uint32, byteIndexOfKey2Lookup uint32, key []uint8) (bool, uint32) {
	startIndexOfNode := me.sparseStartIndexOfNode[nodeNumber-me.denseNodNumbers]
	endIndexOfNode := me.sparseStartIndexOfNode[nodeNumber+1-me.denseNodNumbers]

	byte2Lookup := key[byteIndexOfKey2Lookup]

	var byteIndexOfLabels uint64
	var byteIndexOfLabelsFound = false
	for i := startIndexOfNode; i < endIndexOfNode; i++ {
		if me.sparseLabels[i] == byte2Lookup {
			byteIndexOfLabels = i
			byteIndexOfLabelsFound = true
			break
		}
	}

	if !byteIndexOfLabelsFound {
		return false, 0
	}

	// 如果该byte有closure,那么查一下这个byte对应的suffix与当前key是否匹配
	if me.sparseClosure[byteIndexOfLabels] {
		countOfValuesBeforeNode := me.lookupTable4Value[nodeNumber]
		countOfValuesBeforeByte := 0
		for i := startIndexOfNode; i < byteIndexOfLabels; i++ {
			if me.sparseClosure[i] {
				countOfValuesBeforeByte++
			}
		}

		if isSameKey(me.suffix[countOfValuesBeforeNode+uint32(countOfValuesBeforeByte)], key[byteIndexOfKey2Lookup+1:]) {
			return true, countOfValuesBeforeNode + uint32(countOfValuesBeforeByte)
		}
	}

	// 如果当前byte作为closure与key不匹配,那么看一下当前byte下面的child去递归吧
	if (byteIndexOfKey2Lookup+1 < uint32(len(key))) && me.sparseChildIndicator[byteIndexOfLabels] {
		indexOfChild := 0
		for i := startIndexOfNode; i < byteIndexOfLabels; i++ {
			if me.sparseChildIndicator[i] {
				indexOfChild++
			}
		}
		nodeNumberOfChild := me.lookupTable4Child[nodeNumber] + uint32(indexOfChild)
		return me._Lookup(nodeNumberOfChild, byteIndexOfKey2Lookup+1, key)
	}

	return false, 0
}

// ReadRandomTextAsSuRF4Suffix Read As SuRF4Suffix
func ReadRandomTextAsSuRF4Suffix(filename string, maxLines uint64, doAssert bool) *SuRF4Suffix {
	textList := ReadFileAsList(filename, maxLines)
	mapOB := ReadFileAsOb(textList)

	CreateMemFile("ob_mem_file")

	start := time.Now().UnixNano()

	stringKeys := make([]string, 0, len(mapOB))
	for k := range mapOB {
		stringKeys = append(stringKeys, k)
	}

	log.Println("Count Of String:", len(stringKeys))

	sort.Strings(stringKeys)

	log.Println("sort keys time spent:", (time.Now().UnixNano()-start)/1000000)
	start = time.Now().UnixNano()
	keyBytes := _MapStringAsBytes(stringKeys)
	builder := newSuRFBuilder4Suffix(keyBytes)
	log.Println("build surf time spent:", (time.Now().UnixNano()-start)/1000000)

	stringKeys = nil
	mapOB = nil
	runtime.GC()
	CreateMemFile("builder_mem_file")

	start = time.Now().UnixNano()
	sf := newSuRF4Suffix()
	sf.generateFromBuilder(builder)
	log.Println("create surf time spent:", (time.Now().UnixNano()-start)/1000000)

	builder = nil
	runtime.GC()
	CreateMemFile("surf_mem_file")

	sf.assertKeyBytes(keyBytes)

	return sf
}

func (me *SuRF4Suffix) assertKeyBytes(keyBytes [][]uint8) {
	for _, kBytes := range keyBytes {
		// log.Println("assert:looking for [", string(kBytes), "]--", kBytes)
		found, indexOfClosureByte := me.Lookup(kBytes)
		if !found {
			panic(fmt.Sprintln(string(kBytes), " not found"))
		}
		// log.Println("assert:index of closure byte:", indexOfClosureByte)

		keyFound := me.KeyByIndex(indexOfClosureByte)
		if !isSameKey(kBytes, keyFound) {
			panic(fmt.Sprintln(string(kBytes), " != ", string(keyFound)))
		}
	}
}

func _MapStringAsBytes(strings []string) [][]uint8 {
	res := make([][]uint8, len(strings))
	for i, s := range strings {
		res[i] = []byte(s)
	}
	return res
}
