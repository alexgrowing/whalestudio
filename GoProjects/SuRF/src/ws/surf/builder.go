package surf

import (
	"log"
	"os"
	"runtime"
	"runtime/pprof"
	"sort"
	"time"
)

// ReadRandomTextAsSuRF 不生成TreeNode了,先把string排序,然后就可以直接LOUDS了吧
func ReadRandomTextAsSuRF(textList []string, doAssert bool) *SuRF {
	mapOB := ReadFileAsOb(textList)

	CreateMemFile("ob_mem_file")

	start := time.Now().UnixNano()

	stringKeys := make([]string, 0, len(mapOB))
	countOfValueLines := uint64(0)
	for k, v := range mapOB {
		stringKeys = append(stringKeys, k)
		countOfValueLines += uint64(len(v.values))
	}

	log.Println("Count Of String:", len(stringKeys))

	sort.Strings(stringKeys)

	log.Println("sort keys time spent:", (time.Now().UnixNano()-start)/1000000)
	start = time.Now().UnixNano()
	builder := newSuRFBuilder(stringKeys, mapOB)
	log.Println("build surf time spent:", (time.Now().UnixNano()-start)/1000000)

	countOfStringKeys := len(stringKeys)
	stringKeys = nil
	runtime.GC()
	CreateMemFile("builder_mem_file")

	start = time.Now().UnixNano()
	surf := newSuRF(uint64(countOfStringKeys), countOfValueLines)

	surf.generateFromBuilder(builder)
	log.Println("create surf time spent:", (time.Now().UnixNano()-start)/1000000)

	if doAssert {
		start = time.Now().UnixNano()
		cpuf, err := os.Create("cpu_profile")
		if err != nil {
			log.Fatal(err)
		}
		pprof.StartCPUProfile(cpuf)

		notMatchFound := false
		var key2Lookup string
		var valueShouldBe *Value
		var valueFound *Value
		for mapK, mapV := range mapOB {
			key2Lookup = mapK
			// log.Println("Looking for [", key2Lookup, "]---", []byte(key2Lookup))
			valueFound = surf.Lookup([]byte(key2Lookup))
			valueShouldBe = mapV

			if !isSameKey64(valueShouldBe.values, valueFound.values) {
				notMatchFound = true
				break
			}
		}
		if !notMatchFound {
			log.Println("surf构建完全正确")
		} else {
			log.Println("surf构建失败:", string(key2Lookup), ";found:", valueFound, ";should:", valueShouldBe)
		}

		log.Println("assert time spent:", (time.Now().UnixNano()-start)/1000000)
		pprof.StopCPUProfile()
	}

	mapOB = nil
	builder = nil
	runtime.GC()
	CreateMemFile("surf_mem_file")
	return surf
}

func sortBytes(bytes [][]uint8) {
	sort.SliceStable(bytes, func(iL int, iR int) bool {
		left := bytes[iL]
		right := bytes[iR]
		lenOfLeft := len(left)
		lenOfRight := len(right)

		index2Compare := 0
		for {
			if lenOfRight == index2Compare {
				return false
			}

			if lenOfLeft == index2Compare {
				return true
			}

			if left[index2Compare] == right[index2Compare] {
				index2Compare++
				continue
			}

			return left[index2Compare] < right[index2Compare]
		}
	})
}

// SuRF 最终输出结果
type SuRF struct {
	startLevelOfSparse uint32
	// Dense Nodes
	denseBitmapChildIndicator []uint64
	denseBitmapClosure        []uint64
	denseNodNumbers           uint32
	// Sparse Nodes
	// 每一个label对应一个childIndicator以及一个closure吗?这占的空间也不小啊,这样岂不是只有一个byte时用sparse才划算?这不对吧
	sparseLabels               *LabelVector
	sparseBitmapChildIndicator []uint64
	sparseBitmapClosure        []uint64
	sparseBitmapNodeStartTag   *BitVectorSelect
	// 对应每个byte以1表示该byte是不是start,然后加一个以256位为间隔的LUT,记录有多少个1
	// 先与sparseStartIndexOfNode两套逻辑并存,经过检验后再替换掉

	// Suffix
	hashOfSuffix []uint32
	// Values
	values         []uint64
	indices4Values []uint64
	// LUT
	lookupTable4Child []uint32
	lookupTable4Value []uint32
}

func newSuRF(countOfEndNodes uint64, countOfValueLines uint64) *SuRF {
	return &SuRF{
		denseBitmapChildIndicator: make([]uint64, 0),
		lookupTable4Child:         []uint32{}, // nod-num为index,对应值表示如果有sub,那么first-sub是第几个nod-num

		denseBitmapClosure: make([]uint64, 0),
		lookupTable4Value:  []uint32{},

		sparseLabels:             newLabelVector(0),
		sparseBitmapNodeStartTag: newBitVectorSelect(),

		values:         make([]uint64, 0, countOfValueLines), // nod-num为index,到
		indices4Values: make([]uint64, 0, countOfEndNodes+1),
		hashOfSuffix:   make([]uint32, 0, countOfEndNodes),
	}
}

// Lookup find key by point
func (me *SuRF) Lookup(key []uint8) *Value {
	return &Value{
		values: me._Lookup(0, 0, key),
	}
}

func (me *SuRF) _Lookup(nodeNumber uint32, byteIndexOfKey2Lookup uint32, key []uint8) []uint64 {
	denseLookup := byteIndexOfKey2Lookup < me.startLevelOfSparse
	if denseLookup {
		return me.denseLookup(nodeNumber, byteIndexOfKey2Lookup, key)
	}

	return me.sparseLookup(nodeNumber, byteIndexOfKey2Lookup, key)
}

func (me *SuRF) denseLookup(nodeNumber uint32, byteIndexOfKey2Lookup uint32, key []uint8) []uint64 {
	startIndexOfNode := nodeNumber << 2
	endIndexOfNode := (nodeNumber + 1) << 2

	// 如果该byte有closure,那么查一下这个byte对应的suffix与当前key是否匹配
	if uint256IsMarked(me.denseBitmapClosure[startIndexOfNode:endIndexOfNode], key[byteIndexOfKey2Lookup]) {
		countOfValuesBeforeNode := me.lookupTable4Value[nodeNumber]
		countOfValuesBeforeByte := uint256IndexOfNode(me.denseBitmapClosure[startIndexOfNode:endIndexOfNode], key[byteIndexOfKey2Lookup])

		if me.hashOfSuffix[countOfValuesBeforeNode+uint32(countOfValuesBeforeByte)] == hash32(key) {
			startIndexOfValues := me.indices4Values[countOfValuesBeforeNode+uint32(countOfValuesBeforeByte)]
			endIndexOfValues := me.indices4Values[countOfValuesBeforeNode+uint32(countOfValuesBeforeByte)+1]
			return me.values[startIndexOfValues:endIndexOfValues]
		}
	}

	// 如果当前byte作为closure与key不匹配,那么看一下当前byte下面的child去递归吧
	if (byteIndexOfKey2Lookup+1 < uint32(len(key))) && uint256IsMarked(me.denseBitmapChildIndicator[startIndexOfNode:endIndexOfNode], key[byteIndexOfKey2Lookup]) {
		indexOfChild := uint256IndexOfNode(me.denseBitmapChildIndicator[startIndexOfNode:endIndexOfNode], key[byteIndexOfKey2Lookup])
		nodeNumberOfChild := me.lookupTable4Child[nodeNumber] + uint32(indexOfChild)

		return me._Lookup(nodeNumberOfChild, byteIndexOfKey2Lookup+1, key)
	}

	return nil
}

func (me *SuRF) sparseLookup(nodeNumber uint32, byteIndexOfKey2Lookup uint32, key []uint8) []uint64 {
	nodeNumberOfSparse := nodeNumber - me.denseNodNumbers
	startIndexOfNode := me.sparseBitmapNodeStartTag.select1(uint64(nodeNumberOfSparse))

	byte2Lookup := key[byteIndexOfKey2Lookup]

	var byteIndexOfLabels uint64
	var byteIndexOfLabelsFound = false
	for i := startIndexOfNode; i < me.sparseLabels.countOfLabels(); i++ {
		if i > startIndexOfNode && me.sparseBitmapNodeStartTag.isMarked(i) {
			break
		}
		if me.sparseLabels.labelByIndex(i) == byte2Lookup {
			byteIndexOfLabels = i
			byteIndexOfLabelsFound = true
			break
		}
	}

	if !byteIndexOfLabelsFound {
		return nil
	}

	// 如果该byte有closure,那么查一下这个byte对应的suffix与当前key是否匹配
	if me.isSparseClousreByIndex(byteIndexOfLabels) {
		countOfValuesBeforeNode := me.lookupTable4Value[nodeNumber]
		countOfValuesBeforeByte := 0
		for i := startIndexOfNode; i < byteIndexOfLabels; i++ {
			if me.isSparseClousreByIndex(i) {
				countOfValuesBeforeByte++
			}
		}

		if me.hashOfSuffix[countOfValuesBeforeNode+uint32(countOfValuesBeforeByte)] == hash32(key) {
			startIndexOfValues := me.indices4Values[countOfValuesBeforeNode+uint32(countOfValuesBeforeByte)]
			endIndexOfValues := me.indices4Values[countOfValuesBeforeNode+uint32(countOfValuesBeforeByte)+1]
			return me.values[startIndexOfValues:endIndexOfValues]
		}
	}

	// 如果当前byte作为closure与key不匹配,那么看一下当前byte下面的child去递归吧
	if (byteIndexOfKey2Lookup+1 < uint32(len(key))) && me.isSparseChildIndicatorByIndex(byteIndexOfLabels) {
		indexOfChild := 0
		for i := startIndexOfNode; i < byteIndexOfLabels; i++ {
			if me.isSparseChildIndicatorByIndex(i) {
				indexOfChild++
			}
		}
		nodeNumberOfChild := me.lookupTable4Child[nodeNumber] + uint32(indexOfChild)
		return me._Lookup(nodeNumberOfChild, byteIndexOfKey2Lookup+1, key)
	}

	return nil
}

func (me *SuRF) isSparseClousreByIndex(index uint64) bool {
	return uint64IsMarked(me.sparseBitmapClosure, index)
}

func (me *SuRF) isSparseChildIndicatorByIndex(index uint64) bool {
	return uint64IsMarked(me.sparseBitmapChildIndicator, index)
}

func (me *SuRF) generateFromBuilder(builder *_SuRFBuilder) {
	me.startLevelOfSparse = builder.preferredStartLevelOfSparse()
	var countOfChildren = uint32(1)
	var countOfValues = uint32(0)

	for iL := uint32(0); iL < builder.getTreeHeight(); iL++ {
		var nodesSep []uint8
		if iL == 0 {
			nodesSep = []uint8{uint8(len(builder.labelsTree[0]))}
		} else {
			nodesSep = builder.loudsBits[iL-1]
		}

		isDenseNodeLevel := iL < me.startLevelOfSparse

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

			startIndex = endIndex
		}
	}

	me.indices4Values = append(me.indices4Values, uint64(len(me.values)))
	me.lookupTable4Child = append(me.lookupTable4Child, countOfChildren)
	me.lookupTable4Value = append(me.lookupTable4Value, countOfValues)
	me.sparseBitmapNodeStartTag.initSelectLUT()

	sizeOfDense := uint64(len(me.denseBitmapChildIndicator)) << 4
	sizeOfSparse := me.sparseLabels.memorySize() + me.sparseBitmapNodeStartTag.memorySize() + (uint64(len(me.sparseBitmapChildIndicator)) << 4)
	sizeOfSuffix := uint64(len(me.hashOfSuffix)) << 2
	sizeOfValue := uint64(len(me.values))<<3 + uint64(len(me.indices4Values))<<3
	sizeOfLUT4Child := uint64(len(me.lookupTable4Child)) << 2
	sizeOfLUT4Value := uint64(len(me.lookupTable4Value)) << 2
	log.Println("size of dense:", SizeOfBytesAsString(uint64(sizeOfDense)))
	log.Println("size of sparse:", SizeOfBytesAsString(uint64(sizeOfSparse)))
	log.Println("size of LUT4Chld:", SizeOfBytesAsString(uint64(sizeOfLUT4Child)))
	log.Println("size of LUT4Value:", SizeOfBytesAsString(uint64(sizeOfLUT4Value)))
	log.Println("size of suffix:", SizeOfBytesAsString(uint64(sizeOfSuffix)))
	log.Println("size of value:", SizeOfBytesAsString(uint64(sizeOfValue)))
	log.Println("size of all:", SizeOfBytesAsString(uint64(sizeOfDense+sizeOfSparse+sizeOfSuffix+sizeOfValue+sizeOfLUT4Child+sizeOfLUT4Value)))
}

func (me *SuRF) buildDenseNode(builder *_SuRFBuilder, indexOfLevel uint32, startIndex uint32, endIndex uint32, lut4ChildCount *uint32, lut4ValueCount *uint32) {
	labelLevel := builder.labelsTree[indexOfLevel]
	suffixesLevel := builder.hash32OfSuffixes[indexOfLevel]
	valuesLevel := builder.values[indexOfLevel]
	loudsBitsLevel := builder.loudsBits[indexOfLevel]

	labelBitmap := make([]uint64, 4)
	childIndicatorBitmap := make([]uint64, 4)
	closureBitmap := make([]uint64, 4)

	for i := startIndex; i < endIndex; i++ {
		b := labelLevel[i]
		uint256Mark1(labelBitmap, b)

		if suffixesLevel[i] != 0 {
			uint256Mark1(closureBitmap, b)
			(*lut4ValueCount)++

			me.indices4Values = append(me.indices4Values, uint64(len(me.values)))
			me.hashOfSuffix = append(me.hashOfSuffix, suffixesLevel[i])
			me.values = append(me.values, valuesLevel[i].values...)
		}
		if loudsBitsLevel[i] > 0 {
			uint256Mark1(childIndicatorBitmap, b)
			(*lut4ChildCount)++
		}
	}

	me.denseBitmapChildIndicator = append(me.denseBitmapChildIndicator, childIndicatorBitmap...)
	me.denseBitmapClosure = append(me.denseBitmapClosure, closureBitmap...)
	me.denseNodNumbers++
}

func (me *SuRF) buildSparseNode(builder *_SuRFBuilder, indexOfLevel uint32, startIndex uint32, endIndex uint32, lut4ChildCount *uint32, lut4ValueCount *uint32) {
	labelLevel := builder.labelsTree[indexOfLevel]
	suffixesLevel := builder.hash32OfSuffixes[indexOfLevel]
	valuesLevel := builder.values[indexOfLevel]
	loudsBitsLevel := builder.loudsBits[indexOfLevel]

	me.ensureSparseBitmap(me.sparseLabels.countOfLabels() + uint64(endIndex-startIndex))
	for i := startIndex; i < endIndex; i++ {
		indexOfCurrentByte := me.sparseLabels.countOfLabels()
		b := labelLevel[i]
		me.sparseLabels.appendLabel(b)
		if i == startIndex {
			me.sparseBitmapNodeStartTag.mark1(indexOfCurrentByte)
		}
		if suffixesLevel[i] != 0 {
			uint64Mark1(me.sparseBitmapClosure, indexOfCurrentByte)
			(*lut4ValueCount)++
			me.indices4Values = append(me.indices4Values, uint64(len(me.values)))
			me.hashOfSuffix = append(me.hashOfSuffix, suffixesLevel[i])
			me.values = append(me.values, valuesLevel[i].values...)
		}

		if loudsBitsLevel[i] > 0 {
			uint64Mark1(me.sparseBitmapChildIndicator, indexOfCurrentByte)
			(*lut4ChildCount)++
		}
	}
}

func (me *SuRF) ensureSparseBitmap(size uint64) {
	for (uint64(len(me.sparseBitmapChildIndicator)) << 6) < size {
		me.sparseBitmapChildIndicator = append(me.sparseBitmapChildIndicator, 0)
		me.sparseBitmapClosure = append(me.sparseBitmapClosure, 0)
		me.sparseBitmapNodeStartTag.malloc()
	}
}

type _SuRFBuilder struct {
	labelsTree [][]uint8 // 记录每一个byte
	loudsBits  [][]uint8 // 记录每个byte下面有多少个children

	hash32OfSuffixes [][]uint32
	values           [][]*Value
}

func newSuRFBuilder(stringKeys []string, ob map[string]*Value) *_SuRFBuilder {
	builder := &_SuRFBuilder{
		labelsTree: make([][]uint8, 0),
		loudsBits:  make([][]uint8, 0),

		hash32OfSuffixes: make([][]uint32, 0),
		values:           make([][]*Value, 0),
	}
	builder.build(stringKeys, ob)

	return builder
}

func (me *_SuRFBuilder) buildLabelsAsBitmap(labels []uint8) []uint64 {
	res := make([]uint64, 4)
	for _, b := range labels {
		uint256Mark1(res, b)
	}

	return res
}

func (me *_SuRFBuilder) buildCountOfChildrenAsChildIndicatorBitmap(labels []uint8, countOfChildren []uint8) []uint64 {
	res := make([]uint64, 4)
	for i, count := range countOfChildren {
		if count > 0 {
			uint256Mark1(res, labels[i])
		}
	}

	return res
}

func (me *_SuRFBuilder) buildIsLastByteAsClosureBitmap(labels []uint8, isLastByte []bool) []uint64 {
	res := make([]uint64, 4)
	for i, b := range isLastByte {
		if b {
			uint256Mark1(res, labels[i])
		}
	}

	return res
}

func (me *_SuRFBuilder) printMem() {
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

	log.Println("count of different bytes:", countOfBytes)
	log.Println("size of builder.lableTree:", SizeOfBytesAsString(countOfBytes))
	log.Println("size of builder.loudsBits:", SizeOfBytesAsString(countOfBytes))
	log.Println("size of builder.suffix:", SizeOfBytesAsString(countOfBytes*4))
	log.Println("size of builder.values:", SizeOfBytesAsString(countOfBytes*8))
	log.Println("size of builder.all:", SizeOfBytesAsString(countOfBytes*14))
	// for i, c := range countOfNodes {
	// 	if c > 0 {
	// 		log.Println(i, "个children的node有", c, "个")
	// 	}
	// }

	// me.display()
}
func (me *_SuRFBuilder) display() {
	for iL, treeFlat := range me.labelsTree {
		log.Println(iL, ":", string(treeFlat), "--", me.hash32OfSuffixes[iL], "--", me.loudsBits[iL])
	}
}

func (me *_SuRFBuilder) build(stringKeys []string, ob map[string]*Value) {
	countOfKeys := len(stringKeys)
	for iKey := 0; iKey < countOfKeys; iKey++ {
		key2Store := []byte(stringKeys[iKey])

		level := me.skipStoredPrefix(key2Store)

		if iKey+1 == countOfKeys {
			me.storeKeyBytesToTrieUntilUnique(key2Store, []uint8{}, level, ob)
		} else {
			me.storeKeyBytesToTrieUntilUnique(key2Store, []byte(stringKeys[iKey+1]), level, ob)
		}

		key2Store = nil
	}

	me.printMem()
}

func (me *_SuRFBuilder) skipStoredPrefix(key []uint8) uint32 {
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

func (me *_SuRFBuilder) isStoredPrefixByte(keyByte uint8, level uint32) bool {
	// 因为保存进来的byte是排好序的,所以只需要与每一层最后一个byte比较就可以了
	if level < me.getTreeHeight() {
		treeFlat := me.labelsTree[level]
		return keyByte == treeFlat[len(treeFlat)-1]
	}

	return false
}

func (me *_SuRFBuilder) storeKeyBytesToTrieUntilUnique(currentKey []uint8, nextKey []uint8, startLevel uint32, ob map[string]*Value) {
	level := startLevel

	lengthOfCurrentKey := uint32(len(currentKey))

	if (level == lengthOfCurrentKey-1) || (level >= uint32(len(nextKey))) || !isSameKey(currentKey[0:level+1], nextKey[0:level+1]) {
		me.storeKeyByte(currentKey[level], true, level, currentKey, ob)
		return
	}
	me.storeKeyByte(currentKey[level], false, level, currentKey, ob)
	level++

	for level < lengthOfCurrentKey {
		if (level == lengthOfCurrentKey-1) || (level >= uint32(len(nextKey))) || !isSameKey(currentKey[0:level+1], nextKey[0:level+1]) {
			me.storeKeyByte(currentKey[level], true, level, currentKey, ob)
			return
		}
		me.storeKeyByte(currentKey[level], false, level, currentKey, ob)
		level++
	}
}

func (me *_SuRFBuilder) storeKeyByte(keyByte uint8, isSuffixByte bool, level uint32, currentKey []uint8, ob map[string]*Value) {
	if level >= me.getTreeHeight() {
		me.addTreeLevel()
	}

	me.labelsTree[level] = append(me.labelsTree[level], keyByte)
	me.loudsBits[level] = append(me.loudsBits[level], 0)
	if isSuffixByte {
		me.hash32OfSuffixes[level] = append(me.hash32OfSuffixes[level], hash32(currentKey))
		me.values[level] = append(me.values[level], ob[string(currentKey)])
	} else {
		me.hash32OfSuffixes[level] = append(me.hash32OfSuffixes[level], 0)
		me.values[level] = append(me.values[level], nil)
	}

	if level > 0 {
		upperFlat := me.loudsBits[level-1]
		upperFlat[len(upperFlat)-1]++
	}
}

func (me *_SuRFBuilder) addTreeLevel() {
	me.labelsTree = append(me.labelsTree, make([]uint8, 0))
	me.loudsBits = append(me.loudsBits, make([]uint8, 0))

	me.hash32OfSuffixes = append(me.hash32OfSuffixes, make([]uint32, 0))
	me.values = append(me.values, make([]*Value, 0))
}

func (me *_SuRFBuilder) getTreeHeight() uint32 {
	return uint32(len(me.labelsTree))
}

func (me *_SuRFBuilder) preferredStartLevelOfSparse() uint32 {
	denseSizeOfEachLevel := make([]uint64, me.getTreeHeight())
	sparseSizeOfEachLevel := make([]uint64, me.getTreeHeight())
	for ic := uint32(0); ic < me.getTreeHeight(); ic++ {
		bytesOfLevel := me.labelsTree[ic]
		var nodesOfLevel []uint8
		if ic == 0 {
			nodesOfLevel = []uint8{uint8(len(me.labelsTree[0]))}
		} else {
			nodesOfLevel = me.loudsBits[ic-1]
		}

		denseSizeOfEachLevel[ic] = me.sizeOfDense(bytesOfLevel, nodesOfLevel)
		sparseSizeOfEachLevel[ic] = me.sizeOfSparse(bytesOfLevel, nodesOfLevel)
	}

	var minSize = ^uint64(0)
	var minStartLevelOfSparse = uint32(0)

	for startLevelOfSparse := uint32(0); startLevelOfSparse < me.getTreeHeight(); startLevelOfSparse++ {
		sizeOfCurrentStartLevelOfSparse := uint64(0)
		for i := uint32(0); i < me.getTreeHeight(); i++ {
			if i < startLevelOfSparse {
				sizeOfCurrentStartLevelOfSparse += denseSizeOfEachLevel[i]
			} else {
				sizeOfCurrentStartLevelOfSparse += sparseSizeOfEachLevel[i]
			}
		}

		log.Println("startLevelOfSparse[", startLevelOfSparse, "]---size[", SizeOfBytesAsString(sizeOfCurrentStartLevelOfSparse), "]")
		if sizeOfCurrentStartLevelOfSparse < minSize {
			minSize = sizeOfCurrentStartLevelOfSparse
			minStartLevelOfSparse = startLevelOfSparse
		}
	}
	log.Println("preferredStartLevelOfSparse:", minStartLevelOfSparse)
	log.Println("size:", SizeOfBytesAsString(minSize))
	return minStartLevelOfSparse
}

// 以字节为单位
func (me *_SuRFBuilder) sizeOfDense(bytesOfLevel []uint8, nodesOfLevel []uint8) uint64 {
	return (uint64(len(nodesOfLevel)) << 5) * 2
}

// 以字节为单位
func (me *_SuRFBuilder) sizeOfSparse(bytesOfLevel []uint8, nodesOfLevel []uint8) uint64 {
	unit := (((uint64(len(bytesOfLevel)) >> 6) + 1) << 3)
	return uint64(len(bytesOfLevel)) + unit*4
}

func isSameKey(leftK []uint8, rightK []uint8) bool {
	if len(leftK) != len(rightK) {
		return false
	}

	for i, v := range leftK {
		if v != rightK[i] {
			return false
		}
	}

	return true
}

func isSameKey64(leftK []uint64, rightK []uint64) bool {
	if len(leftK) != len(rightK) {
		return false
	}

	for i, v := range leftK {
		if v != rightK[i] {
			return false
		}
	}

	return true
}

type _SpeedTest4SuRF struct {
	sf *SuRF
}

func (me *_SpeedTest4SuRF) nameOfProc() string {
	return "surf speed test"
}
func (me *_SpeedTest4SuRF) beforeIterate() {
}
func (me *_SpeedTest4SuRF) proc(lineNo uint64, bytes string) {
	me.sf.Lookup([]byte(bytes))
}

// TestSpeedOfLOUDS test lookup speed
func TestSpeedOfLOUDS(textList []string, _surf *SuRF) {
	proc := &_SpeedTest4SuRF{
		sf: _surf,
	}
	for i := 0; i < 5; i++ { 
		IterateStringList(textList, proc)
	}
}
