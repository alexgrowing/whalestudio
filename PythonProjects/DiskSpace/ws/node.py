import time
import sys

class DenseNode:
    countOfDenseNode = 0

    def __init__(self):
        DenseNode.countOfDenseNode += 1

        # self.__labelBitMap = 0
        self.__hasChildBitMap = 0
        self.__hasValueBitMap = 0
        # self.__prefixValue = None
        self.values = [] #就可以是一个简单的list嘛，每个bit根据hasChildMap的位置，就知道是这个values数组的第几个
        # self.simpleView = []

    def memorySize(self):
        # s1 = sys.getsizeof(self.__hasChildBitMap)
        # s2= sys.getsizeof(self.__hasValueBitMap)
        # s3 = sys.getsizeof(self.values)
        # print("dense:%d - %d - %d - %s" % (s1, s2, s3, self.values))
        # return s1 + s2 + s3

        return 32 + 32 + 8

    # def markPrefixValue(self, v):
    #     self.__prefixValue = v

    def markByTreeNode(self, treeNode, childNodes4NextLevel):
        for i, x in enumerate(list(bin(treeNode.labelBitMap)[:1:-1])):
            if x == '1':
                self.__denseMark(treeNode, i, childNodes4NextLevel)

    def __denseMark(self, treeNode, i, childNodes4NextLevel):
        pos = 1<<i
        iValue = None
        iSub = None
        if treeNode.values != None:
            iValue = treeNode.values[i]
        if treeNode.subs != None:
            iSub = treeNode.subs[i]

        if iSub != None:
            self.__hasChildBitMap |= pos
            childNodes4NextLevel.append(iSub)

        if iValue != None:
            self.__hasValueBitMap |= pos
            self.values.append(iValue)

    def readAll(self, louds, currentIndex, prefixBytes):
        # if self.__prefixValue != None:
        #     print("%s=>%s" % (str(bytes(prefixBytes), encoding="utf-8"), self.__prefixValue))
        indexOfChild = 0
        indexOfValues = 0
        for i in range(0x100):
            pos = 1<<i
            if self.__hasValueBitMap & pos:
                newBytes = prefixBytes.copy()
                newBytes.append(i)
                print("%s=>%s" % (str(bytes(newBytes), encoding="utf-8"), self.values[indexOfValues]))

                indexOfValues += 1
            if self.__hasChildBitMap & pos:
                indexOfChildNode = louds.childNodeByIndex(currentIndex, indexOfChild)
                newBytes = prefixBytes.copy()
                newBytes.append(i)
                louds.nodes[indexOfChildNode].readAll(louds, indexOfChildNode, newBytes)

                indexOfChild += 1

    def lookupValue(self, louds, currentIndex, _byte, _suffixBytes):
        if len(_suffixBytes) == 0:
            if self.__hasValueBitMap & (1<<_byte):
                indexOfValues = popcount(self.__hasValueBitMap<<(0x100-_byte))
                return self.values[indexOfValues]
        elif self.__hasChildBitMap & (1<<_byte):
            indexOfChild = popcount(self.__hasChildBitMap<<(0x100-_byte))
            indexOfChildNode = louds.childNodeByIndex(currentIndex, indexOfChild)
            childNode = louds.nodes[indexOfChildNode]

            return childNode.lookupValue(louds, indexOfChildNode, _suffixBytes[0], _suffixBytes[1:])

        return None

    def assertEquals(self, aHasChildBitMap, aHasValueBitMap, aValues):
        if self.values == None:
            assert(aValues == None)
        else:
            assert(len(self.values) == len(aValues))
            for i in range(len(self.values)):
                assert(self.values[i] == aValues[i])

        assert(self.__hasChildBitMap == aHasChildBitMap)
        assert(self.__hasValueBitMap == aHasValueBitMap)

class SparseNode:
    countOfSparseNode = 0

    def __init__(self):
        SparseNode.countOfSparseNode += 1

        self.__lables = []
        self.__hasChildBitMap = 0
        self.__values = []

    def markByTreeNode(self, treeNode, childNodes4NextLevel):
        # checkPos = 0
        # checkNumber = treeNode.labelBitMap
        # while checkNumber != 0:
        #     if checkNumber & 1:
        #         self.__sparseMark(treeNode, checkPos, childNodes4NextLevel)
        #     checkPos += 1
        #     checkNumber >>= 1

        for i, x in enumerate(list(bin(treeNode.labelBitMap)[:1:-1])):
            if x == '1':
                self.__sparseMark(treeNode, i, childNodes4NextLevel)
                # iValue = None
                # iSub = None
                # if treeNode.values != None:
                #     iValue = treeNode.values[i]
                # if treeNode.subs != None:
                #     iSub = treeNode.subs[i]

                # self.__values.append(iValue)

                # if iSub != None:
                #     self.__hasChildBitMap |= 1<<len(self.__lables)
                #     childNodes4NextLevel.append(iSub)

                # self.__lables.append(i)

    def __sparseMark(self, treeNode, i, childNodes4NextLevel):
        iValue = None
        iSub = None
        if treeNode.values != None:
            iValue = treeNode.values[i]
        if treeNode.subs != None:
            iSub = treeNode.subs[i]

        self.__values.append(iValue)

        if iSub != None:
            self.__hasChildBitMap |= 1<<len(self.__lables)
            childNodes4NextLevel.append(iSub)

        self.__lables.append(i)

    def memorySize(self):
        # s1 = sys.getsizeof(self.__lables)
        # s2 = sys.getsizeof(self.__hasChildBitMap)
        # s3 = sys.getsizeof(self.__values)
        # print("sparse:%d - %d - %d - %s" % (s1, s2, s3, self.__values))
        # return s1 + s2 + s3

        return (len(self.__lables) << 3) + sys.getsizeof(self.__hasChildBitMap) + 8

    def readAll(self, louds, currentIndex, prefixBytes):
        for i in range(len(self.__lables)):
            labelByte = self.__lables[i]

            if self.__values[i] != None:
                newBytes = prefixBytes.copy()
                newBytes.append(labelByte)
                print("%s=>%s" % (str(bytes(newBytes), encoding="utf-8"), self.__values[i]))
            
            if self.__hasChildBitMap & (1<<i):
                indexOfChildNode = louds.childNodeByIndex(currentIndex, i)
                newBytes = prefixBytes.copy()
                newBytes.append(labelByte)
                louds.nodes[indexOfChildNode].readAll(louds, indexOfChildNode, newBytes)

    def lookupValue(self, louds, currentIndex, _byte, _suffixBytes):
        indexOfByte = -1
        for i in range(len(self.__lables)):
            if self.__lables[i] == _byte:
                indexOfByte = i
                break
        
        if indexOfByte == -1:
            return None

        if len(_suffixBytes) == 0:
            return self.__values[indexOfByte]
        elif self.__hasChildBitMap & (1<<indexOfByte):
            indexOfChildNode = louds.childNodeByIndex(currentIndex, indexOfByte)
            childNode = louds.nodes[indexOfChildNode]

            return childNode.lookupValue(louds, indexOfChildNode, _suffixBytes[0], _suffixBytes[1:])

        return None


class LOUDS:
    def __init__(self):
        self.nodes = [None]

        self.lookupTable4Child = []
        self.lookupTable4Parent = [-1]

    def assertEquals(self, ob, encoding):
        for key, v in ob.items():
            keyAsBytes = bytes(key, encoding=encoding)
            vLouds = self.lookupValue(keyAsBytes)
            assert(v == vLouds)

    def memorySize(self):
        size = sys.getsizeof(self.lookupTable4Child) + sys.getsizeof(self.lookupTable4Parent) + sys.getsizeof(self.nodes)
        for i in range(len(self.nodes)):
            if self.nodes[i] != None:
                size += self.nodes[i].memorySize()

        return size
        
    def lookupValue(self, keyAsBytes):
        if len(keyAsBytes) == 0:
            return None

        return self.nodes[1].lookupValue(self, 1, keyAsBytes[0], keyAsBytes[1:])

    def iterateItems(self):
        self.nodes[1].readAll(self, 1, [])

    def readTreeNodesByLevel(self, arrayOfPATN):
        if len(arrayOfPATN) == 0:
            return
        nextArrayOfPATN = []
        for i in range(len(arrayOfPATN)):
            patn = arrayOfPATN[i]
            self.__readTreeNodes(patn.treeNodes, patn.parentIndex, nextArrayOfPATN)

        self.readTreeNodesByLevel(nextArrayOfPATN)

    def __readTreeNodes(self, treeNodes, parentIndexOfTreeNodes, nextArrayOfPATN):
        self.lookupTable4Child.append(len(self.lookupTable4Parent))
        if len(treeNodes) == 0:
            return

        for it in range(len(treeNodes)):
            iNode = treeNodes[it]

            # denseNode = DenseNode()
            loudsNode = None
            if popcount(iNode.labelBitMap) >= 2:
                loudsNode = DenseNode()
            else:
                loudsNode = SparseNode()

            self.nodes.append(loudsNode)
            self.lookupTable4Parent.append(parentIndexOfTreeNodes)

            indexOfCurrentNode = len(self.nodes) - 1
            temp = ParentAndTreeNodes(indexOfCurrentNode, [])
            nextArrayOfPATN.append(temp)

            loudsNode.markByTreeNode(iNode, temp.treeNodes)

    def firstChildNode(self, nodeIndex):
        return self.lookupTable4Child[nodeIndex]

    def lastChildNode(self, nodeIndex):
        return self.lookupTable4Child[nodeIndex + 1] -1

    def parentNode(self, nodeIndex):
        return self.lookupTable4Parent[nodeIndex]

    def childNodeByIndex(self, nodeIndex, childIndex):
        return self.lookupTable4Child[nodeIndex] + childIndex

class ParentAndTreeNodes:
    def __init__(self, _parentIndex, _treeNodes):
        self.parentIndex = _parentIndex
        self.treeNodes = _treeNodes
        
class TreeNode:
    def __init__(self):
        self.labelBitMap = 0
        self.subs = None
        self.values = None

    def markByte(self, index):
        if self.subs == None:
            self.subs = [None] * 0x100

        if self.subs[index] == None:
            self.subs[index] = TreeNode()
            self.labelBitMap |= 1<<index

        return self.subs[index]

    def markValue(self, index, value):
        if self.values == None:
            self.values = [None] * 0x100

        if self.values[index] == None:
            self.values[index] = []
            self.labelBitMap |= 1<<index

        self.values[index].append(value)

    def asLOUDS(self):
        start = time.time() * 1000

        louds = LOUDS()
        louds.readTreeNodesByLevel([ParentAndTreeNodes(0, [self])])
        print("build LOUDS time spent:%d" % (time.time() * 1000-start))
        print("DenseNode.size=%d, SparseNode.size=%d" % (DenseNode.countOfDenseNode, SparseNode.countOfSparseNode))

        return louds


def readRandomTextAsTree(filename, maxLine, encoding):
    start = time.time() * 1000

    print("正在读取文件%s" % filename)

    fo = open(filename, "r")
    lineNo = 0
    root = TreeNode()
    while lineNo < maxLine:
        line = fo.readline()
        if len(line) == 0:
            break

        line = line.rstrip()

        lineAsBytes = bytes(line, encoding=encoding)
        lengthOfBytes = len(lineAsBytes)
        
        nextTreeNode = root
        for i in range(lengthOfBytes):
            if i == lengthOfBytes - 1:
                nextTreeNode.markValue(lineAsBytes[i], lineNo)
            else:
                nextTreeNode = nextTreeNode.markByte(lineAsBytes[i])

        lineNo += 1

    print("build Tree time spent:%d" % (time.time() * 1000-start))
    return root
    # louds = root.asLOUDS()
    # print("time spent:%d" % (time.time() * 1000-start))
    # return root

__popcount_tab = [
    0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8,
]

def popcountTable(number):
    res = 0
    while number != 0:
        res += __popcount_tab[number & 0xFF]

        number = number >> 8

    return res

    # return __popcount_tab[(number >> 0) & 0xFF] + __popcount_tab[(number >> 8) & 0xFF]\
    # + __popcount_tab[(number >> 16) & 0xFF] + __popcount_tab[(number >> 24) & 0xFF]\
    # + __popcount_tab[(number >> 32) & 0xFF] + __popcount_tab[(number >> 40) & 0xFF]\
    # + __popcount_tab[(number >> 48) & 0xFF] + __popcount_tab[(number >> 56) & 0xFF]\
    # + __popcount_tab[(number >> 64) & 0xFF] + __popcount_tab[(number >> 72) & 0xFF]\
    # + __popcount_tab[(number >> 80) & 0xFF] + __popcount_tab[(number >> 88) & 0xFF]\
    # + __popcount_tab[(number >> 96) & 0xFF] + __popcount_tab[(number >> 104) & 0xFF]\
    # + __popcount_tab[(number >> 112) & 0xFF] + __popcount_tab[(number >> 120) & 0xFF]\
    # + __popcount_tab[(number >> 128) & 0xFF] + __popcount_tab[(number >> 136) & 0xFF]\
    # + __popcount_tab[(number >> 144) & 0xFF] + __popcount_tab[(number >> 152) & 0xFF]\
    # + __popcount_tab[(number >> 160) & 0xFF] + __popcount_tab[(number >> 168) & 0xFF]\
    # + __popcount_tab[(number >> 176) & 0xFF] + __popcount_tab[(number >> 184) & 0xFF]\
    # + __popcount_tab[(number >> 192) & 0xFF] + __popcount_tab[(number >> 200) & 0xFF]\
    # + __popcount_tab[(number >> 208) & 0xFF] + __popcount_tab[(number >> 216) & 0xFF]\
    # + __popcount_tab[(number >> 224) & 0xFF] + __popcount_tab[(number >> 232) & 0xFF]\
    # + __popcount_tab[(number >> 240) & 0xFF] + __popcount_tab[(number >> 248) & 0xFF]\

def popcount(x):
    return __popcount128(x & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF) + __popcount128(x >> 128)

def __popcount64(x):
    return __popcount32(x & 0xFFFFFFFF) + __popcount32(x >> 32)

def __popcount128(x):
    return __popcount64(x & 0xFFFFFFFFFFFFFFFF) + __popcount64(x >> 64)

def __popcount32(x):
    x -= (x >> 1) & 0x55555555
    x = (x & 0x33333333) + ((x >> 2) & 0x33333333)
    x = (x + (x >> 4)) & 0x0F0F0F0F
    x += x >> 8
    return (x + (x >> 16)) & 0x3F


def testPopcount():
    assert(popcount(0x01) == 1)
    assert(popcount(0x07) == 3)
    assert(popcount(0xFF) == 8)
    assert(popcount(0xFE) == 7)
    assert(popcount(0xFFFE) == 15)
    assert(popcount(0xFFFE) == 15)
    assert(popcount(0xFFFEFF) == 23)
    assert(popcount(0xFFFEFF07) == 26)
    assert(popcount(0xFFFEFF70) == 26)
    assert(popcount(0xFFFEFFFEFF70FF70) == 52)
    assert(popcount(0xFFFFFEFFFEFF70FF70FEFFFEFF70FF70) == 104)
    assert(popcount(0xFFFFFEFFFEFF70FF70FEFFFEFF70FF7006) == 106)