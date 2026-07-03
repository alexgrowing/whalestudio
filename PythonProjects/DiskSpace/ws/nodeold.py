import time

class Nodes:
    def __init__(self):
        pseudoRoot = Node()
        pseudoRoot.numberOf1 = 1
        self.nodes = [pseudoRoot] + [Node()]
        self.lookupTable = [1, 1]

    def rank1(self, number):
        countOf1 = 0
        for i in range(len(self.nodes)):
            iLUT = self.lookupTable[i]
            iPreviousLUT = 0
            if i > 0:
                iPreviousLUT = self.lookupTable[i - 1]

            if number < iLUT:
                countOf1 += (number - iPreviousLUT)
                break
            elif number == iLUT:
                countOf1 += (iLUT - iPreviousLUT)
                break
            else:
                countOf1 += (iLUT - iPreviousLUT)

        return countOf1


    def select1(self, number):
        if number == 0:
            return None

        countOf1 = 0
        for i in range(len(self.nodes)):
            iLUT = self.lookupTable[i]
            iPreviousLUT = 0
            if i > 0:
                iPreviousLUT = self.lookupTable[i - 1]

            countOf1 += (iLUT - iPreviousLUT)
            if countOf1 < number:
                pass
            elif countOf1 == number:
                return iLUT - 1
            else:
                return iLUT - 1 - (countOf1 - number)

        return None

    def rank0(self, number):
        countOf0 = 0
        for i in range(len(self.nodes)):
            iLUT = self.lookupTable[i]
            # iPreviousLUT = 0
            # if i > 0:
            #     iPreviousLUT = self.lookupTable[i - 1]

            if number < iLUT:
                break
            if number == iLUT:
                countOf0 += 1
                break
            else:
                countOf0 += 1

        return countOf0

    def select0(self, number):
        if number == 0:
            return None

        countOf0 = 0
        for i in range(len(self.nodes)):
            iLUT = self.lookupTable[i]
            # iPreviousLUT = 0
            # if i > 0:
            #     iPreviousLUT = self.lookupTable[i - 1]
            countOf0 += 1
            if countOf0 < number:
                pass
            else:
                return iLUT

        return None

    def firstChild(self, indexOfNode):
        return self.nodes[self.rank1(self.select0(indexOfNode) + 1)]

    def lastChild(self, indexOfNode):
        return self.nodes[self.rank1(self.select0(indexOfNode + 1) - 1)]

    def parent(self, indexOfNode):
        return self.nodes[self.rank0(self.select1(indexOfNode))]

    def children(self, indexOfNode):
        return (self.select0(indexOfNode + 1) - 1) - (self.select0(indexOfNode) + 1) + 1

    def indexOfChild(self, indexOfNode, num):
        return self.rank1(self.select0(indexOfNode) + 1 + num)

    def insertNodeByIndex(self, indexOfNode):
        self.nodes.insert(indexOfNode, Node())
        self.lookupTable.insert(indexOfNode, self.lookupTable[indexOfNode-1])

    def setValueByNodeIndex(self, indexOfNode, value):
        self.nodes[indexOfNode].saveValue(value)

    def markLabelBMapByNodeIndex(self, indexOfNode, byte):
        self.nodes[indexOfNode].markLabelBMap(byte)
    
    def markHasChildBMapByNodeIndex(self, indexOfNode, byte):
        isChildNodeExist, childIndex = self.nodes[indexOfNode].markHasChildBMap(byte)
        if isChildNodeExist == False:
            for i in range(indexOfNode, len(self.nodes)):
                self.lookupTable[i] += 1

        nodeIndexOfChild = self.indexOfChild(indexOfNode, childIndex)
        if isChildNodeExist == False:
            self.insertNodeByIndex(nodeIndexOfChild)

        return nodeIndexOfChild

    def readAsBytesArray(self):
        return self.nodes[1].readFromNodes(self, 1)

    def getValueByKey(self, keyBytes):
        lengthOfBytes = len(keyBytes)
        nodeIndex2Lookup = 1
        for i in range(lengthOfBytes):
            byte = keyBytes[i]
            childExist, childIndex = self.nodes[nodeIndex2Lookup].childIndex(byte)
            if childExist == False:
                return None
            
            nodeIndex2Lookup = self.indexOfChild(nodeIndex2Lookup, childIndex)

        return self.nodes[nodeIndex2Lookup].values

class Node:
    def __init__(self):
        self.labelBMap = self.hasChildBMap = 0
        self.values = []

    def saveValue(self, v):
        self.markLabelBMap(0xFF)
        self.values.append(v)

    def markLabelBMap(self, byte):
        self.labelBMap = self.labelBMap | (1 << byte)

    def markHasChildBMap(self, byte):
        childExist, childIndex = self.childIndex(byte)
        if childExist == False:
            self.hasChildBMap = self.hasChildBMap | (1<<byte)

        return (childExist, childIndex)

    def childIndex(self, byte):
        childIndex = 0
        childExist = False
        for i in range(byte + 1):
            if i == byte:
                if self.hasChildBMap & (1<<i):
                    childExist = True
            elif self.hasChildBMap & (1<<i):
                childIndex += 1

        return (childExist, childIndex)

    def childIndexPop(self, byte):
        childExist = (self.hasChildBMap & (1<<byte) > 0)
        childIndex = popcount(self.hasChildBMap<<(0x100 - byte) & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)

        return (childExist, childIndex)

    def readFromNodes(self, nodes:Nodes, currentIndex:int):
        bytesInNode = []
        for i in range(1<<8):
            if(1<<i)&self.labelBMap:
                bytesInNode.append(i)

        fullBytesArray = []
        for i in range(len(bytesInNode)):
            ib = bytesInNode[i]
            if ib == 0xFF:
                fullBytes = [ib]
                fullBytesArray.append(fullBytes)
            else:
                childIndex = nodes.indexOfChild(currentIndex, i)
                iChildNode = nodes.nodes[childIndex]
                childBytesArray = iChildNode.readFromNodes(nodes, childIndex)

                for ic in range(len(childBytesArray)):
                    childBytes = childBytesArray[ic]
                    childBytes.insert(0, ib)
                    fullBytesArray.append(childBytes)

        return fullBytesArray


def readRandomTextAsNodes(filename, maxLine, encoding):
    start = time.time() * 1000

    print("正在读取文件%s" % filename)

    fo = open(filename, "r")
    lineNo = 0
    nodes = Nodes()
    while lineNo < maxLine:
        line = fo.readline()
        if len(line) == 0:
            break

        line = line.rstrip()

        lineAsBytes = bytes(line, encoding=encoding)
        lengthOfBytes = len(lineAsBytes)
        
        nodeIndex2FillByte = 1
        for i in range(lengthOfBytes + 1):
            if i == lengthOfBytes:
                nodes.setValueByNodeIndex(nodeIndex2FillByte, lineNo)
            else:
                byte = lineAsBytes[i]
                nodes.markLabelBMapByNodeIndex(nodeIndex2FillByte, byte)

                nodeIndex2FillByte = nodes.markHasChildBMapByNodeIndex(nodeIndex2FillByte, byte)

        lineNo += 1

    end = time.time() * 1000
    print("time spent:%d" % (end-start))
    return nodes

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

def popcount(number):
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