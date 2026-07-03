import random
import time
import ws.node as nd
import ws.nodeold as ndo
import sys
import psutil
import os

def generateRandomText():
    fo = open("random.txt", "w")
    str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_~!?@#$%^&*(){}[]"
    lineNo = 0
    maxLine = 1 << 24
    while lineNo < maxLine:
        lineNo = lineNo + 1
        countOfStr = random.randrange(20) + 5
        stringArray2Write = []
        while countOfStr > 0:
            countOfStr = countOfStr - 1
            stringArray2Write.append(random.choice(str))
        stringArray2Write.append("\n")

        fo.write("".join(stringArray2Write))

    fo.close()

def generateRandomText2():
    fo = open("random2.txt", "w")
    str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_~!?@#$%^&*(){}[]"
    lineNo = 0
    maxLine = 1 << 16
    while lineNo < maxLine:
        lineNo = lineNo + 1
        countOfStr = random.randrange(20) + 5
        stringArray2Write = []
        while countOfStr > 0:
            countOfStr = countOfStr - 1
            stringArray2Write.append(random.choice(str))
        stringArray2Write.append("\n")

        for _ in range(1<<8):
            fo.write("".join(stringArray2Write))

    fo.close()

def readRandomText(maxLine):
    start = time.time() * 1000
    fo = open("random.txt", "r")
    lineNo = 0
    while lineNo < maxLine:
        line = fo.readline()
        if len(line) == 0:
            break

        line = line.rstrip()
        lineNo += 1
    
    end = time.time() * 1000
    print("time spent:%d" % (end-start))

def readRandomTextAsDictionary(filename, maxLine):
    start = time.time() * 1000
    fo = open(filename, "r")
    lineNo = 0
    ob = {}
    while lineNo < maxLine:
        line = fo.readline()
        if len(line) == 0:
            break

        line = line.rstrip()

        if line in ob:
            vArray = ob[line]
            vArray.append(lineNo)
        else:
            ob[line] = [lineNo]
        lineNo += 1
    
    end = time.time() * 1000
    print("time spent:%d" % (end-start))

    return ob


    # bytesArray = nodes.readAsBytesArray()
    # for iBytes in bytesArray:
    #     print("%s" % str(bytes(iBytes[:-1]), encoding=encoding))

def readRandomTextAsList(filename, maxLine):
    start = time.time() * 1000
    fo = open(filename, "r")
    lineNo = 0
    theList = []
    while lineNo < maxLine:
        line = fo.readline()
        if len(line) == 0:
            break

        line = line.rstrip()

        found = False
        for i in range(len(theList)):
            if theList[i][0] == line:
                theList[i][1].append(lineNo)
                found = True
                break
        if found == False:
            theList.append((line, [lineNo]))
        
        lineNo += 1
    
    end = time.time() * 1000
    print("time spent:%d" % (end-start))

    return theList

def testSimpleFiles():
    ndo.readRandomTextAsNodes("r0.txt", 100, "utf-8")
    ndo.readRandomTextAsNodes("r1.txt", 100, "utf-8")
    ndo.readRandomTextAsNodes("r2.txt", 100, "utf-8")
    ndo.readRandomTextAsNodes("r3.txt", 100, "utf-8")
    ndo.readRandomTextAsNodes("r4.txt", 100, "utf-8")
    ndo.readRandomTextAsNodes("r5.txt", 100, "utf-8")

def testCorrectionOfNodes():
    maxLine = 1<<10
    encoding = "utf-8"
    filename = "random.txt"
    nodes = ndo.readRandomTextAsNodes(filename, maxLine, "utf-8")
    fo = open(filename, "r")
    lineNo = 0
    while lineNo < maxLine:
        line = fo.readline()
        if len(line) == 0:
            break

        line = line.rstrip()

        lineAsBytes = bytes(line, encoding=encoding)

        values = nodes.getValueByKey(lineAsBytes)
        assert(lineNo in values)

        lineNo += 1

def testReadRandomTextAsNodesThenOutput():
    nodes = ndo.readRandomTextAsNodes("random.txt", 1<<1, "utf-8")
    bytesArray = nodes.readAsBytesArray()
    for i in range(len(bytesArray)):
        print(str(bytes(bytesArray[i][:-1]), encoding="utf-8"))

def testEncoding():
    ndo.readRandomTextAsNodes("r6.txt", 100, "GBK")

def testReadLouds():
    louds = nd.readRandomTextAsTree("pctest1.txt", 100, "utf-8").asLOUDS()
    louds.iterateItems()

def testParentAndChildNode1():
    louds = nd.readRandomTextAsTree("pctest1.txt", 100, "utf-8").asLOUDS()

    assert(len(louds.nodes) == 12)

    louds.nodes[1].assertEquals(1<<b'a'[0], None)
    louds.nodes[2].assertEquals(1<<b'b'[0] | 1<<b'c'[0] | 1<<b'd'[0], [3])
    louds.nodes[3].assertEquals(1<<b'c'[0] | 1<<b's'[0] | 1<<b't'[0], [0])
    louds.nodes[4].assertEquals(1<<b'c'[0], [1])
    louds.nodes[5].assertEquals(0, [2,8])
    louds.nodes[6].assertEquals(1<<b'd'[0], None)
    louds.nodes[7].assertEquals(0, [6])
    louds.nodes[8].assertEquals(1<<b'w'[0], None)
    louds.nodes[9].assertEquals(0, [4])
    louds.nodes[10].assertEquals(0, [5])
    louds.nodes[11].assertEquals(0, [7])

    assert(louds.parentNode(1) == louds.nodes[0])
    assert(louds.parentNode(2) == louds.nodes[1])
    assert(louds.parentNode(3) == louds.nodes[2])
    assert(louds.parentNode(4) == louds.nodes[2])
    assert(louds.parentNode(5) == louds.nodes[2])
    assert(louds.parentNode(6) == louds.nodes[3])
    assert(louds.parentNode(7) == louds.nodes[3])
    assert(louds.parentNode(8) == louds.nodes[3])
    assert(louds.parentNode(9) == louds.nodes[4])
    assert(louds.parentNode(10) == louds.nodes[6])
    assert(louds.parentNode(11) == louds.nodes[8])

    assert(louds.firstChildNode(0) == louds.nodes[1])
    assert(louds.firstChildNode(1) == louds.nodes[2])
    assert(louds.firstChildNode(2) == louds.nodes[3])
    assert(louds.firstChildNode(3) == louds.nodes[6])
    assert(louds.firstChildNode(4) == louds.nodes[9])
    # assert(louds.firstChildNode(5) == None)
    assert(louds.firstChildNode(6) == louds.nodes[10])
    # assert(louds.firstChildNode(7) == None)
    assert(louds.firstChildNode(8) == louds.nodes[11])
    # assert(louds.firstChildNode(9) == None)
    # assert(louds.firstChildNode(10) == None)
    # assert(louds.firstChildNode(11) == None)

    assert(louds.lastChildNode(0) == louds.nodes[1])
    assert(louds.lastChildNode(1) == louds.nodes[2])
    assert(louds.lastChildNode(2) == louds.nodes[5])
    assert(louds.lastChildNode(3) == louds.nodes[8])
    assert(louds.lastChildNode(4) == louds.nodes[9])
    # assert(louds.lastChildNode(5) == None)
    assert(louds.lastChildNode(6) == louds.nodes[10])
    # assert(louds.lastChildNode(7) == None)
    assert(louds.lastChildNode(8) == louds.nodes[11])
    # assert(louds.lastChildNode(9) == None)
    # assert(louds.lastChildNode(10) == None)
    # assert(louds.lastChildNode(11) == None)

def testParentAndChildNode2():
    louds = nd.readRandomTextAsTree("pctest2.txt", 100, "utf-8").asLOUDS()

    assert(len(louds.nodes) == 14)

    louds.nodes[1].assertEquals(1<<b'A'[0] | 1<<b'a'[0], None)
    louds.nodes[2].assertEquals(1<<b'K'[0], [0])
    louds.nodes[3].assertEquals(1<<b'b'[0] | 1<<b'c'[0] | 1<<b'd'[0], [4])
    louds.nodes[4].assertEquals(0, [7])
    louds.nodes[5].assertEquals(1<<b'c'[0] | 1<<b's'[0] | 1<<b't'[0], [1])
    louds.nodes[6].assertEquals(1<<b'c'[0], [2])
    louds.nodes[7].assertEquals(0, [3,10])
    louds.nodes[8].assertEquals(1<<b'd'[0], None)
    louds.nodes[9].assertEquals(0, [8])
    louds.nodes[10].assertEquals(1<<b'w'[0], None)
    louds.nodes[11].assertEquals(0, [5])
    louds.nodes[12].assertEquals(0, [6])
    louds.nodes[13].assertEquals(0, [9])

    assert(louds.parentNode(1) == louds.nodes[0])
    assert(louds.parentNode(2) == louds.nodes[1])
    assert(louds.parentNode(3) == louds.nodes[1])
    assert(louds.parentNode(4) == louds.nodes[2])
    assert(louds.parentNode(5) == louds.nodes[3])
    assert(louds.parentNode(6) == louds.nodes[3])
    assert(louds.parentNode(7) == louds.nodes[3])
    assert(louds.parentNode(8) == louds.nodes[5])
    assert(louds.parentNode(9) == louds.nodes[5])
    assert(louds.parentNode(10) == louds.nodes[5])
    assert(louds.parentNode(11) == louds.nodes[6])
    assert(louds.parentNode(12) == louds.nodes[8])
    assert(louds.parentNode(13) == louds.nodes[10])

    assert(louds.firstChildNode(0) == louds.nodes[1])
    assert(louds.firstChildNode(1) == louds.nodes[2])
    assert(louds.firstChildNode(2) == louds.nodes[4])
    assert(louds.firstChildNode(3) == louds.nodes[5])
    # assert(louds.firstChildNode(4) == louds.nodes[9])
    assert(louds.firstChildNode(5) == louds.nodes[8])
    assert(louds.firstChildNode(6) == louds.nodes[11])
    # assert(louds.firstChildNode(7) == None)
    assert(louds.firstChildNode(8) == louds.nodes[12])
    # assert(louds.firstChildNode(9) == None)
    assert(louds.firstChildNode(10) == louds.nodes[13])
    # assert(louds.firstChildNode(11) == None)
    # assert(louds.firstChildNode(12) == None)
    # assert(louds.firstChildNode(13) == None)

    assert(louds.lastChildNode(0) == louds.nodes[1])
    assert(louds.lastChildNode(1) == louds.nodes[3])
    assert(louds.lastChildNode(2) == louds.nodes[4])
    assert(louds.lastChildNode(3) == louds.nodes[7])
    # assert(louds.lastChildNode(4) == louds.nodes[9])
    assert(louds.lastChildNode(5) == louds.nodes[10])
    assert(louds.lastChildNode(6) == louds.nodes[11])
    # assert(louds.lastChildNode(7) == None)
    assert(louds.lastChildNode(8) == louds.nodes[12])
    # assert(louds.lastChildNode(9) == None)
    assert(louds.lastChildNode(10) == louds.nodes[13])
    # assert(louds.lastChildNode(11) == None)
    # assert(louds.lastChildNode(12) == None)
    # assert(louds.lastChildNode(13) == None)

def testKeyAndValues():
    ob = readRandomTextAsDictionary("random2.txt", 1<<18)
    louds = nd.readRandomTextAsTree("random2.txt", 1<<18, "utf-8").asLOUDS()
    louds.assertEquals(ob, "utf-8")

def compareSpeedOfLookup(filename, maxLine, encoding):
    ob = readRandomTextAsDictionary(filename, maxLine)
    louds = nd.readRandomTextAsTree(filename, maxLine, encoding).asLOUDS()

    start = time.time() * 1000

    print("louds读取测试开始%s" % filename)

    fo = open(filename, "r")
    lineNo = 0
    while lineNo < maxLine:
        line = fo.readline()
        if len(line) == 0:
            break

        line = line.rstrip()

        lineAsBytes = bytes(line, encoding=encoding)
        vLouds = louds.lookupValue(lineAsBytes)
        assert(lineNo in vLouds)

        lineNo += 1

    print("time spent:%d" % (time.time() * 1000-start))


    start = time.time() * 1000

    print("ob读取测试开始%s" % filename)

    fo = open(filename, "r")
    lineNo = 0
    while lineNo < maxLine:
        line = fo.readline()
        if len(line) == 0:
            break

        line = line.rstrip()
        vOb = ob[line]
        assert(lineNo in vOb)

        lineNo += 1

    print("time spent:%d" % (time.time() * 1000-start))


def __sizeOfBytesAsString(number):
    unit = "B"
    if number > 1024:
        number = number / 1024
        unit = "K"
        if number > 1024:
            number = number / 1024
            unit = "M"
            if number > 1024:
                number = number / 1024
                unit = "G"

    return "{:.2f}{}".format(number, unit)

def __checkMemory():
    info = psutil.virtual_memory()
    print(u'内存使用：',__sizeOfBytesAsString(psutil.Process(os.getpid()).memory_info().rss))
    print(u'总内存：',__sizeOfBytesAsString(info.total))
    print(u'内存占比：',info.percent)
    print(u'cpu个数：',psutil.cpu_count())

def __onesPosition2(number):
    res = []
    checkPos = 0
    checkNumber = number
    while checkNumber != 0:
        if checkNumber & 1:
            res.append(checkPos)
        checkPos += 1
        checkNumber >>= 1

def __onesPosition(number):
    res = []
    for i, x in enumerate(list(bin(number)[:1:-1])):
            if x == '1':
                res.append(i)

def testOnesPosition():
    start = time.time() * 1000
    number = 0
    for pi in range(0x100):
        number |= 1<<pi

    for _ in range(0x10000):

        __onesPosition(number)

    end = time.time() * 1000
    print("time spent:%d" % (end-start))


if __name__ == "__main__":
    # generateRandomText2()
    # testOnesPosition()
    # readRandomText(1<<18)
    # theList = readRandomTextAsList("random.txt", 1<<16)

    # ob = readRandomTextAsDictionary("random.txt", 1<<24)
    # obSize = sys.getsizeof(ob)
    # for k, v in ob.items():
    #     obSize += len(k)
    # print(__sizeOfBytesAsString(obSize))

    louds = nd.readRandomTextAsTree("random.txt", 1<<16, "utf-8").asLOUDS()
    # print(u'louds的大小：',__sizeOfBytesAsString(louds.memorySize()))

    # testReadLouds()
    
    # nd.readRandomTextAsLOUDS("r0.txt", 100, "utf-8")
    # testEncoding()
    # testSimpleFiles()
    # testTree()
    # testCorrectionOfNodes()
    # testReadRandomTextAsNodesThenOutput()
    # nd.testPopcount()

    # testParentAndChildNode1()
    # testParentAndChildNode2()

    # testKeyAndValues()

    # compareSpeedOfLookup("random.txt", 1<<16, "utf-8")
    # time spent:67
    # 正在读取文件random.txt
    # time spent:11738
    # count of tree nodes:817762
    # time spent:36335
    # louds读取测试开始random.txt
    # time spent:7566
    # ob读取测试开始random.txt
    # time spent:45

# 看一下random.txt里面的文字能不能全部读出来
# 看一下random.txt里面文字对应的行号读出来对不对
# 对比ob的读与louds的读，看看速度对比如何
# 把DenseNode最后那一层只有$的Node想办法去掉
# 把大部分的DenseNode换成SparseNode
# 能不能不要先构建TreeNode再生成LOUDS
# 自己写完之后，去看看人家写的我自己电脑的Git/SuRF目录下面
