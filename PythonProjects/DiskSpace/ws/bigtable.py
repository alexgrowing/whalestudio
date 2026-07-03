import time

class BigTable:
    def __init__(self):
        self.table = []
        for _ in range(0xFFFF):
            self.table.append(BigCell())

    def mark(self, key, lineNo):
        for ci in range(len(key)):
            decodedBytes = bytes(key[ci], "GBK")
            if len(decodedBytes) == 1:
                self.__mark(decodedBytes[0], lineNo, ci)
            else:
                self.__mark((decodedBytes[0]<<8) + decodedBytes[1], lineNo, ci)


    def __mark(self, byte, lineNo, charIndex):
        bigCell = self.table[byte]
        bigCell.mark(lineNo, charIndex)


class BigCell:
    def __init__(self):
        self.arrayOfLines = []

    def mark(self, lineNo, charIndex):
        while charIndex >= len(self.arrayOfLines):
            self.arrayOfLines.append(Lines())

        lines = self.arrayOfLines[charIndex]
        lines.mark(lineNo)

class Lines:
    def __init__(self):
        self.numbers = []

    def mark(self, lineNo):
        self.numbers.append(lineNo)


def readRandomTextAsBigTable(maxLine):
    start = time.time() * 1000
    fo = open("random.txt", "r")
    lineNo = 0
    table = BigTable()
    while lineNo < maxLine:
        line = fo.readline()
        if len(line) == 0:
            break

        line = line.rstrip()
        table.mark(line, lineNo)

        lineNo += 1
    
    end = time.time() * 1000
    print("time spent:%d" % (end-start))

    return table

def testCorrection():
    pass

if __name__ == "__main__":
    array = BigTable().table
    array[0].append("abc")
    print(array[0])
    print(array[1])