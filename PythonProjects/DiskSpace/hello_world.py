import os
        
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

def printFiles(files, writer):
    for f in files:
        writer.write("%s - %s\n" % (f[0], __sizeOfBytesAsString(f[1])))

def findTopNFiles(directory, number):
    ob = {'count_of_files':0, 'seats':[]}

    if os.path.isdir(directory) == False:
        return ob

    checkFilesUnderDir(directory, ob, number)
    return ob

def checkSizeOfFile(file, ob, topN):
    ob['count_of_files'] = ob['count_of_files'] + 1
    if ob['count_of_files'] % topN == 0:
        print("%d:%s" % (ob['count_of_files'], file))
    sizeOfFile = os.path.getsize(file)

    index = len(ob['seats']) - 1
    
    while index >= 0:
        if ob['seats'][index][1] > sizeOfFile:
            break
        index = index - 1

    if index + 1 < topN:
        ob['seats'].insert(index + 1, (file, sizeOfFile))

    if len(ob['seats']) > topN:
        popedFile = ob['seats'].pop()
        print("pop:%s - %s" % (__sizeOfBytesAsString(popedFile[1]), popedFile[0]))

def checkFilesUnderDir(directory, ob, topN):
    for sub in os.listdir(directory):
        absPath = os.path.join(directory, sub)

        try:
            if os.path.islink(absPath):
                pass
            elif os.path.isfile(absPath):
                checkSizeOfFile(absPath, ob, topN)
            elif os.path.isdir(absPath):
                checkFilesUnderDir(absPath, ob, topN)
        except:
            pass


if __name__ == "__main__":
    ob = findTopNFiles("/", 1000)

    fo = open("foo.txt", "w")
    printFiles(ob['seats'], fo)
    fo.close()