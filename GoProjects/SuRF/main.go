package main

import (
	"log"
	"math/rand"
	"net/http"
	_ "net/http/pprof"
	"os"
	"runtime/pprof"
	"sort"
	"unsafe"
	"ws/surf"
)

// 在初始化LOUDS的时候，数组的大小根据Level可以算一下，可以减少一半的内存消耗
// 为什么hashmap生成的hash就不能是有顺序的呢?研究一下hashmap的原理
// surf.sparse部分能不能把LUT4Child, LUT4Value & StartIndexOfSparseNode合并呢?通过0xFF的标记符

func main() {
	// darts.ReadRandomTextAsDAT("random.txt", 1<<14, true)
	// surf.ReadRandomTextAsSuRF("random.txt", 1<<24, true)
	// cpuProfileOfSuRF()
	testSpeedOfGetValue()
	// sizeTest()
	// res := surf.Uint256OnePositions([]uint64{12249790986447749120, 0, 0, 0})
	// for _, v := range res {
	// 	print(v, ",")
	// }
}

func generateRandomText() {
	str := "abcdefghijklmnopqrstuvwxyz"
	filename := "ordered.txt"

	f, err := os.Create(filename)
	if err != nil {
		panic(err)
	}
	defer f.Close()

	for is := range str {
		maxLines := 1 << 24
		allStrings2Write := make([]string, 0, maxLines)
		lineNo := 0
		for {
			randomCountOfString := rand.Intn(20) + 5
			bytes4NewString := make([]byte, 0, randomCountOfString)
			for is := 0; is < randomCountOfString; is++ {
				bytes4NewString = append(bytes4NewString, str[rand.Intn(len(str))])
			}

			allStrings2Write = append(allStrings2Write, string(bytes4NewString))
			lineNo++
			if lineNo == maxLines {
				break
			}
		}

		sort.Strings(allStrings2Write)
		for i, s := range allStrings2Write {
			f.Write([]byte{str[is]})
			f.WriteString(s)
			f.Write([]byte{'\n'})
			if i%100000 == 0 {
				log.Println(str[is], ":", i)
			}
		}

		f.Sync()
	}
}

/*
 map : SuRF = 1.2G(1.8G-Value0.6G) : 825M(No Value)
*/
func webProfileOfSuRF() {
	go func() {
		textList := surf.ReadFileAsList("random.txt", 1<<24)
		surf.ReadRandomTextAsSuRF(textList, false)
	}()
	log.Fatal(http.ListenAndServe("0.0.0.0:8080", nil))
	// go tool pprof http://localhost:8080/debug/pprof/profile
	// go tool pprof http://localhost:8080/debug/pprof/heap
	// go tool pprof http://localhost:8080/debug/pprof/block
	// go tool pprof -alloc_space http://localhost:8080/debug/pprof/heap
	// go tool pprof -inuse_space http://localhost:8080/debug/pprof/heap
}

func webProfileOfOb() {
	go func() {
		textList := surf.ReadFileAsList("random.txt", 1<<24)
		ob := surf.ReadFileAsOb(textList)
		times := 1
		for {
			for k := range ob {
				surf.DoNothing(k)
			}
			log.Println("完成第", times, "次遍历")
			times++
		}
	}()
	log.Fatal(http.ListenAndServe("0.0.0.0:8080", nil))
	// go tool pprof http://localhost:8080/debug/pprof/profile
	// go tool pprof http://localhost:8080/debug/pprof/heap
	// go tool pprof http://localhost:8080/debug/pprof/block
	// go tool pprof -alloc_space http://localhost:8080/debug/pprof/heap
	// go tool pprof -inuse_space http://localhost:8080/debug/pprof/heap
}

func webProfileOfList() {
	go func() {
		list := surf.ReadFileAsList("random2.txt", 1<<24)
		// tree := wsnode.ReadRandomTextAsTree("pctest3.txt", 1<<18)
		times := 1
		for {
			for i := range list {
				surf.DoNothing(i)
			}
			log.Println("完成第", times, "次遍历")
			times++
		}
	}()
	log.Fatal(http.ListenAndServe("0.0.0.0:8080", nil))
}

func cpuProfileOfSuRF() {
	cpuf, err := os.Create("cpu_profile")
	if err != nil {
		log.Fatal(err)
	}
	pprof.StartCPUProfile(cpuf)
	defer pprof.StopCPUProfile()

	textList := surf.ReadFileAsList("random.txt", 1<<20)
	surf.ReadRandomTextAsSuRF(textList, false)
}

func cpuProfileOfOB() {
	cpuf, err := os.Create("cpu_profile")
	if err != nil {
		log.Fatal(err)
	}
	pprof.StartCPUProfile(cpuf)
	defer pprof.StopCPUProfile()

	textList := surf.ReadFileAsList("random2.txt", 1<<24)
	surf.ReadFileAsOb(textList)
}

func sizeTest() {
	array := make([][]uint64, uint64(1)<<18)
	for i := range array {
		array[i] = make([]uint64, 4)
		array[i][0] = uint64(i)
		array[i][1] = uint64(i * 2)
		array[i][2] = uint64(i * 4)
		array[i][3] = uint64(i * 8)
	}
	println("sizeof(array):", unsafe.Sizeof(array))
	println("sizeof(array[0]):", unsafe.Sizeof(array[0]))
	println("sizeof(array[0][0]):", unsafe.Sizeof(array[0][0]))
	sizeOf2D := uint64(1<<18) << 3
	sizeOf1D := uint64(1<<18) << 3
	println("2D:", surf.SizeOfBytesAsString(sizeOf2D), ";1D:", surf.SizeOfBytesAsString(sizeOf1D))
	surf.CreateMemFile("size_test_mem_file")
	for i := 0; i < 1<<1; i++ {
		for _, v := range array {
			surf.DoNothing(v)
		}
	}
}

// ob:5327,louds:11931
// ob:5141,louds:19125 ------ 变差了,可能是因为把values变成一维数组,每次取都要用截取操作导致的吧
// ob:5233,louds:24024 ------ sparse.startNodeVectorSelect.interval=1
// ob:6769,louds:32588 ------ sparse.startNodeVectorSelect.interval=4
func testSpeedOfGetValue() {
	textList := surf.ReadFileAsList("random.txt", 1<<24)
	_testSpeedOfGetValueOfOB(textList)
	_testSpeedOfGetValueOfLOUDS(textList)
}

func _testSpeedOfGetValueOfOB(textList []string) {
	ob := surf.ReadFileAsOb(textList)
	surf.TestSpeedOfOB(textList, ob)
}

func _testSpeedOfGetValueOfLOUDS(textList []string) {
	sf := surf.ReadRandomTextAsSuRF(textList, false)
	surf.TestSpeedOfLOUDS(textList, sf)
}
