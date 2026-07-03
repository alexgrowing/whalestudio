package darts

import (
	"fmt"
	"log"
	"os"
	"runtime/pprof"
	"sort"
	"time"
	"ws/surf"
)

// DoubleArrayTrie DoubleArrayTrie
type DoubleArrayTrie struct {
	base  []int
	check []int

	beginUsed []bool

	keys []string
}

type _Node struct {
	code  int
	depth int
	left  int
	right int
}

func newDoubleArrayTrie() *DoubleArrayTrie {
	return &DoubleArrayTrie{}
}

func newNode() *_Node {
	return &_Node{}
}

func (me *DoubleArrayTrie) build(keys []string) {
	me.resize(65536 * 32)
	me.base[0] = 1
	rootNode := newNode()
	rootNode.left = 0
	rootNode.right = len(keys)
	rootNode.depth = 0

	me.keys = keys

	children := me.fetchChildrenNodes(rootNode)
	me.insert(children)

	me.beginUsed = nil
	me.keys = nil
}

func (me *DoubleArrayTrie) resize(newSize int) {
	base2 := make([]int, newSize)
	check2 := make([]int, newSize)
	beginUsed2 := make([]bool, newSize)

	copy(base2, me.base)
	copy(check2, me.check)
	copy(beginUsed2, me.beginUsed)

	me.base = base2
	me.check = check2
	me.beginUsed = beginUsed2
}

func (me *DoubleArrayTrie) fetchChildrenNodes(parent *_Node) []*_Node {
	var prev int
	sibling := make([]*_Node, 0)
	for i := parent.left; i < parent.right; i++ {
		tmp := []rune(me.keys[i])
		if len(tmp) < parent.depth {
			continue
		}

		cur := 0
		if len(tmp) > parent.depth {
			cur = int(tmp[parent.depth]) + 1
		}

		if cur != prev || len(sibling) == 0 {
			tmpNode := newNode()
			tmpNode.depth = parent.depth + 1
			tmpNode.code = cur
			tmpNode.left = i

			if len(sibling) > 0 {
				sibling[len(sibling)-1].right = i
			}

			sibling = append(sibling, tmpNode)
		}

		prev = cur
	}

	if len(sibling) > 0 {
		sibling[len(sibling)-1].right = parent.right
	}

	return sibling
}

func (me *DoubleArrayTrie) insert(siblings []*_Node) int {
	// 通过检查check[begin + siblings]是否为0（位置是否空闲），寻找一个安置下所有siblings的begin值
	begin := 1
	for true {
		if me.beginUsed[begin] {
			begin++
			continue
		}
		break
	}
	for true {
		beginAvailable := true
		for _, node := range siblings {
			if me.check[begin+node.code] != 0 {
				beginAvailable = false
				break
			}
		}
		if beginAvailable {
			break
		}
		begin++
	}
	me.beginUsed[begin] = true

	// 开始填sibling,先填check,再填base
	for _, node := range siblings {
		me.check[begin+node.code] = begin
	}
	for _, node := range siblings {
		children := me.fetchChildrenNodes(node)

		if len(children) == 0 {
			// 没有children了,已经是最后一个字符了,用来标记位置
			me.base[begin+node.code] = -node.left - 1
		} else {
			beginOfChildren := me.insert(children)
			me.base[begin+node.code] = beginOfChildren
		}
	}

	return begin
}

func (me *DoubleArrayTrie) search(key string) (bool, int) {
	posOfBegin := me.base[0]

	chars := []rune(key)
	foundMatch := true
	for i := 0; i < len(chars); i++ {
		character := chars[i]
		posOfCharacter := posOfBegin + int(character) + 1
		if me.check[posOfCharacter] == 0 {
			foundMatch = false
			break
		}

		posOfBegin = me.base[posOfCharacter]
	}

	if foundMatch && me.base[posOfBegin] < 0 {
		return true, -me.base[posOfBegin] - 1
	}
	return false, 0
}

func (me *DoubleArrayTrie) dump() {
	println("i\tbase\tcheck\ti-check-1")
	for i := range me.base {
		if me.base[i] != 0 || me.check[i] != 0 {
			println(i, "\t", me.base[i], "\t", me.check[i], "\t", string(i-me.check[i]-1))
		}
	}
}

// ReadRandomTextAsDAT ReadRandomTextAsDAT
func ReadRandomTextAsDAT(filename string, maxLines uint64, doAssert bool) *DoubleArrayTrie {
	mapOB := surf.ReadFileAsOb(filename, maxLines)

	stringKeys := make([]string, 0, len(mapOB))
	for k := range mapOB {
		stringKeys = append(stringKeys, k)
	}
	sort.Strings(stringKeys)

	start := time.Now().UnixNano()
	cpuf, err := os.Create("cpu_profile")
	if err != nil {
		log.Fatal(err)
	}
	pprof.StartCPUProfile(cpuf)
	dat := newDoubleArrayTrie()
	dat.build(stringKeys)
	log.Println("build DAT time spent:", (time.Now().UnixNano()-start)/1000000)
	pprof.StopCPUProfile()
	surf.CreateMemFile("dat_mem_file")

	// dat.dump()

	if doAssert {
		start = time.Now().UnixNano()
		for i, key := range stringKeys {
			found, index := dat.search(key)
			if i != index {
				panic(fmt.Sprintln("search:", key, "should index:", i, "!=", index))
			}
			if !found {
				panic(fmt.Sprintln("search:", key, "should found:true"))
			}
		}
		log.Println("do Assert time spent:", (time.Now().UnixNano()-start)/1000000)

		if found, _ := dat.search("大家好"); found {
			panic(fmt.Sprintln("search:大家好, should found:false"))
		}
		if found, _ := dat.search("一"); found {
			panic(fmt.Sprintln("search:一, should found:false"))
		}
		if found, _ := dat.search("一举一"); found {
			panic(fmt.Sprintln("search:一举一, should found:false"))
		}
	}

	return dat
}
