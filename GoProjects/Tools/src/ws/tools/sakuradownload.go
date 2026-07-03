package tools

import (
	"os"
	"bufio"
	"strconv"
	"fmt"
)

func SakuraDownload() {
	var filename = "./download_new.bat"

	var f *os.File

	if _, err := os.Stat(filename);os.IsNotExist(err) {
		f, err = os.Create(filename)
	} else {
		f, err = os.OpenFile(filename, os.O_WRONLY|os.O_TRUNC|os.O_CREATE, 0666)
	}

	w := bufio.NewWriter(f)
	writeBat(w)
	w.Flush()
	f.Close()
}

func writeBat(w *bufio.Writer) {
	var countOfURLS = 0
	var atoz = "abcdefghijklmnopqrstuvwxyz"

	var countOfUnits = 12
	for ui := 1; ui <= countOfUnits; ui++ {
		w.WriteString(fmt.Sprint("set Obj[", countOfURLS, "]$URL=\"http://192.168.1.2/product7/level7/l7_learn/L7_learn_", ui, ".swf\"\n"))
		countOfURLS++

		w.WriteString(fmt.Sprint("set Obj[", countOfURLS, "]$URL=\"http://192.168.1.2/product7/level7/amination/Unit", ui, "/lev7_U", fillTensPlace(ui), "_lesson.swf\"\n"))
		countOfURLS++

		var countOfLessonsOfThisUnit = 9
		for li:=1;li<=countOfLessonsOfThisUnit; li++ {
			w.WriteString(fmt.Sprint("set Obj[", countOfURLS, "]$URL=\"http://192.168.1.2/product7/level7/amination/Unit", ui, "/lev7_U", fillTensPlace(ui), "_lesson",li,".swf\"\n"))
			countOfURLS++
		}

		var countOfTopics = 5
		for ti:=1;ti<=countOfTopics;ti++ {
			w.WriteString(fmt.Sprint("set Obj[", countOfURLS, "]$URL=\"http://192.168.1.2/product7/level7/amination/Unit", ui, "/lev7_U", fillTensPlace(ui), "_topic",ti,".swf\"\n"))
			countOfURLS++

			var countOfSubTopics = 26
			for sti:=0;sti<countOfSubTopics;sti++ {
				w.WriteString(fmt.Sprint("set Obj[", countOfURLS, "]$URL=\"http://192.168.1.2/product7/level7/amination/Unit", ui, "/lev7_U", fillTensPlace(ui), "_topic",ti,atoz[sti:sti+1],".swf\"\n"))
				countOfURLS++
			}
		}

		var countOfTrains = 10
		for ti:=1;ti<=countOfTrains;ti++ {
			w.WriteString(fmt.Sprint("set Obj[", countOfURLS, "]$URL=\"http://192.168.1.2/product7/level7/amination/Unit", ui, "/lev7_u", fillTensPlace(ui), "_train",ti,".swf\"\n"))
			countOfURLS++
		}
	}

	w.WriteString(fmt.Sprint("SET Obj_Index=0\n"))
	w.WriteString(fmt.Sprint("set Obj_Length=",countOfURLS, "\n"))

	w.WriteString(":LoopStart\n")
	w.WriteString("IF %Obj_Index% EQU %Obj_Length% GOTO :EOF\n")

	w.WriteString("SET Obj_Current.URL=0\n")
	w.WriteString("FOR /F \"usebackq delims==$ tokens=1-3\" %%I IN (`SET Obj[%Obj_Index%]`) DO (\n")
	w.WriteString("  SET Obj_Current.%%J=%%K\n")
	w.WriteString(")\n")

	w.WriteString("curl/bin/curl -O %Obj_Current.URL%\n")
	w.WriteString("SET /A Obj_Index=%Obj_Index% + 1\n")
	w.WriteString("GOTO LoopStart\n")
}

func fillTensPlace(number int) string {
	if number < 10 {
		return "0" + strconv.Itoa(number)
	} else {
		return strconv.Itoa(number)
	}
}