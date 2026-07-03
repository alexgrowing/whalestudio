package main

import (
	"log"
	"strconv"
	"net/http"
	"bytes"
	"os/exec"
	"ws/base"
	"time"
	"os"
	"io"
	"bufio"
	"html/template"
	"strings"
)

func main() {
	PORT := 9001

	log.Println("监听" + strconv.Itoa(PORT) + "端口...")

	http.HandleFunc("/kill", killHandler)
	http.HandleFunc("/start", startHandler)
	http.HandleFunc("/clean", cleanHandler)

	http.Handle("/js/", http.FileServer(http.Dir("static")))

	http.HandleFunc("/", templateHandler)

	go startTimer()
	log.Fatal(http.ListenAndServe(":"+strconv.Itoa(PORT), nil))
}

func templateHandler(w http.ResponseWriter, r *http.Request) {
	t := template.New("")
	//t = t.Funcs(template.FuncMap{"unescaped": unescaped})
	t = template.Must(t.ParseFiles("templates/index.html", "templates/project.html"))

	obs := make([]base.SM, len(projects))
	for index, p := range projects {
		obs[index] = base.SM{}
		obs[index]["name"] = p.name
		obs[index]["running"] = isProjectRunning(p.name)
		obs[index]["information"] = p.information
	}

	t.ExecuteTemplate(w, "index.html", obs)
}

/*
func unescaped (x string) interface{} {
	return x
}
*/

func killHandler(w http.ResponseWriter, r *http.Request) {
	project2Kill := r.FormValue("project")

	for _, p := range projects {
		if p.name == project2Kill {
			if err := executeShell(p.nameOfKillShell); err == nil {
				w.Write([]byte("success"))
			} else {
				w.Write([]byte(err.Error()))
			}

			return
		}
	}

	w.Write([]byte("no matched project[" + project2Kill + "] found"))
}

func startHandler(w http.ResponseWriter, r *http.Request) {
	project2Start := r.FormValue("project")

	for _, p := range projects {
		if p.name == project2Start {
			if err := executeShell(p.nameOfStartShell); err == nil {
				w.Write([]byte("success"))
			} else {
				w.Write([]byte(err.Error()))
			}

			return
		}
	}

	w.Write([]byte("no matched project[" + project2Start + "] found"))
}

func cleanHandler(w http.ResponseWriter, r *http.Request) {
	project2Clean := r.FormValue("project")

	for _, p := range projects {
		if p.name == project2Clean {
			if err := executeShell(p.nameOfCleanShell); err == nil {
				w.Write([]byte("success"))
			} else {
				w.Write([]byte(err.Error()))
			}

			return
		}
	}

	w.Write([]byte("no matched project[" + project2Clean + "] found"))
}

type project struct {
	name               string
	information string

	isRunningLastCheck bool
	nameOfKillShell    string
	nameOfStartShell   string
	nameOfCleanShell string
}

func newProject(name string, information string) *project {
	p := project{}
	p.name = name
	p.information = information

	p.isRunningLastCheck = true
	p.nameOfKillShell = strings.ToLower(name) + "_kill_process.sh"
	p.nameOfStartShell = strings.ToLower(name) + "_start_server.sh"
	p.nameOfCleanShell = strings.ToLower(name) + "_clean_folder.sh"

	return &p
}

var projects = []*project{
	newProject("WhaleStudio", ""),
	newProject("URLMonitor", ""),
	newProject("Gym", ""),
	newProject("KnowledgeCard", "http://www.whalestudio.cn:9527/info"),
	newProject("DiceGame", "http://www.whalestudio.cn:8888/session/alive"),
	newProject("Territory", "http://www.whalestudio.cn:9999/info"),
	newProject("Figure", ""),
}

func checkProjects() {
	changed := false

	for _, p := range projects {
		newResult := isProjectRunning(p.name)

		if p.isRunningLastCheck != newResult {
			changed = true
			p.isRunningLastCheck = newResult
		}
	}

	if changed {
		var buffer bytes.Buffer
		for _, p := range projects {
			buffer.WriteString(p.name + ":" + strconv.FormatBool(p.isRunningLastCheck) + "\n")
			if !p.isRunningLastCheck {
				buffer.WriteString("messages:" + readAndClearLogMessage(p.name))
				buffer.WriteString("\n\n\n\n\n")
			}
		}

		base.SendEmail("服务器状态有变动", buffer.String(), "18101584@qq.com")
	}
}

func startTimer() {
	checkProjects()

	select {
	case <-time.After(60 * time.Second):
		startTimer()
	}
}

func executeShell(nameOfShell string) error {
	cmd := exec.Command("sh")
	in := bytes.NewBuffer(nil)
	cmd.Stdin = in

	in.WriteString("cd ~\n")
	in.WriteString("sh " + nameOfShell + "\n")
	in.WriteString("exit\n")

	return cmd.Run()
}

func isProjectRunning(nameOfProject string) bool {
	cmd := exec.Command("sh")
	in := bytes.NewBuffer(nil)
	cmd.Stdin = in

	var out bytes.Buffer
	cmd.Stdout = &out

	in.WriteString("pidof " + nameOfProject + "\n")
	in.WriteString("exit\n")

	if err := cmd.Run(); err != nil {
		return false
	} else {
		return true
	}
}

func readAndClearLogMessage(nameOfProject string) string {
	filePath := "../" + strings.ToLower(nameOfProject) + "_out.file"
	file, err := os.Open(filePath)

	if err != nil {
		return err.Error()
	}
	defer file.Close()

	bufLen, _ := file.Seek(0, io.SeekEnd)

	var lenOfFileNeeded int64 = 1024 * 2
	if bufLen > lenOfFileNeeded {
		file.Seek(-lenOfFileNeeded, io.SeekCurrent)
	} else {
		file.Seek(0, io.SeekStart)
	}

	bufReader := bufio.NewReader(file)
	buf := make([]byte, lenOfFileNeeded)
	var outputBuf bytes.Buffer

	for {
		readNum, err := bufReader.Read(buf)
		if err != nil && err != io.EOF {
			return err.Error()
		}

		if 0 == readNum {
			break
		}

		outputBuf.Write(buf[:readNum])
	}

	newFile, err := os.OpenFile(filePath, os.O_WRONLY|os.O_TRUNC, 0600)
	defer newFile.Close()
	newFile.WriteString(outputBuf.String())

	return outputBuf.String()
}
