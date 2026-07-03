package main

import (
	"net/http"
	"log"
	"strconv"
	"io/ioutil"
	"os"
	"ws/base"
)

func main() {
	PORT := 4004

	log.Println("监听" + strconv.Itoa(PORT) + "端口...")
	http.Handle("/f/", http.FileServer(http.Dir("..")))
	http.Handle("/fr/", http.FileServer(http.Dir("..")))

	http.HandleFunc("/figureupload", figureUploadHandler)

	log.Fatal(http.ListenAndServe(":"+strconv.Itoa(PORT), nil))
}

func figureUploadHandler(w http.ResponseWriter, r *http.Request) {
	sm := base.SM{}
	if file, handler, err := r.FormFile("userfile"); err == nil {
		defer file.Close()
		if bytes, err := ioutil.ReadAll(file); err == nil {
			if outputFile, err := os.Create(getPath2Directory(handler.Filename)); err == nil {
				defer outputFile.Close()
				if _, err := outputFile.Write(bytes); err == nil {
					sm.MarkAsSuccess()
				} else {
					sm.MarkErrorMessage(err.Error())
				}
			} else {
				sm.MarkErrorMessage(err.Error())
			}
		}
	} else {
		sm.MarkErrorMessage(err.Error())
	}

	sm.ZipWrite(w)
}

func getPath2Directory(filename string) string {
	return "../" + folder_name_saving_player_figures + "/" + filename
}

const folder_name_saving_player_figures = "f"
