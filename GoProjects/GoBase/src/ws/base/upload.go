package base

import (
	"net/http"
	"io/ioutil"
	"os"
	"log"
)

type UploadHandlerOb struct {
	folder string
}

func NewUploadHandlerOb(destination string) *UploadHandlerOb {
	ob := UploadHandlerOb{}
	ob.folder = destination

	return &ob
}

func (self *UploadHandlerOb) Handler(w http.ResponseWriter, r *http.Request) {
	if file, handler, err := r.FormFile("userfile"); err == nil {
		defer file.Close()
		if bytes, err := ioutil.ReadAll(file); err == nil {
			if outputFile, err := os.Create(self.folder + "/" + handler.Filename); err == nil {
				defer outputFile.Close()
				if _, err := outputFile.Write(bytes); err == nil {
					log.Print("ok")
					w.Write([]byte("ok"))
				} else {
					log.Print("1:", err.Error())
					w.Write([]byte("1:" + err.Error()))
				}
			} else {
				log.Print("2:", err.Error())
				w.Write([]byte("2:" + err.Error()))
			}
		}
	} else {
		w.Write([]byte("3:" + err.Error()))
	}
}
