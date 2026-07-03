package main

import (
	"log"
	"net/http"
	"strconv"
	"ws/base"
	"ws/base/account"
	"ws/kc/db"
	"encoding/json"
	"os"
	"io/ioutil"
	"html/template"
)

const (
	message_ERROR_NOT_LOGIN_YET = "ERROR_NOT_LOGIN_YET"
	folder4UserFiles = "../kc_user_files"
)

func main() {
	PORT := 9527

	os.Mkdir(folder4UserFiles, os.ModePerm)

	account.HandleHttpRequest()

	http.HandleFunc("/lastmodified", fetchLastModified)
	http.HandleFunc("/upload", upload)
	http.HandleFunc("/imageupload", base.NewUploadHandlerOb(folder4UserFiles).Handler)
	http.HandleFunc("/downloadall", downloadAll)
	http.HandleFunc("/edit", editKnowledge)
	http.HandleFunc("/delete", deleteKnowledge)

	http.Handle("/kc_user_files/", http.FileServer(http.Dir("..")))

	http.HandleFunc("/info", info)

	account.EnsureDB()

	log.Println("监听" + strconv.Itoa(PORT) + "端口...")
	log.Fatal(http.ListenAndServe(":"+strconv.Itoa(PORT), nil))
}

func fetchLastModified(w http.ResponseWriter, r *http.Request) {
	returnSM := base.SM{}

	passcode := r.FormValue("passcode")

	objectId := account.FindAccountIdByPasscode(passcode)
	if !objectId.Valid() {
		returnSM.MarkErrorMessage(message_ERROR_NOT_LOGIN_YET)
	} else {
		returnSM["lastmodified"] = db.FetchLastModified(objectId).Unix()
	}

	returnSM.ZipWrite(w)
}

func upload(w http.ResponseWriter, r *http.Request) {
	returnSM := base.SM{}

	passcode := r.FormValue("passcode")
	data := r.FormValue("data")

	objectId := account.FindAccountIdByPasscode(passcode)
	if !objectId.Valid() {
		returnSM.MarkErrorMessage(message_ERROR_NOT_LOGIN_YET)
	} else {
		var jsonOb base.SM
		if err := json.Unmarshal([]byte(data), &jsonOb); err != nil {
			return
		}

		if lastModified, err := db.UploadKnowledge(objectId, jsonOb); err == nil {
			returnSM["lastmodified"] = lastModified.Unix()
		} else {
			returnSM.MarkErrorMessage(err.Error())
		}
	}

	returnSM.ZipWrite(w)
}

func editKnowledge(w http.ResponseWriter, r *http.Request) {
	returnSM := base.SM{}

	passcode := r.FormValue("passcode")
	index, _ := strconv.Atoi(r.FormValue("index"))
	newText := r.FormValue("text")

	objectId := account.FindAccountIdByPasscode(passcode)
	if !objectId.Valid() {
		returnSM.MarkErrorMessage(message_ERROR_NOT_LOGIN_YET)
	} else {
		if lastModified, err := db.EditKnowledge(objectId, index, newText); err == nil {
			returnSM["lastmodified"] = lastModified.Unix()
		} else {
			returnSM.MarkErrorMessage(err.Error())
		}
	}

	returnSM.ZipWrite(w)
}

func deleteKnowledge(w http.ResponseWriter, r *http.Request) {
	returnSM := base.SM{}

	passcode := r.FormValue("passcode")
	index, _ := strconv.Atoi(r.FormValue("index"))

	objectId := account.FindAccountIdByPasscode(passcode)
	if !objectId.Valid() {
		returnSM.MarkErrorMessage(message_ERROR_NOT_LOGIN_YET)
	} else {
		if lastModified, err := db.DeleteKnowledge(objectId, index); err == nil {
			returnSM["lastmodified"] = lastModified.Unix()
		} else {
			returnSM.MarkErrorMessage(err.Error())
		}
	}

	returnSM.ZipWrite(w)
}

func downloadAll(w http.ResponseWriter, r *http.Request) {
	returnSM := base.SM{}

	passcode := r.FormValue("passcode")
	objectId := account.FindAccountIdByPasscode(passcode)
	if !objectId.Valid() {
		returnSM.MarkErrorMessage(message_ERROR_NOT_LOGIN_YET)
	} else {
		if knows, lastModified, err := db.DownloadAllKnows(objectId); err == nil {
			returnSM["lastmodified"] = lastModified.Unix()
			returnSM["knows"] = db.EncodeKnowsAsJson(knows)
		} else {
			returnSM.MarkErrorMessage(err.Error())
		}
	}

	returnSM.ZipWrite(w)
}

func info(w http.ResponseWriter, r *http.Request) {
	sm := db.Info()

	images := make([]string, 0)
	files, _ := ioutil.ReadDir(folder4UserFiles)
	for _, f := range files {
		images = append(images, f.Name())
	}
	sm["countofimages"] = len(images)
	sm["images"] = images

	t := template.New("")
	t = template.Must(t.ParseFiles("tpl/info.html"))

	t.ExecuteTemplate(w, "info.html", sm)
}