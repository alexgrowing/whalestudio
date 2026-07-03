package main

import (
	"log"
	"net/http"
	"strconv"
	"ws/gym/db"
	"ws/base"
	"encoding/json"
	"ws/base/account"
)

const (
	message_ERROR_NOT_LOGIN_YET = "ERROR_NOT_LOGIN_YET"
)

func main() {
	PORT := 9988

	account.HandleHttpRequest()

	http.HandleFunc("/lastmodified", fetchLastModified)
	http.HandleFunc("/uploadall", uploadAll)
	http.HandleFunc("/downloadall", downloadAll)

	http.HandleFunc("/refreshallmoves", actionOfRefreshAllMoves)
	http.HandleFunc("/newtraining", actionOfNewTrainingAction)

	account.EnsureDB()
	db.EnsureIndex()

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
		returnSM["lastmodified"] = db.FetchLastModifiedAsUnix(objectId)
	}

	returnSM.ZipWrite(w)
}

func uploadAll(w http.ResponseWriter, r *http.Request) {
	returnSM := base.SM{}

	passcode := r.FormValue("passcode")
	data := r.FormValue("data")

	objectId := account.FindAccountIdByPasscode(passcode)
	if !objectId.Valid() {
		returnSM.MarkErrorMessage(message_ERROR_NOT_LOGIN_YET)
	} else {
		var jsonOb map[string]interface{}
		if err := json.Unmarshal([]byte(data), &jsonOb); err != nil {
			return
		}

		json4CategoriedMoves := jsonOb["categoriedmoves"].([]interface{})
		json4Trainings := jsonOb["trainings"].([]interface{})

		db.UploadAllCategoriedMoves(objectId, json4CategoriedMoves)
		db.UploadAllTrainings(objectId, json4Trainings)
		db.UploadAllAction(objectId, jsonOb)

		returnSM.MarkAsSuccess()
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
		returnSM["categoriedmoves"] = db.DownloadCategoriedMoves(objectId)
		returnSM["trainings"] = db.DownloadAllTrainings(objectId)
		db.DownloadAction(objectId, returnSM)
	}

	returnSM.ZipWrite(w)
}

func actionOfRefreshAllMoves(w http.ResponseWriter, r *http.Request) {
	returnSM := base.SM{}

	passcode := r.FormValue("passcode")
	data := r.FormValue("data")

	objectId := account.FindAccountIdByPasscode(passcode)
	if !objectId.Valid() {
		returnSM.MarkErrorMessage(message_ERROR_NOT_LOGIN_YET)
	} else {
		var jsonOb map[string]interface{}
		if err := json.Unmarshal([]byte(data), &jsonOb); err != nil {
			return
		}

		json4CategoriedMoves := jsonOb["categoriedmoves"].([]interface{})

		db.UploadAllCategoriedMoves(objectId, json4CategoriedMoves)
		db.UploadAllAction(objectId, jsonOb)

		returnSM.MarkAsSuccess()
	}

	returnSM.ZipWrite(w)
}

func actionOfNewTrainingAction(w http.ResponseWriter, r *http.Request) {
	returnSM := base.SM{}

	passcode := r.FormValue("passcode")
	data := r.FormValue("data")

	objectId := account.FindAccountIdByPasscode(passcode)
	if !objectId.Valid() {
		returnSM.MarkErrorMessage(message_ERROR_NOT_LOGIN_YET)
	} else {
		var jsonOb map[string]interface{}
		if err := json.Unmarshal([]byte(data), &jsonOb); err != nil {
			return
		}

		db.SetNewTraining(objectId, jsonOb["training"].(map[string]interface{}))
		db.UploadAllAction(objectId, jsonOb)

		returnSM.MarkAsSuccess()
	}
	returnSM.ZipWrite(w)
}