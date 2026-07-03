package account

import (
	"net/http"
	"ws/base"
)

func HandleHttpRequest(listener IAccountListener) {
	http.HandleFunc("/a4vc", ask4VerifyCode)
	//http.HandleFunc("/register", register)
	//http.HandleFunc("/login", login)
	//http.HandleFunc("/logingc", loginByGameCenter)
	http.HandleFunc("/quick", quickLogin)
	http.HandleFunc("/loginbygamecenter", loginByGameCenterId)
	http.HandleFunc("/createquickaccount", createQuickAccount)

	appendListener(listener)
}

func ask4VerifyCode(w http.ResponseWriter, r *http.Request) {
	returnSM := base.SM{}

	email:=r.FormValue("email")
	if !base.ValidateFormatOfEmail(email) {
		returnSM.MarkErrorMessage(message_ERROR_FORMAT_OF_EMAIL_IS_NOT_RIGHT)
	} else {
		if verifyCode, err := createVerifyCode4Register(email); err == nil {

			err := base.SendVerifyCode(verifyCode, email)
			if err == nil {
				returnSM.MarkAsSuccess()
			} else {
				returnSM.MarkErrorMessage(err.Error())
			}
		} else {
			returnSM.MarkErrorMessage(err.Error())
		}
	}

	returnSM.ZipWrite(w)
}

func quickLogin(w http.ResponseWriter, r *http.Request) {
	quickPassCode := r.FormValue("passcode")

	dbLoginByQuickPassCode(quickPassCode).ZipWrite(w)
}

func loginByGameCenterId(w http.ResponseWriter, r *http.Request) {
	idOfGameCenter := r.FormValue("gamecenterid")
	nameOfGameCenter := r.FormValue("gamecentername")

	ensureAccountByGameCenter(idOfGameCenter, nameOfGameCenter).ZipWrite(w)
}

func createQuickAccount(w http.ResponseWriter, r *http.Request) {
	defaultName := r.FormValue("dname")
	if len(defaultName) == 0 {
		defaultName = "Player"
	}
	createAccountByNameAndGameCenterId(defaultName, "").ZipWrite(w)
}

/*
func register(w http.ResponseWriter, r *http.Request) {
	email:=r.FormValue("email")
	verifyCode:=r.FormValue("code")
	password:=r.FormValue("password")

	returnSM := base.SM{}

	if !base.ValidateFormatOfEmail(email) {
		returnSM.MarkErrorMessage(message_ERROR_FORMAT_OF_EMAIL_IS_NOT_RIGHT)
	} else if !base.ValidatePasswordStrength(password) {
		returnSM.MarkErrorMessage(message_ERROR_PASSWORD_SHOULD_CONTAIN_NUMBERS_AND_LETTERS)
	} else if !CheckValidationOfEmailAndCode(email, verifyCode) {
		returnSM.MarkErrorMessage(message_ERROR_VERIFY_CODE_NOT_MATCH)
	} else {
		returnSM = ensureAccount(email, password)
	}

	returnSM.ZipWrite(w)
}
*/

/*
func loginByGameCenter(w http.ResponseWriter, r *http.Request) {
	idOfGameCenter := r.FormValue("gamecenterid")

	dbLoginByIdOfGameCenter(idOfGameCenter).ZipWrite(w)
}
*/

/*
func login(w http.ResponseWriter, r *http.Request) {
	email:=r.FormValue("email")
	password:=r.FormValue("password")

	dbLogin(email, password).ZipWrite(w)
}
*/