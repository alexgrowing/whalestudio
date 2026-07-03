package account

import (
	"gopkg.in/mgo.v2/bson"
	"time"
	"ws/base"
	"strings"
)

const (
	dbName           = "Whale"
	tableNameAccount = "account"

	message_ERROR_LOGIN_WRONG_PASSWORD = "ERROR_LOGIN_WRONG_PASSWORD"
	message_ERROR_LOGIN_ACCOUNT_NOT_FOUND = "ERROR_LOGIN_ACCOUNT_NOT_FOUND"

	message_ERROR_FORMAT_OF_EMAIL_IS_NOT_RIGHT = "ERROR_FORMAT_OF_EMAIL_IS_NOT_RIGHT"
	message_ERROR_PASSWORD_SHOULD_CONTAIN_NUMBERS_AND_LETTERS = "ERROR_PASSWORD_SHOULD_CONTAIN_NUMBERS_AND_LETTERS"
	message_ERROR_VERIFY_CODE_NOT_MATCH = "ERROR_VERIFY_CODE_NOT_MATCH"

	message_ERROR_QUCIK_LOGIN_FAILED = "ERROR_QUCIK_LOGIN_FAILED"
)

type Account struct {
	Id   bson.ObjectId `bson:"_id"`

	//Email string
	//EncodedPassword string

	GameCenterId string

	QuickPassCode string
	QuickPassCodeExpired time.Time

	Nickname string
}

type IAccountListener interface {
	AccountFound(account *Account)
}

var listeners []IAccountListener = make([]IAccountListener, 0)

func appendListener(l IAccountListener) {
	listeners = append(listeners, l)
}

func EnsureDB() {
	//ensureIndex()
	//ensureAccount4Test()
	ensureTimer2DeleteLastDayVerifyCode()
}

/*
func ensureIndex() {
	index := mgo.Index{
		Key : []string {"email"},
		Unique:true,
		DropDups:true,
		Background:true,
		Sparse:true,
	}

	base.EnsureIndex(dbName, tableNameAccount, &index)
}
*/

/*
func ensureAccount4Test() {
	ensureAccount("test@whalestudio.cn", "test123")
}
*/

func FindAccountIdByPasscode(passcode string) bson.ObjectId {
	if len(passcode) == 0 {
		return ""
	}

	account := newBlankAccount()
	if err := base.DBFindOne(dbName, tableNameAccount, bson.M{"quickpasscode":passcode}, account); err == nil {
		return account.Id
	}

	return ""
}

func newBlankAccount() *Account {
	account := Account{}

	return &account
}

/*
func isEmailExist(email string) bool {
	email = strings.ToLower(email)

	if count, err := base.DBCount(dbName, tableNameAccount, bson.M{"email":email}); err == nil && count > 0{
		return true
	}

	return false
}
*/

func isGameCenterIdExist(idOfGameCenter string) bool {
	idOfGameCenter = strings.ToLower(idOfGameCenter)

	if count, err := base.DBCount(dbName, tableNameAccount, bson.M{"gamecenterid":idOfGameCenter}); err == nil && count > 0{
		return true
	}

	return false
}

func isGameCenterIdAndPasscodeMatch(idOfGameCenter string, passcode string) bool {
	idOfGameCenter = strings.ToLower(idOfGameCenter)

	if count, err := base.DBCount(dbName, tableNameAccount, bson.M{"gamecenterid":idOfGameCenter,"quickpasscode":passcode}); err == nil && count > 0{
		return true
	}

	return false
}

/*
func ensureAccount(email string, password string) base.SM {
	email = strings.ToLower(email)

	returnSM := base.SM{}

	if isEmailExist(email) {
		account := newBlankAccount()

		if err := base.DBFindOne(dbName, tableNameAccount, bson.M{"email":email}, account); err == nil {
			account.EncodedPassword = base.GetMd5String(password)

			didEnsureAccountExist(account, false)

			if err := base.DBUpdate(dbName, tableNameAccount, account.Id, account); err == nil {
				returnSM["passcode"] = account.QuickPassCode
				returnSM["newaccount"] = false
			} else {
				returnSM.MarkErrorMessage(err.Error())
			}
		} else {
			returnSM.MarkErrorMessage(err.Error())
		}
	} else {
		account := newBlankAccount()
		account.Id = bson.NewObjectId()
		account.Email = email
		account.EncodedPassword = base.GetMd5String(password)

		didEnsureAccountExist(account, true)

		if err := base.DBInsert(dbName, tableNameAccount, account); err == nil {
			returnSM["passcode"] = account.QuickPassCode
			returnSM["newaccount"] = true
		} else {
			returnSM.MarkErrorMessage(err.Error())
		}
	}

	return returnSM
}
*/

/*
passcode
uuid
newaccount
 */
func ensureAccountByGameCenter(idOfGameCenter string, nameOfGameCenter string) base.SM {
	idOfGameCenter = strings.ToLower(idOfGameCenter)

	account := newBlankAccount()
	if isGameCenterIdExist(idOfGameCenter) {
		if err := base.DBFindOne(dbName, tableNameAccount, bson.M{"gamecenterid":idOfGameCenter}, account); err == nil {
			account.Nickname = nameOfGameCenter

			return upsertAccount(account, false)
		} else {
			res := base.SM{}
			res.MarkErrorMessage(err.Error())

			return res
		}
	} else {
		return createAccountByNameAndGameCenterId(nameOfGameCenter, idOfGameCenter)
	}
}

func createAccountByNameAndGameCenterId(nickName string, gameCenterId string) base.SM {
	account := newBlankAccount()
	account.Id = bson.NewObjectId()

	if len(nickName) > 0 {
		account.Nickname = nickName
	}
	if len(gameCenterId) > 0 {
		account.GameCenterId = gameCenterId
	}

	return upsertAccount(account, true)
}

func upsertAccount(account *Account, doInsert bool) base.SM {
	returnSM := base.SM{}
	extendExpiredPeriod(account, true)

	var err error
	if doInsert {
		err = base.DBInsert(dbName, tableNameAccount, account)
	} else {
		err = base.DBUpdate(dbName, tableNameAccount, account.Id, account)
	}

	if err == nil {
		returnSM["passcode"] = account.QuickPassCode
		returnSM["uuid"] = account.Id.Hex()
		returnSM["newaccount"] = doInsert
	} else {
		returnSM.MarkErrorMessage(err.Error())
	}

	for i := 0; i < len(listeners); i++  {
		listeners[i].AccountFound(account)
	}

	return returnSM
}

/*
func dbLogin(email string, password string) base.SM {
	email = strings.ToLower(email)
	
	account := newBlankAccount()
	returnSM := base.SM{}

	if err := base.DBFindOne(dbName, tableNameAccount, bson.M{"email":email}, account); err == nil {
		if account.EncodedPassword == base.GetMd5String(password) {
			didEnsureAccountExist(account, account.QuickPassCodeExpired.Before(time.Now()))

			err = base.DBUpdate(dbName, tableNameAccount, account.Id, account)
			if err !=  nil {
				returnSM.MarkErrorMessage(err.Error())
			} else {
				returnSM["passcode"] = account.QuickPassCode
			}
		} else {
			returnSM.MarkErrorMessage(message_ERROR_LOGIN_WRONG_PASSWORD)
		}
	} else {
		returnSM.MarkErrorMessage(message_ERROR_LOGIN_ACCOUNT_NOT_FOUND)
	}

	return returnSM
}
*/

/*
func dbLoginByIdOfGameCenter(idOfGameCenter string) base.SM {
	idOfGameCenter = strings.ToLower(idOfGameCenter)

	account := newBlankAccount()
	returnSM := base.SM{}

	if err := base.DBFindOne(dbName, tableNameAccount, bson.M{"gamecenterid":idOfGameCenter}, account); err == nil {
		didEnsureAccountExist(account, account.QuickPassCodeExpired.Before(time.Now()))

		err = base.DBUpdate(dbName, tableNameAccount, account.Id, account)
		if err !=  nil {
			returnSM.MarkErrorMessage(err.Error())
		} else {
			returnSM["passcode"] = account.QuickPassCode
		}
	} else {
		returnSM.MarkErrorMessage(message_ERROR_LOGIN_ACCOUNT_NOT_FOUND)
	}

	return returnSM
}
*/

func dbLoginByQuickPassCode(passcode string) base.SM {
	sm := base.SM{}
	if len(passcode) > 0 {
		account := newBlankAccount()
		if err := base.DBFindOne(dbName, tableNameAccount, bson.M{"quickpasscode":passcode}, account); err == nil {
			if account.QuickPassCodeExpired.After(time.Now()) {
				extendExpiredPeriod(account, false)

				base.DBUpdate(dbName, tableNameAccount, account.Id, account)
				sm["uuid"] = account.Id.Hex()
				return sm
			}
		}
	}


	sm.MarkErrorMessage(message_ERROR_QUCIK_LOGIN_FAILED)
	return sm
}

func extendExpiredPeriod(accountFound *Account, shouldUpdatePasscode bool) {
	if shouldUpdatePasscode {
		accountFound.QuickPassCode = base.UniqueId()
	}

	accountFound.QuickPassCodeExpired = time.Now().Add(time.Hour * 24 * 7)
}