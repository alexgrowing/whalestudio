package account

import (
	"time"
	"strconv"
	"gopkg.in/mgo.v2/bson"
	"math/rand"
	"ws/base"
	"log"
	"errors"
)

const (
	tableNameRegister = "register"

	message_ERROR_VERIFY_CODE_SENT_TOO_FREQUENTLY = "ERROR_VERIFY_CODE_SENT_TOO_FREQUENTLY"
)

var randomGenerator = rand.New(rand.NewSource(time.Now().UnixNano()))

type DBRegister struct {
	Id   bson.ObjectId `bson:"_id"`

	Email string
	VerifyCode string
	Expired time.Time
}

func createVerifyCode4Register(email string) (string, error) {
	if count, err := checkFrequency(email); err == nil {
		if count > 10 {
			return "", errors.New(message_ERROR_VERIFY_CODE_SENT_TOO_FREQUENTLY)
		}
	} else {
		return "", err
	}

	code := strconv.Itoa(randomGenerator.Intn(9000) + 1000)

	register := DBRegister{}
	register.Id = bson.NewObjectId()
	register.Email = email
	register.VerifyCode = code
	register.Expired = time.Now().Add(time.Second * 60)

	return code, base.DBInsert(dbName, tableNameRegister, register)
}

func ensureTimer2DeleteLastDayVerifyCode() {
	go startTimer2DeleteLastDayVerifyCode()
}

func startTimer2DeleteLastDayVerifyCode() {
	deleteLastDayVerifyCode()

	select {
	case <-time.After(24 * time.Hour):
		startTimer2DeleteLastDayVerifyCode()
	}
}

func deleteLastDayVerifyCode() {
	if count, err := base.DBDelete(dbName, tableNameRegister, bson.M{"expired":bson.M{"$lt":time.Now().AddDate(0,0,-1)}}); err == nil {
		log.Print("每天清理验证码信息,删除信息:", count, "条")
	}
}

func checkFrequency(email string) (int, error) {
	return base.DBCount(dbName, tableNameRegister, bson.M{"email":email})
}

func CheckValidationOfEmailAndCode(email string, verifyCode string) bool {

	if count, err := base.DBCount(dbName, tableNameRegister, bson.M{"email":email, "verifycode":verifyCode, "expired":bson.M{"$gte":time.Now()}}); err == nil && count > 0{
		return true
	}

	return false
}
