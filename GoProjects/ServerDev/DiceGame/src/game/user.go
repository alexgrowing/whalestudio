package game

import (
	"crypto/md5"
	"crypto/rand"
	"db"
	"encoding/base64"
	"encoding/hex"
	"io"
	"sync"
	"ws/base/account"
	"base"
)

type AccountListener struct {

}

func(self *AccountListener) AccountFound(account * account.Account) {
	ensurePlayerBy(account.Nickname, account.Id.Hex())
}

var mutex sync.Mutex

//var lock = make(chan bool, 1)

func RegisterUserDirectly(name string, uuid string) (*db.Player, error) {
	if len(name) == 0 {
		name = "anonymous"
	}
	mutex.Lock()
	defer mutex.Unlock()

	return ensurePlayerBy(name, uuid)
}

func GetPlayerDBInforByUUID(uuid string) (*DGPlayer, error) {
	playerFound, err := db.FindPlayerByUUID(uuid)
	if err != nil {
		return nil, err
	}

	return newDGPlayer(
		playerFound.UUID,
		playerFound.Name,
		newDGFigure(true, base.GetFigureURLOfPlayer(playerFound.UUID)),
		playerFound.Win,
		playerFound.Attack,
		playerFound.Defend,
		playerFound.Crown,
		playerFound.Gold,
		0,
	), nil
}

func GetPlayerDBCardsByUUID(uuid string) map[string]int {
	var ret = map[string]int{}

	if cards, err := db.FindCardsByUUID(uuid); err == nil {
		for _, c := range cards {
			ret[c.TypeOfCard] = c.Quantity
		}
	}

	return ret
}

/*
 * 1.没有传uuid，根据name，创建一个uuid
 * 2.传了uuid，但是uuid在当前DB中没有，那么就拿这个uuid和name作为新的一个player吧
 * 3.传了uuid，并且uuid有效，更新name
 */
func ensurePlayerBy(name string, uuid string) (*db.Player, error) {
	// 1.没有传uuid，根据name，创建一个uuid
	if len(uuid) == 0 {
		return createAUUID(name)
	}

	if playerFound, err := db.FindPlayerByUUID(uuid); err == nil {
		return playerFound, nil
	} else {
		return db.CreateANewPlayerByUUIDAndName(uuid, name)
	}
}

func createAUUID(name string) (*db.Player, error) {
	newUUID := generateUUID()

	found, _ := db.CheckExistanceOfPlayerByUUID(newUUID)

	if found {
		// 居然这个newUUID有重的，只能重新createAUUID了
		return createAUUID(name)
	} else {
		return db.CreateANewPlayerByUUIDAndName(newUUID, name)
	}
}

func generateUUID() string {
	bytes := make([]byte, 48)
	if _, err := io.ReadFull(rand.Reader, bytes); err != nil {
		return ""
	}
	return "DICE[" + md5Encode(base64.URLEncoding.EncodeToString(bytes)) + "]"
}

func md5Encode(in string) string {
	h := md5.New()
	h.Write([]byte(in))
	return hex.EncodeToString(h.Sum(nil))
}
