package db

import (
	"crypto/md5"
	"crypto/rand"
	"encoding/base64"
	"encoding/hex"
	"io"
	"time"

	"gopkg.in/mgo.v2/bson"
	"ws/base"
)

const (
	playerTableName = "player"

	defaultUserName = "Dicer"
)

type Player struct {
	Id   bson.ObjectId `bson:"_id"`
	UUID string
	Name string

	Created  time.Time
	LastPlay time.Time

	Win    int
	Lose   int
	Attack int
	Defend int
	Crown  int
	Gold   int

	SummaryDaysOfLogin          int
	ContinuousDaysOfLoginLately int
}

func newBlankPlayer() *Player {
	return &Player{}
}

func newPlayer(uuid string, name string) *Player {
	ret := Player{}

	ret.Id = bson.NewObjectId()
	ret.UUID = uuid
	ret.Name = name
	ret.Created = time.Now()
	ret.LastPlay = time.Now()

	return &ret
}

func CheckExistanceOfPlayerByUUID(uuid string) (bool, error) {
	if count, err := base.DBCount(dbName, playerTableName, bson.M{"uuid":uuid}); err == nil {
		return count > 0, nil
	} else {
		return false, err
	}
}

func CreateANewPlayerByUUIDAndName(uuid string, name string) (*Player, error) {
	if len(uuid) == 0 {
		uuid = generateUUID()
	}
	if len(name) == 0 {
		name = defaultUserName
	}

	p := newPlayer(uuid, name)


	return p, base.DBInsert(dbName, playerTableName, p)
}

func FindPlayerByUUID(uuid string) (*Player, error) {
	blankPlayer := newBlankPlayer()
	err := base.DBFindOne(dbName, playerTableName, bson.M{"uuid":uuid}, blankPlayer)

	return blankPlayer, err
}

func RenameByUUID(newName string, uuid string) error {
	return base.DBUpdateBson(dbName, playerTableName, bson.M{"uuid": uuid}, bson.M{"$set": bson.M{"name": newName}})
}

func UpdatePlayerOnLoseByUUID(goldLost int, crownModification int, uuid string) error {
	return base.DBUpdateBson(dbName, playerTableName, bson.M{"uuid": uuid}, bson.M{"$inc": bson.M{"gold": -goldLost, "crown": crownModification, "lose": 1}, "$set": bson.M{"lastplay": time.Now()}})
}

func UpdatePlayerOnWinByUUID(goldWin int, attackWin bool, currentDefendWins int, crownModification int, uuid string) error {
	var updateBson bson.M
	if attackWin {
		updateBson = bson.M{"$inc": bson.M{"gold": goldWin, "win": 1, "attack": 1, "crown": crownModification}, "$set": bson.M{"lastplay": time.Now()}}
	} else {
		updateBson = bson.M{"$inc": bson.M{"gold": goldWin, "win": 1, "crown": crownModification}, "$set": bson.M{"lastplay": time.Now()}}
	}
	return base.DBUpdateBson(dbName, playerTableName, bson.M{"uuid": uuid}, updateBson)
}

func UpdatePlayerOnGoldGotByUUID(goldGot int, uuid string) error {
	return base.DBUpdateBson(dbName, playerTableName, bson.M{"uuid": uuid}, bson.M{"$inc": bson.M{"gold": goldGot}})
}

func UpdatePlayerLoginInformation(p *Player) {
	lastPlayTime := p.LastPlay
	now := time.Now()
	yesterday := now.AddDate(0, 0, -1)

	if lastPlayTime.Year() == now.Year() && lastPlayTime.Month() == now.Month() && lastPlayTime.Day() == now.Day() {
		// 如果上次登录时间和当前是同一天
		p.LastPlay = now
	} else if lastPlayTime.Year() == yesterday.Year() && lastPlayTime.Month() == yesterday.Month() && lastPlayTime.Day() == yesterday.Day() {
		// 如果上次登录时间和昨天是同一天
		p.LastPlay = now
		p.SummaryDaysOfLogin = p.SummaryDaysOfLogin + 1
		p.ContinuousDaysOfLoginLately = p.ContinuousDaysOfLoginLately + 1
	} else {
		// 如果上次登录时间是昨天以前
		p.LastPlay = now
		p.SummaryDaysOfLogin = p.SummaryDaysOfLogin + 1
		p.ContinuousDaysOfLoginLately = 1
	}

	base.DBUpdateId(dbName, playerTableName, p.Id, bson.M{"$set": bson.M{"lastplay": p.LastPlay, "summarydaysoflogin": p.SummaryDaysOfLogin, "continuousdaysofloginlately": p.ContinuousDaysOfLoginLately}})
}

func CountOfPlayersIn48Hours() (int, int, error) {
	countOfCreated, err := base.DBCount(dbName, playerTableName, bson.M{"created": bsonOfRegionOf48Hours()})
	countOfLastPlayed, err := base.DBCount(dbName, playerTableName, bson.M{"lastplay": bsonOfRegionOf48Hours()})

	return countOfCreated, countOfLastPlayed, err
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
