package db

import (
	"errors"
	"time"

	"gopkg.in/mgo.v2/bson"

	"ws/base"
)

const (
	cardTableName      = "card"
	cardUsageTableName = "cardusage"
)

type Card struct {
	Id         bson.ObjectId `bson:"_id"`
	OwnerUUID  string
	TypeOfCard string
	Quantity   int
}

func newBlankCard() *Card {
	return &Card{}
}

func newCard(ownerUUID string, typeOfCard string, quantity int) *Card {
	ret := Card{}

	ret.Id = bson.NewObjectId()
	ret.OwnerUUID = ownerUUID
	ret.TypeOfCard = typeOfCard
	ret.Quantity = quantity

	return &ret
}

type CardUsage struct {
	Id         bson.ObjectId `bson:"_id"`
	UserUUID   string
	TypeOfCard string
	When       time.Time
}

func newCardUsage(userUUID string, typeOfCard string) *CardUsage {
	ret := CardUsage{}

	ret.Id = bson.NewObjectId()
	ret.UserUUID = userUUID
	ret.TypeOfCard = typeOfCard
	ret.When = time.Now()

	return &ret
}

func FindCardsByUUID(playerUUID string) ([]Card, error) {
	var cards []Card
	err := base.DBFindAll(dbName, cardTableName, bson.M{"owneruuid": playerUUID}, &cards)
	return cards, err
}

func UpdateOnNewCardsGotByUUID(playerUUID string, cards map[string]int) error {
	var err error
	for typeOfCard, countOfCards := range cards {
		info := newBlankCard()
		if err = base.DBFindOne(dbName, cardTableName, bson.M{"owneruuid": playerUUID, "typeofcard": typeOfCard}, info); err == nil {
			err = base.DBUpdateId(dbName, cardTableName, info.Id, bson.M{"$inc": bson.M{"quantity": countOfCards}})
		} else {
			newCardInfoRecord := newCard(playerUUID, typeOfCard, countOfCards)
			err = base.DBInsert(dbName, cardTableName, newCardInfoRecord)
		}
	}

	return err
}

func UpdateOnCardUsageByUUID(typeOfCard string, playerUUID string) error {
	info := newBlankCard()
	if err := base.DBFindOne(dbName, cardTableName, bson.M{"owneruuid": playerUUID, "typeofcard": typeOfCard}, info); err == nil {
		if info.Quantity > 0 {
			if err := base.DBUpdateId(dbName, cardTableName, info.Id, bson.M{"$inc": bson.M{"quantity": -1}}); err == nil {
				insertACardUsageRecord(typeOfCard, playerUUID)
				return nil
			} else {
				return err
			}
		} else {
			return errors.New("Not enough card")
		}
	} else {
		return err
	}
}

func insertACardUsageRecord(typeOfCard string, playerUUID string) error {
	cardUsage := newCardUsage(playerUUID, typeOfCard)
	return base.DBInsert(dbName, cardUsageTableName, cardUsage)
}

func SummaryCardUsage() (base.SM, error) {
	ret := base.SM{}
	if allCount, err := base.DBCount(dbName, cardUsageTableName, bson.M{}); err == nil {
		ret["卡片使用总次数"] = allCount
	} else {
		return ret, err
	}
	if dailyCount, err := base.DBCount(dbName, cardUsageTableName, bson.M{"when": bsonOfRegionOf48Hours()}); err == nil {
		ret["N48小时内卡片使用总次数"] = dailyCount
	} else {
		return ret, err
	}

	return ret, nil
}

/*
func GroupDailyCardUsage() ([]base.SM, error) {
	ret := make([]base.SM, 0)

	if session, err := mgo.Dial(dbConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(dbName).C(cardUsageTableName)

		matchO := bson.M{"$match": bson.M{"when": bson.M{"$exists": true}}}
		groupO := bson.M{"$group": bson.M{
			"_id": bson.M{
				"year":     bson.M{"$year": "$when"},
				"month":    bson.M{"$month": "$when"},
				"day":      bson.M{"$dayOfMonth": "$when"},
				"cardtype": "$typeofcard",
			},
			"count": bson.M{"$sum": 1},
		}}
		sortO := bson.M{"$sort": bson.M{
			"_id.year":  -1,
			"_id.month": -1,
			"_id.day":   -1,
		}}
		limitO := bson.M{"$limit": 10}
		pipeOperations := []bson.M{matchO, groupO, sortO, limitO}

		results := []bson.M{}
		if err := c.Pipe(pipeOperations).All(&results); err == nil {
			for _, rt := range results {
				groupByYear := (rt["_id"].(bson.M))["year"].(int)
				groupByMonth := (rt["_id"].(bson.M))["month"].(int)
				groupByDay := (rt["_id"].(bson.M))["day"].(int)
				groupByType := (rt["_id"].(bson.M))["cardtype"].(string)

				groupByDate := strconv.Itoa(groupByYear) + "-" + strconv.Itoa(groupByMonth) + "-" + strconv.Itoa(groupByDay)
				countOfCards := rt["count"].(int)
				ret = append(ret, base.SM{"日期": groupByDate, "卡片类型": groupByType, "卡片数量": countOfCards})
			}

			return ret, nil
		} else {
			return ret, err
		}
	} else {
		return ret, err
	}
}
*/