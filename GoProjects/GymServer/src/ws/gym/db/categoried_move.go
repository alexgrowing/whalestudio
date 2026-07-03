package db

import (
	"gopkg.in/mgo.v2/bson"
	"ws/base"
)

const (
	tableNameCategoriedMoves = "categoriedmoves"
)

type DBCategoriedMoves struct {
	Id bson.ObjectId `bson:"_id"`

	IdOfAccount bson.ObjectId
	Details []MovesWithCategory
}

func (self *DBCategoriedMoves) asSM() []base.SM {
	smOfDetails := make([]base.SM, len(self.Details))
	for i, detail := range self.Details {
		smOfDetails[i] = detail.asSM()
	}

	return smOfDetails
}

func (self *DBCategoriedMoves) decode(jsons []interface{}) {
	self.Details = make([]MovesWithCategory, len(jsons))
	for index, jsonOb := range jsons {
		self.Details[index] = *createMovesWithCategory(jsonOb.(map[string]interface{}))
	}
}

func UploadAllCategoriedMoves(accountId bson.ObjectId, jsons []interface{}) {
	base.DBDelete(dbName, tableNameCategoriedMoves, bson.M{"idofaccount":accountId})

	ob := DBCategoriedMoves{}
	ob.Id = bson.NewObjectId()
	ob.IdOfAccount = accountId

	ob.decode(jsons)

	base.DBInsert(dbName, tableNameCategoriedMoves, ob)
}

func DownloadCategoriedMoves(accountId bson.ObjectId) []base.SM {
	ob := DBCategoriedMoves{}
	if err := base.DBFindOne(dbName, tableNameCategoriedMoves, bson.M{"idofaccount":accountId}, &ob); err == nil {
		return ob.asSM()
	}

	return []base.SM{}
}

type MovesWithCategory struct {
	NameOfCategory string
	NameOfMoves []string
}

func (self *MovesWithCategory) asSM() base.SM {
	return base.SM{
		"nameofcategory" : self.NameOfCategory,
		"nameofmoves":self.NameOfMoves,
	}
}

func createMovesWithCategory(json map[string]interface{}) *MovesWithCategory {
	ret := MovesWithCategory{}

	ret.NameOfCategory = json["nameofcategory"].(string)

	tempInterfaces := json["nameofmoves"].([]interface{})
	ret.NameOfMoves = make([]string, len(tempInterfaces))
	for index, interf := range tempInterfaces {
		ret.NameOfMoves[index] = interf.(string)
	}

	return &ret
}


/*
func WriteCategoriedMoves() {
	account := newBlankAccount()

	if err := dbFindOne(accountTableName, bson.M{"email":"18101584@qq.com"}, account); err == nil {
		cm := DBCategoriedMoves{}
		cm.Id = bson.NewObjectId()
		cm.IdOfAccount = account.Id

		mwc1 := MovesWithCategory{}
		mwc1.NameOfCategory = "胸"
		mwc1.NameOfMoves = []string{"sms卧推", "绳索夹胸", "自由卧推"}

		mwc2 := MovesWithCategory{}
		mwc2.NameOfCategory = "臀"
		mwc2.NameOfMoves = []string{"反向哈克", "自由深蹲（臀）", "山羊挺身（臀）"}

		cm.Details = []MovesWithCategory{mwc1, mwc2}

		dbInsert(tableNameCategoriedMoves, cm)
	}
}

func ReadCategoriedMoves() base.SM {
	if session, err := mgo.Dial(dbConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(dbName).C(tableNameCategoriedMoves)

		var allMoves []DBCategoriedMoves
		c.Find(bson.M{}).All(&allMoves)

		for _, t := range allMoves {
			return t.asSM()
		}
	}

	return base.SM{}
}
*/