package land

import (
	"time"

	"gopkg.in/mgo.v2/bson"
	"ws/base"
)

type Account struct {
	Id bson.ObjectId `bson:"_id"`

	UUID        string
	Name        string
	Created     time.Time
	LoginLately time.Time

	Gold              int
	ArmyQuantity      int
	ArmyTrainingLevel int
	Diamond           int

	Training Training

	Free2Rename bool

	SummaryDaysOfLogin          int
	ContinuousDaysOfLoginLately int
}

func newAccount(uuid string, name string) *Account {
	account := Account{}

	account.Id = bson.NewObjectId()
	account.UUID = uuid
	account.Name = name
	account.Created = time.Now()
	account.LoginLately = time.Now()
	account.SummaryDaysOfLogin = 1
	account.ContinuousDaysOfLoginLately = 1

	account.Free2Rename = true

	return &account
}

func (self *Account) isTrainingFinished() bool {
	return self.Training.End.Before(time.Now())
}

func (self *Account) setTrainingFinished() {
	self.ArmyQuantity = self.ArmyQuantity + self.Training.CountOfSoldier
	self.Training.CountOfSoldier = 0
	self.Training.End = time.Now()
}

func newBlankAccount() *Account {
	return &Account{}
}

type Training struct {
	CountOfSoldier int
	Start          time.Time
	End            time.Time
}

func newTraining(countOfSoldier int) Training {
	training := Training{}
	training.CountOfSoldier = countOfSoldier
	training.Start = time.Now()

	countOfTerms := countOfSoldier / COUNT_OF_SOLDIER_TRAINING_PER_MINUTE
	if countOfSoldier%COUNT_OF_SOLDIER_TRAINING_PER_MINUTE > 0 {
		countOfTerms = countOfTerms + 1
	}
	training.End = training.Start.Add(time.Duration(60) * time.Second * time.Duration(countOfTerms))

	return training
}

func (self Training) writeAsJsonable() base.SM {
	/*
		return base.SM{
			"countofsoldier": 100,
			"start":          time.Now().Add(time.Duration(-1000) * time.Second).Unix(),
			"end":            time.Now().Add(time.Duration(100) * time.Second).Unix(),
		}
	*/
	return base.SM{
		"countofsoldier": self.CountOfSoldier,
		"start":          self.Start.Unix(),
		"end":            self.End.Unix(),
	}
}

type Location interface {
	GetLatitude100() int
	GetLongitude100() int
}

type Footprint struct {
	Id bson.ObjectId `bson:"_id"`

	AccountUUID  string
	Latitude100  int
	Longitude100 int
}

func (self Footprint) GetLatitude100() int {
	return self.Latitude100
}

func (self Footprint) GetLongitude100() int {
	return self.Longitude100
}

func (self Footprint) writeAsJsonable() base.SM {
	return base.SM{
		"la": self.Latitude100,
		"lo": self.Longitude100,
	}
}

func newFootprintByJson(playerID string, json map[string]interface{}) *Footprint {
	fp := Footprint{}

	fp.Id = bson.NewObjectId()
	fp.AccountUUID = playerID
	fp.Latitude100 = int(json["la"].(float64))
	fp.Longitude100 = int(json["lo"].(float64))

	return &fp
}

type SimpleFootprint struct {
	Latitude100  int
	Longitude100 int
}

func (self SimpleFootprint) GetLatitude100() int {
	return self.Latitude100
}

func (self SimpleFootprint) GetLongitude100() int {
	return self.Longitude100
}

func newSimpleFootprintByJson(json map[string]interface{}) *SimpleFootprint {
	fp := SimpleFootprint{}

	fp.Latitude100 = int(json["la"].(float64))
	fp.Longitude100 = int(json["lo"].(float64))

	return &fp
}

type Step struct {
	Id bson.ObjectId `bson:"_id"`

	AccountUUID string
	Count       int
	UploadTime  time.Time
}

func newBlankStep() *Step {
	return &Step{}
}

func newStep(playerID string, count int) *Step {
	st := Step{}

	st.Id = bson.NewObjectId()
	st.AccountUUID = playerID
	st.Count = count
	st.UploadTime = time.Now()

	return &st
}

type Territory struct {
	Id bson.ObjectId `bson:"_id"`

	Name         string
	Latitude100  int
	Longitude100 int
	Born         time.Time

	LevelOfTerritory       int
	OccupiedSoldierSeconds int64
	UnixOfLastActivated    int64

	OwnerUUID    string
	ArmyQuantity int

	TreasureSearchable bool
	TimesSearched      int
}

func (self Territory) GetLatitude100() int {
	return self.Latitude100
}

func (self Territory) GetLongitude100() int {
	return self.Longitude100
}

func newBlankTerritory() *Territory {
	return &Territory{}
}

func newWildTerritory(latitude100 int, longitude100 int) *Territory {
	ter := Territory{}
	ter.Id = bson.NewObjectId()
	ter.Latitude100 = latitude100
	ter.Longitude100 = longitude100
	ter.Name = "蛮荒地块"
	ter.Born = time.Now()
	ter.UnixOfLastActivated = ter.Born.Unix()

	ter.LevelOfTerritory = 0
	ter.OwnerUUID = ""
	ter.ArmyQuantity = randomGenerator.Intn(90) + 10

	ter.TreasureSearchable = true

	return &ter
}

func (self *Territory) writeCoordinatAsJsonable() base.SM {
	return base.SM{
		"la": self.Latitude100,
		"lo": self.Longitude100,
	}
}

func (self *Territory) deprecatedWriteCoordinatAsJsonable() base.SM {
	return base.SM{
		"latitude":  self.Latitude100,
		"longitude": self.Longitude100,
	}
}

func (self *Territory) writeAsJsonable() base.SM {
	ret := base.SM{
		"latitude":         self.Latitude100,
		"longitude":        self.Longitude100,
		"name":             self.Name,
		"levelofterritory": self.LevelOfTerritory,
		"armyquantity":     self.ArmyQuantity,

		"owneruuid": "",
		"ownername": "",
		"armylevel": 0,
	}

	if len(self.OwnerUUID) > 0 {
		if account, err := FindAccountByUUID(self.OwnerUUID); err == nil {
			ret["owneruuid"] = account.UUID
			ret["ownername"] = account.Name
			ret["armylevel"] = account.ArmyTrainingLevel
		}
	}

	return ret
}

type MovingArmy struct {
	Id bson.ObjectId `bson:"_id"`

	BelongToUUID        string
	Quantity            int
	TargetLatitude100   int
	TargetLongitude100  int
	StartTime           time.Time
	ArriveTimeEstimated time.Time
}

type Fight struct {
	Id bson.ObjectId `bson:"_id"`

	Occured time.Time

	AttackerUUID         string
	AttackerArmyQuantity int
	AttackerArmyLevel    int
	GoldCost             int

	Latitude100OfTarget  int
	Longitude100OfTarget int

	DefenderUUID           string
	DefenderArmyQuantity   int
	DefenderTerritoryLevel int

	AttackerWins            bool
	QuantityLosesOfWinner   int
	QuantityCaptiveOfWinner int
}

func newFight(attacker *Account, target *Territory, countOfSoldierAttack int, goldCost int, attackerWins bool, countOfSoldierLoseOfWinner int, countOfSoldierCaptivedByWinner int) *Fight {
	fight := Fight{}
	fight.Id = bson.NewObjectId()
	fight.Occured = time.Now()

	fight.AttackerUUID = attacker.UUID
	fight.AttackerArmyQuantity = countOfSoldierAttack
	fight.AttackerArmyLevel = attacker.ArmyTrainingLevel
	fight.GoldCost = goldCost

	fight.Latitude100OfTarget = target.Latitude100
	fight.Longitude100OfTarget = target.Longitude100

	fight.DefenderUUID = target.OwnerUUID
	fight.DefenderArmyQuantity = target.ArmyQuantity
	fight.DefenderTerritoryLevel = target.LevelOfTerritory

	fight.AttackerWins = attackerWins
	fight.QuantityLosesOfWinner = countOfSoldierLoseOfWinner
	fight.QuantityCaptiveOfWinner = countOfSoldierCaptivedByWinner

	return &fight
}

func (self *Fight) writeAsJsonable() base.SM {
	ret := base.SM{
		"lat":               self.Latitude100OfTarget,
		"lon":               self.Longitude100OfTarget,
		"occured":           self.Occured.Unix(),
		"attacker":          "",
		"defender":          "",
		"soldierofattacker": self.AttackerArmyQuantity,
		"soldierofdefender": self.DefenderArmyQuantity,
		"attackerwins":      self.AttackerWins,
		"deathofwinner":     self.QuantityLosesOfWinner,
		"captive":           self.QuantityCaptiveOfWinner,
		"goldcost":          self.GoldCost,
	}

	if len(self.AttackerUUID) > 0 {
		if account, err := FindAccountByUUID(self.AttackerUUID); err == nil {
			ret["attacker"] = account.Name
		}
	}

	if len(self.DefenderUUID) > 0 {
		if account, err := FindAccountByUUID(self.DefenderUUID); err == nil {
			ret["defender"] = account.Name
		}
	}

	return ret
}
