package game

import (
	"log"
	"time"

	"base"
	"db"
	base2 "ws/base"
)

const (
	keyOP                = "operation"
	keyPLAYER_ID         = "playerid"
	keyPLAYERS           = "players"
	keyTYPE_OF_ROOM = "typeofroom"
	keyONE_PLAYER        = "oneplayer"
	keyROUND_INDEX       = "roundindex"
	keyCARD_INFORMATION  = "cardinformation"
	keyGOLD_GOT          = "goldgot"
	keyTYPE_OF_CARD      = "typeofcard"
	keySOME_PLAYER_UUIDS = "someplayeruuids"
	keyINVALID_MESSAGE   = "invalidmessage"
	keyGUESS             = "guess"
	keyNEXT_PLAYER_ID    = "nextplayerid"
	keyROUND_RESULT      = "roundresult"
	keyREASON            = "reason"

	keyROOM_ID               = "roomid"
	keyCOUNT_OF_FULL_PLAYERS = "countoffullplayers"
	keyPLAYER_UUID           = "uuid"
	keyDICES                 = "dices"
)

const (
	opServer2ClientNewCardsGot        = "yougotreward"
	opServer2ClientRoomIDNotAvailable = "roomidnotavailable"
	opServer2ClientYourRoomID         = "roomid"
	// opServer2ClientSomeoneIntoRoom                       = "someoneintoroom"
	opServer2ClientStartRoundAndShakeDice              = "startround"
	opServer2ClientCardUsed                            = "cardused"
	opServer2ClientCardNotAvailable                    = "cardnotavailable"
	opServer2ClientOneClientHasShakedDice              = "onclienthasshakeddice"
	opServer2ClientOneClientCanGuessDiceNow            = "oneclientcanguessdicenow"
	opServer2ClientItIsNotYourTurn2Guess               = "itisnotyourturn2guess"
	opServer2ClientItIsNotTime2PointOurLiar            = "itisnottime2pointoutliar"
	opServer2ClientYourLastGuessIsNotValid             = "yourlastguessisnotvalid"
	opServer2ClientSomeoneTakeAGuess                   = "someonetakeaguess"
	opServer2ClientSomeoneNotBelieveAndOpenCupNow      = "someonenotbelievetheguessandopencupnow"
	opServer2ClientRoundOverAndResultIsAndGo4NextRound = "roundoverandresultisandgo4nextround"
	opServer2ClientOneClientIsReady4NewRound           = "oneclientisready4newround"

	opServer2ClientEndGameOfServerCrash                  = "endgameofservercrashed"
	opServer2ClientEndGameOfSomeoneLostConnection2Server = "endgameofsomeonelostconnection2server"
	opServer2ClientEndGameOfSomeoneAsk4Exit              = "endgameofsomeoneask4exit"
)

const (
	opClient2ServerQuickStart         = "quickstart"
	opClient2ServerQuickStartOf4      = "quickstart4"
	opClient2ServerRing               = "ring"
	opClient2ServerCreateAPrivateRoom = "createanewroom"
	opClient2ServerGo2APrivateRoom    = "go2aspecifiedroom"
	opClient2ServerIHaveShakedDice    = "ihaveshakeddice"
	opClient2ServerTry2UseCard        = "try2usecard"
	opClient2ServerMyGuessIs          = "myguessis"
	opClient2ServerIDoNotBelieve      = "idonotbelieve"
	opClient2ServerMyDicesAre         = "mydicesare"
	opClient2ServerIAmReady4NewRound  = "iamready4newround"
	opClient2ServerIWant2EndGame      = "iwant2endgame"
)

const TIME_OUT_2_GIVE_A_MINDLESS_GUESS = 12

var notifiedByClient = map[string]func(*DGGameServer, base.MessageSender2Client, map[string]interface{}){

	opClient2ServerQuickStart: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		playerUUID := jsonOb[keyPLAYER_UUID].(string)

		if simplePlayer, err := GetPlayerDBInforByUUID(playerUUID); err == nil {
			cardsOwned := GetPlayerDBCardsByUUID(playerUUID)
			gameServer.quickStart(simplePlayer, cardsOwned, 2, sender)
		} else {
			log.Println(err)
		}
	},

	opClient2ServerQuickStartOf4: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		playerUUID := jsonOb[keyPLAYER_UUID].(string)

		if simplePlayer, err := GetPlayerDBInforByUUID(playerUUID); err == nil {
			cardsOwned := GetPlayerDBCardsByUUID(playerUUID)
			gameServer.quickStart(simplePlayer, cardsOwned, 4, sender)
		} else {
			log.Println(err)
		}
	},

	opClient2ServerRing: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		playerUUID := jsonOb[keyPLAYER_UUID].(string)

		if simplePlayer, err := GetPlayerDBInforByUUID(playerUUID); err == nil {
			cardsOwned := GetPlayerDBCardsByUUID(playerUUID)
			gameServer.ring(simplePlayer, cardsOwned, sender)
		} else {
			log.Println(err)
		}
	},

	opClient2ServerCreateAPrivateRoom: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		playerUUID := jsonOb[keyPLAYER_UUID].(string)

		if simplePlayer, err := GetPlayerDBInforByUUID(playerUUID); err == nil {
			cardsOwned := GetPlayerDBCardsByUUID(playerUUID)
			gameServer.addPlayer2ANewRoom(simplePlayer, cardsOwned, PrivateRoom, 2, sender)
		} else {
			log.Println(err)
		}
	},

	opClient2ServerGo2APrivateRoom: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		playerUUID := jsonOb[keyPLAYER_UUID].(string)
		roomID := jsonOb[keyROOM_ID].(string)

		if simplePlayer, err := GetPlayerDBInforByUUID(playerUUID); err == nil {
			cardsOwned := GetPlayerDBCardsByUUID(playerUUID)
			if !gameServer.addPlayer2RoomByRoomID(true, simplePlayer, cardsOwned, roomID, PrivateRoom, sender) {
				ob := map[string]interface{}{
					keyOP:      opServer2ClientRoomIDNotAvailable,
					keyROOM_ID: roomID,
				}
				sender.Send2Client(base.NewBytesMessage(ob))
			} else {
				// 如果成功进入房间，统计一下
				db.InsertIntoPrivateRoom(playerUUID)
			}
		} else {
			log.Println(err)
		}
	},

	opClient2ServerIHaveShakedDice: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		if room, ok := gameServer.lookupRoomBySender(sender); ok {
			room.beNotifiedOfSomeoneHasShakedDice(readPlayerUUIDFromJsonOB(jsonOb))
		}
	},

	opClient2ServerTry2UseCard: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		if room, ok := gameServer.lookupRoomBySender(sender); ok {
			typeOfCard := readTypeOfCardFromJsonOB(jsonOb)
			sourceUUID := readPlayerUUIDFromJsonOB(jsonOb)
			targetUUID := readSomePlayerUUIDSFromJsonOB(jsonOb)
			room.beNotifiedOfTry2UseCard(typeOfCard, sourceUUID, targetUUID)
		}
	},

	opClient2ServerMyGuessIs: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		if room, ok := gameServer.lookupRoomBySender(sender); ok {
			room.beNotifiedOfGuessOfSomeone(readPlayerUUIDFromJsonOB(jsonOb), readGuessFromJsonOB(jsonOb))
		}
	},

	opClient2ServerIDoNotBelieve: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		if room, ok := gameServer.lookupRoomBySender(sender); ok {
			room.beNotifiedOfSomeoneNotBelieve(readPlayerUUIDFromJsonOB(jsonOb))
		}
	},

	opClient2ServerMyDicesAre: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		if room, ok := gameServer.lookupRoomBySender(sender); ok {
			room.beNotifiedOfDicesOfSomeone(readPlayerUUIDFromJsonOB(jsonOb), readDicesFromJsonOB(jsonOb))
		}
	},

	opClient2ServerIAmReady4NewRound: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		if room, ok := gameServer.lookupRoomBySender(sender); ok {
			room.beNotifiedOfSomeoneReady4NewRound(readPlayerUUIDFromJsonOB(jsonOb))
		}
	},

	opClient2ServerIWant2EndGame: func(gameServer *DGGameServer, sender base.MessageSender2Client, jsonOb map[string]interface{}) {
		if room, ok := gameServer.lookupRoomBySender(sender); ok {
			room.beNotifiedOfSomeoneWant2EndGame(readPlayerUUIDFromJsonOB(jsonOb))
			sender.Shutdown()
		}
	},
}

func readPlayerUUIDFromJsonOB(jsonOb map[string]interface{}) string {
	return jsonOb[keyPLAYER_ID].(string)
}
func readTypeOfCardFromJsonOB(jsonOb map[string]interface{}) string {
	return jsonOb[keyTYPE_OF_CARD].(string)
}
func readSomePlayerUUIDSFromJsonOB(jsonOb map[string]interface{}) []string {
	uuidsOb := jsonOb[keySOME_PLAYER_UUIDS].([]interface{})
	ret := make([]string, len(uuidsOb))
	for index, ob := range uuidsOb {
		ret[index] = ob.(string)
	}

	return ret
}
func readGuessFromJsonOB(jsonOb map[string]interface{}) *DGGuess {
	guessOb := jsonOb[keyGUESS].(map[string]interface{})
	return newDGGuess(int(guessOb["count"].(float64)), int(guessOb["factor"].(float64)))
}
func readDicesFromJsonOB(jsonOb map[string]interface{}) []int {
	dicesOb := jsonOb[keyDICES].([]interface{})
	ret := make([]int, len(dicesOb))
	for index, ob := range dicesOb {
		ret[index] = int(ob.(float64))
	}
	return ret
}

type DGGameServer struct {
	publicRooms  map[string]*DGRoom // roomID:string -> *DGRoom
	privateRooms map[string]*DGRoom // roomID:string -> *DGRoom
	rings        map[string]*DGRoom

	uniqueSenderID2Room4Lookup map[string]*DGRoom // senderID:string -> *DGRoom

	playerUUIDSGotAttendanceAward  []string // 今天已经领取签到奖励的UUID
	playerUUIDSGotPrivateRoomAward []string // 今天已经领取创建私密房间奖励的UUID
	playerUUIDSGotAdAward          []string // 今天已经领取点击广告奖励的UUID
	today                          time.Time
}

func NewDGGameServer() *DGGameServer {
	server := DGGameServer{}
	server.publicRooms = make(map[string]*DGRoom)
	server.privateRooms = make(map[string]*DGRoom)
	server.rings = make(map[string]*DGRoom)

	server.uniqueSenderID2Room4Lookup = make(map[string]*DGRoom)
	server.resetDailyReward()

	return &server
}

func (self *DGGameServer) resetDailyReward() {
	self.today = time.Now()
	self.playerUUIDSGotAttendanceAward = make([]string, 0)
	self.playerUUIDSGotPrivateRoomAward = make([]string, 0)
	self.playerUUIDSGotAdAward = make([]string, 0)
}

func (self *DGGameServer) alreadyGotAdAward(playerUUID string) bool {
	for _, uuid := range self.playerUUIDSGotAdAward {
		if uuid == playerUUID {
			return true
		}
	}

	return false
}

func (self *DGGameServer) alreadyGotAttendanceAward(playerUUID string) bool {
	for _, uuid := range self.playerUUIDSGotAttendanceAward {
		if uuid == playerUUID {
			return true
		}
	}

	return false
}

func (self *DGGameServer) alreadyGotPrivateRoomAward(playerUUID string) bool {
	for _, uuid := range self.playerUUIDSGotPrivateRoomAward {
		if uuid == playerUUID {
			return true
		}
	}

	return false
}

func (self *DGGameServer) shouldResetDayilyReward() bool {
	now := time.Now()

	return now.Year() != self.today.Year() || now.Month() != self.today.Month() || now.Day() != self.today.Day()
}

func (self *DGGameServer) Reward4AdClicked(playerUUID string) {
	if len(playerUUID) == 0 {
		return
	}

	if self.shouldResetDayilyReward() {
		self.resetDailyReward()
	}

	if self.alreadyGotAdAward(playerUUID) {
		return
	}
	self.playerUUIDSGotAdAward = append(self.playerUUIDSGotAdAward, playerUUID)

	go db.UpdateOnNewCardsGotByUUID(playerUUID, map[string]int{
		base.CARD_NAME_RESHAKE: 1,
	})
}

func (self *DGGameServer) reward4AttendanceIfShould(playerUUID string) bool {
	if self.shouldResetDayilyReward() {
		self.resetDailyReward()
	}

	if self.alreadyGotAttendanceAward(playerUUID) {
		return false
	}

	self.playerUUIDSGotAttendanceAward = append(self.playerUUIDSGotAttendanceAward, playerUUID)

	return true
}

func (self *DGGameServer) reward4PlayInPrivateRoomIfShould(playerUUID string) bool {
	if self.shouldResetDayilyReward() {
		self.resetDailyReward()
	}

	if self.alreadyGotPrivateRoomAward(playerUUID) {
		return false
	}

	self.playerUUIDSGotPrivateRoomAward = append(self.playerUUIDSGotPrivateRoomAward, playerUUID)

	return true
}

func (self *DGGameServer) Dispatch(sender base.MessageSender2Client, jsonOb map[string]interface{}) {
	 //log.Println(time.Now(), "\tReceive:", jsonOb)
	notifiedByClient[jsonOb[keyOP].(string)](self, sender, jsonOb)
}

func (self *DGGameServer) LostConnectionOfSessionID(sid string) {
	log.Println("Lost Connection:", sid)
	roomSessionIDBelongTo, ok := self.uniqueSenderID2Room4Lookup[sid]
	if ok {
		roomSessionIDBelongTo.beNotifiedOfSomeoneLostConnection(sid)
	}
}

func (self *DGGameServer) quickStart(simplePlayer *DGPlayer, cardsOwned map[string]int, countOfFullSeats int, sender base.MessageSender2Client) {
	for _, room := range self.publicRooms {
		if room.countOfAvailableSeats == countOfFullSeats && self.addPlayer2Room(true, simplePlayer, cardsOwned, room, sender) {
			return
		}
	}

	self.addPlayer2ANewRoom(simplePlayer, cardsOwned, PublicRoom, countOfFullSeats, sender)
}

func (self *DGGameServer) ring(simplePlayer *DGPlayer, cardsOwned map[string]int, sender base.MessageSender2Client) {
	for _, room := range self.rings {
		if self.addPlayer2Room(true, simplePlayer, cardsOwned, room, sender) {
			return
		}
	}

	self.addPlayer2ANewRoom(simplePlayer, cardsOwned, Ring, 2, sender)
}

func (self *DGGameServer) addPlayer2ANewRoom(simplePlayer *DGPlayer, cardsOwned map[string]int, typeOfRoom RoomTypeEnum, countOfFullSeats int, sender base.MessageSender2Client) string {
	randomString := generateRandomString()

	for {
		_, foundMatchInPublicRooms := self.publicRooms[randomString]
		_, foundMatchInPrivateRooms := self.privateRooms[randomString]
		if !foundMatchInPublicRooms && !foundMatchInPrivateRooms {
			break
		}
		randomString = generateRandomString()
	}

	room := newDGRoom(randomString, countOfFullSeats, typeOfRoom, self)
	switch typeOfRoom {
	case PrivateRoom:
		self.privateRooms[randomString] = room
	case PublicRoom:
		self.publicRooms[randomString] = room

		// 如果新建的是一个public room,有一定概率的,里面已经有机器人在里面了
		for i := 0; i < countOfFullSeats-1; i++ {
			if base2.CreateRandomInt(10) < 5 {
				room.inviteARobot2Play(0)
			}
		}
	case Ring:
		self.rings[randomString] = room
		// 如果是新建一个Ring,要假装是攻一个擂台,所以里面必须要有一个人
		for i := 0; i < countOfFullSeats-1; i++ {
			room.inviteARobot2Play(base2.CreateRandomInt(6) + 1)
		}
	}
	if !self.addPlayer2RoomByRoomID(true, simplePlayer, cardsOwned, randomString, typeOfRoom, sender) {
		return self.addPlayer2ANewRoom(simplePlayer, cardsOwned, typeOfRoom, countOfFullSeats, sender)
	}

	return randomString
}

func (self *DGGameServer) addPlayer2Room(isHuman bool, simplePlayer *DGPlayer, cardsOwned map[string]int, room *DGRoom, sender base.MessageSender2Client) bool {
	// 如果该ID已经在一个房间里,先从这个房间退出来
	if isHuman {
		if roomAlreadyIn, ok := self.lookupRoomBySender(sender); ok {
			log.Println("important:", simplePlayer.playerName, " still in room:", roomAlreadyIn.roomID)
			roomAlreadyIn.beNotifiedOfSomeoneWant2EndGame(simplePlayer.uuid)
		}
	}

	if room.addPlayer(isHuman, simplePlayer, cardsOwned, sender) {
		self.uniqueSenderID2Room4Lookup[sender.UniqueIDOfSender()] = room
		return true
	}
	return false
}

func (self *DGGameServer) addPlayer2RoomByRoomID(isHuman bool, simplePlayer *DGPlayer, cardsOwned map[string]int, roomID string, typeOfRoom RoomTypeEnum, sender base.MessageSender2Client) bool {
	room, ok := self.searchRoomByID(roomID, typeOfRoom)
	if !ok {
		return false
	}

	return self.addPlayer2Room(isHuman, simplePlayer, cardsOwned, room, sender)
}

func (self *DGGameServer) updateSummary2DB() {
	var countOfHumanPlayers = 0
	for _, room := range self.publicRooms {
		if room.isTimeout() {
			log.Println("destroy timeout public room")
			self.destroyRoom(room)
			continue
		}

		for _, player := range room.players {
			if player.isHuman {
				countOfHumanPlayers++
			}
		}
	}

	for _, room := range self.privateRooms {
		if room.isTimeout() {
			log.Println("destroy timeout private room")
			self.destroyRoom(room)
			continue
		}

		for _, player := range room.players {
			if player.isHuman {
				countOfHumanPlayers++
			}
		}
	}

	for _, room := range self.rings {
		if room.isTimeout() {
			log.Println("destroy timeout ring room")
			self.destroyRoom(room)
			continue
		}

		for _, player := range room.players {
			if player.isHuman {
				countOfHumanPlayers++
			}
		}
	}

	db.InsertSummary(len(self.publicRooms), len(self.privateRooms), len(self.rings), countOfHumanPlayers)
}

func (self *DGGameServer) searchRoomByID(roomID string, typeOfRoom RoomTypeEnum) (*DGRoom, bool) {
	switch typeOfRoom {
	case PrivateRoom:
		room, ok := self.privateRooms[roomID]
		return room, ok
	case PublicRoom:
		room, ok := self.publicRooms[roomID]
		return room, ok
	case Ring:
		room, ok := self.rings[roomID]
		return room, ok
	}

	return nil, false
}

func (self *DGGameServer) lookupRoomBySender(sender base.MessageSender2Client) (*DGRoom, bool) {
	room, ok := self.uniqueSenderID2Room4Lookup[sender.UniqueIDOfSender()]

	if ok {
		room.whenLastActive = time.Now()
	}

	return room, ok
}

func (self *DGGameServer) destroyRoom(room *DGRoom) {
	for _, playerInfor := range room.players {
		delete(self.uniqueSenderID2Room4Lookup, playerInfor.sender.UniqueIDOfSender())
	}

	room.releaseResources()

	switch room.typeOfRoom {
	case PrivateRoom:
		delete(self.privateRooms, room.roomID)
	case PublicRoom:
		delete(self.publicRooms, room.roomID)
	case Ring:
		delete(self.rings, room.roomID)
	}
}
