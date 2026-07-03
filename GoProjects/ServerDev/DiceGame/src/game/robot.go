package game

import (
	"db"
	"log"
	"time"
	"base"
	base2 "ws/base"
	"sync"
)

/*
 * 这个方法不需要再支持可执行了
func InitialAllRobots2DB() {
	bytes, err := ioutil.ReadFile("resources/robotnames.txt")
	if err != nil {
		log.Println("read file error:", err)
		panic(err)
	}

	robotNameLongString := string(bytes)
	robotNames := strings.Split(robotNameLongString, " ")

	db, err := getGlobalDB()

	for _, name := range robotNames {
		_, err := db.Exec("insert into ROBOT (name, win, lose, steak, available) values('" + name + "',0,0,0,1)")

		if err != nil {
			log.Println("execute error:", err)
		}
	}
}
*/

type DGRobot struct {
	serverBelongTo *DGGameServer
	mgo            *db.Robot
	figure         *DGFigure

	room *DGRoom

	roundPlayers      []*DGPlayer
	roundDicesITossed []int
	roundGuessHistory []*DGGuessHistoryElement

	state4Debug string

	isWaitingNewMessage bool
	patientChannel chan bool
	patient int
}

var lock4VisitRobotsWorking *sync.Mutex = new(sync.Mutex)
var robotsWorking = make([]*DGRobot, 0)

func syncAppendRobot2Working(robot *DGRobot) {
	lock4VisitRobotsWorking.Lock()
	defer lock4VisitRobotsWorking.Unlock()

	robotsWorking = append(robotsWorking, robot)
}

func syncRemoveRobotFromWorking(robot *DGRobot) {
	lock4VisitRobotsWorking.Lock()
	defer lock4VisitRobotsWorking.Unlock()

	indexOfRobot := __indexOfWorkingRobots__(robot)

	if indexOfRobot >= 0 {
		robotsWorking = append(robotsWorking[:indexOfRobot], robotsWorking[indexOfRobot + 1:]...)
	}
}

func syncIndexOfWorkingRobots(theRobot *DGRobot) int {
	lock4VisitRobotsWorking.Lock()
	defer lock4VisitRobotsWorking.Unlock()

	return __indexOfWorkingRobots__(theRobot);
}

func __indexOfWorkingRobots__(theRobot *DGRobot) int {
	for index, robot := range robotsWorking {
		if robot == theRobot {
			return index
		}
	}

	return -1
}

func informationOfRobotsMemory() map[string]int {
	ret := make(map[string]int)

	for _, robot := range robotsWorking {
		stateOfRobot := robot.state4Debug
		if count, found := ret[stateOfRobot]; found {
			ret[stateOfRobot] = count + 1
		} else {
			ret[stateOfRobot] = 1
		}
	}

	return ret
}

func newRobot(server *DGGameServer, exceptionsOfNumberID []string) *DGRobot {
	if mgoRobot, err := db.FindRobotByRandom(exceptionsOfNumberID); err == nil {
		robot := DGRobot{}
		robot.serverBelongTo = server
		robot.mgo = mgoRobot

		robot.figure = newDGFigure(true, base.GetFigureURLOfRobot(robot.mgo.NumberID))
		robot.state4Debug = "i am born"

		robot.isWaitingNewMessage = false
		robot.patientChannel = make(chan bool, 0)
		robot.patient = base2.CreateRandomInt(15) + 30

		syncAppendRobot2Working(&robot)

		return &robot
	} else {
		return nil
	}
}

func (self *DGRobot) relax() {
	syncRemoveRobotFromWorking(self)
}

/*
 * implements MessageSender2Client
 */
func (self *DGRobot) Send2Client(message *base.DGBytesMessage) {
	self.noNeed2WaitNewMessage()

	jsonOb := message.OriginalMessage
	notifiedByServer[jsonOb[keyOP].(string)](self, jsonOb)

	if syncIndexOfWorkingRobots(self) >= 0 {
		self.waitingNewMessageOrEndGame()
	}
}

func (self *DGRobot) UniqueIDOfSender() string {
	return "Robot[" + self.mgo.NumberID + "]"
}

func (self *DGRobot) Shutdown() {
	//self.noNeed2WaitNewMessage()
	//self.relax()

}

func (self *DGRobot) noNeed2WaitNewMessage() {
	if self.isWaitingNewMessage {
		self.patientChannel <- true // to stop waiting2EndGame
		self.isWaitingNewMessage = false
	}
}

func (self *DGRobot) waitingNewMessageOrEndGame() {
	if self.isWaitingNewMessage {
		return
	}
	self.isWaitingNewMessage = true

	go func() {
		select {
		case <- self.patientChannel:
			break
		case <- time.After(time.Duration(self.patient) * time.Second):
			log.Println(self.UniqueIDOfSender(), ":i do not want to wait now")
			self.notifyServerIWant2EndGame()
		}
	}()
}

/*
 * Notified By Server
 */
func (self *DGRobot) beNotifiedOfMyRoomID(roomID string) {
	self.room = self.findRoomByID(roomID)
}

func (self *DGRobot) findRoomByID(roomID string) *DGRoom {
	if roomFound, ok := self.serverBelongTo.searchRoomByID(roomID, PublicRoom); ok {
		return roomFound
	}
	if roomFound, ok := self.serverBelongTo.searchRoomByID(roomID, Ring); ok {
		return roomFound
	}

	return nil
}

func (self *DGRobot) beNotified2StartRound(roundIndex int, playersInRoom []*DGPlayer) {
	self.roundPlayers = playersInRoom

	self.roundGuessHistory = make([]*DGGuessHistoryElement, 0)
	self.roundDicesITossed = randomDicesTossed()

	time.Sleep(time.Duration(base2.CreateRandomInt(4)+6) * time.Second)

	self.notifyServerIHaveShakedDice()
}

func (self *DGRobot) beNotifiedOfOneClient2Guess(playerUUID string) {
	if playerUUID == self.mgo.NumberID {
		if self.room == nil {
			log.Println("my room is broken!! my id:", self.UniqueIDOfSender(), " and my name:", self.mgo.Name)
			self.notifyServerIWant2EndGame()
			return
		}
		suggestGuess := suggestGuessByHistoryAndDices(self.roundGuessHistory, self.roundDicesITossed, self.room.countOfAvailableSeats)
		time.Sleep(time.Duration(base2.CreateRandomInt(5)+1) * time.Second)

		if suggestGuess != nil {
			self.notifyServerMyGuess(suggestGuess)
		} else {
			self.notifyServerIDoNotBelieve()
		}
	}
}

func (self *DGRobot) beNotifiedOfGuessByPlayer(guess *DGGuess, playerUUID string, nextPlayerUUID string) {
	historyEl := newGuessHistoryElement(guess, playerUUID)
	self.roundGuessHistory = append(self.roundGuessHistory, historyEl)

	self.beNotifiedOfOneClient2Guess(nextPlayerUUID)
}

func (self *DGRobot) beNotified2OpenCup(uuidOfNotBelieveGuy string) {
	time.Sleep(time.Duration(base2.CreateRandomInt(3)+1) * time.Second)

	self.notifyServerMyDicesShaked(self.roundDicesITossed)
}

func (self *DGRobot) beNotifiedOfRoundResult() {
	// 如果是擂台赛,不管是输是赢,都relax
	if self.room.typeOfRoom == Ring {
		self.relax()
	} else {
		time.Sleep(time.Duration(base2.CreateRandomInt(5)+12) * time.Second)

		self.notifyServerIAmReady4NewRound()
	}
}

func (self *DGRobot) beNotifiedOfOneClientIsReady4NewRound(playerUUID string) {

}

var notifiedByServer = map[string]func(*DGRobot, map[string]interface{}){
	opServer2ClientNewCardsGot: func(robot *DGRobot, message map[string]interface{}) {

	},
	opServer2ClientRoomIDNotAvailable: func(robot *DGRobot, message map[string]interface{}) {

	},
	opServer2ClientYourRoomID: func(robot *DGRobot, message map[string]interface{}) {
		/*
			jsonablePlayers := message[keyPLAYERS].([]map[string]interface{})
			players := make([]*DGPlayer, len(jsonablePlayers))
			for index, json := range jsonablePlayers {
				players[index] = newDGPlayerByMap(json)
			}
		*/
		robot.beNotifiedOfMyRoomID(message[keyROOM_ID].(string))
	},
	opServer2ClientStartRoundAndShakeDice: func(robot *DGRobot, message map[string]interface{}) {
		jsonablePlayers := message[keyPLAYERS].([]map[string]interface{})
		players := make([]*DGPlayer, len(jsonablePlayers))
		for index, json := range jsonablePlayers {
			players[index] = newDGPlayerByMap(json)
		}

		robot.beNotified2StartRound(message[keyROUND_INDEX].(int), players)
	},
	opServer2ClientOneClientHasShakedDice: func(robot *DGRobot, message map[string]interface{}) {

	},
	opServer2ClientCardUsed: func(robot *DGRobot, message map[string]interface{}) {

	},
	opServer2ClientCardNotAvailable: func(robot *DGRobot, message map[string]interface{}) {

	},
	opServer2ClientOneClientCanGuessDiceNow: func(robot *DGRobot, message map[string]interface{}) {
		robot.beNotifiedOfOneClient2Guess(message[keyPLAYER_ID].(string))
	},
	opServer2ClientItIsNotYourTurn2Guess: func(robot *DGRobot, message map[string]interface{}) {

	},
	opServer2ClientItIsNotTime2PointOurLiar: func(robot *DGRobot, message map[string]interface{}) {

	},
	opServer2ClientYourLastGuessIsNotValid: func(robot *DGRobot, message map[string]interface{}) {

	},
	opServer2ClientSomeoneTakeAGuess: func(robot *DGRobot, message map[string]interface{}) {
		robot.beNotifiedOfGuessByPlayer(newDGGuessByMap(message[keyGUESS].(map[string]interface{})), message[keyPLAYER_ID].(string), message[keyNEXT_PLAYER_ID].(string))
	},
	opServer2ClientSomeoneNotBelieveAndOpenCupNow: func(robot *DGRobot, message map[string]interface{}) {
		robot.beNotified2OpenCup(message[keyPLAYER_ID].(string))
	},
	opServer2ClientRoundOverAndResultIsAndGo4NextRound: func(robot *DGRobot, message map[string]interface{}) {
		robot.beNotifiedOfRoundResult()
	},
	opServer2ClientOneClientIsReady4NewRound: func(robot *DGRobot, message map[string]interface{}) {
		robot.beNotifiedOfOneClientIsReady4NewRound(message[keyPLAYER_ID].(string))
	},
	opServer2ClientEndGameOfServerCrash: func(robot *DGRobot, message map[string]interface{}) {
		//log.Println(robot.UniqueIDOfSender(), " be notified of server crash")
		robot.relax()
	},
	opServer2ClientEndGameOfSomeoneLostConnection2Server: func(robot *DGRobot, message map[string]interface{}) {
		//log.Println(robot.UniqueIDOfSender(), " be notified of someone lost connection")
		robot.relax()
	},
	opServer2ClientEndGameOfSomeoneAsk4Exit: func(robot *DGRobot, message map[string]interface{}) {
		//log.Println(robot.UniqueIDOfSender(), " be notified of someone ask to exit")
		robot.relax()
	},
}

/*
 * Notify Server Some Stuff
 */
func (self *DGRobot) notifyServerIHaveShakedDice() {
	self.serverBelongTo.Dispatch(self, map[string]interface{}{
		keyOP:        opClient2ServerIHaveShakedDice,
		keyPLAYER_ID: self.mgo.NumberID,
	})

	self.state4Debug = "i have shaked my dice"
}

func (self *DGRobot) notifyServerMyGuess(myGuess *DGGuess) {
	self.serverBelongTo.Dispatch(self, map[string]interface{}{
		keyOP:        opClient2ServerMyGuessIs,
		keyGUESS:     myGuess.writeAsJsonable(),
		keyPLAYER_ID: self.mgo.NumberID,
	})

	self.state4Debug = "my guess is"
}

func (self *DGRobot) notifyServerIDoNotBelieve() {
	self.serverBelongTo.Dispatch(self, map[string]interface{}{
		keyOP:        opClient2ServerIDoNotBelieve,
		keyPLAYER_ID: self.mgo.NumberID,
	})

	self.state4Debug = "i do not believe"
}

func (self *DGRobot) notifyServerMyDicesShaked(myDices []int) {
	// todo 因为json.Marshal和unMarshal，要把[]int转成[]interface{}，并且里面的值是float64
	myDicesInterface := make([]interface{}, len(myDices))
	for index, dice := range myDices {
		myDicesInterface[index] = float64(dice)
	}

	self.serverBelongTo.Dispatch(self, map[string]interface{}{
		keyOP:        opClient2ServerMyDicesAre,
		keyPLAYER_ID: self.mgo.NumberID,
		keyDICES:     myDicesInterface,
	})

	self.state4Debug = "after show my dices"
}

func (self *DGRobot) notifyServerIAmReady4NewRound() {
	self.serverBelongTo.Dispatch(self, map[string]interface{}{
		keyOP:        opClient2ServerIAmReady4NewRound,
		keyPLAYER_ID: self.mgo.NumberID,
	})
	self.state4Debug = "i am ready 4 new round"
}

func (self *DGRobot) notifyServerIWant2EndGame() {
	self.serverBelongTo.Dispatch(self, map[string]interface{}{
		keyOP:        opClient2ServerIWant2EndGame,
		keyPLAYER_ID: self.mgo.NumberID,
	})

	self.state4Debug = "i want to end game"
}
