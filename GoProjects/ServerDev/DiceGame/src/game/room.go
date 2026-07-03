package game

import (
	"base"
	"database/sql"
	"db"
	"fmt"
	"log"
	"time"
	base2 "ws/base"
)

/*
 * DGRoom
 */
const count_of_dices = 5
const factors_of_dice = 6

type RoomTypeEnum int

const (
	PublicRoom RoomTypeEnum = 1 << iota
	PrivateRoom
	Ring
)

type DGRoom struct {
	countOfAvailableSeats int

	serverBelongTo    *DGGameServer
	roomID            string
	typeOfRoom        RoomTypeEnum
	players           []*DGPlayerInformation
	uuidOfNextGuesser string
	guessHistory      []*DGGuessHistoryElement
	roundIndex        int

	whenLastActive time.Time

	isWaiting2InviteRobot bool
	inviteRobotChannel    chan bool

	isSendingMessage    bool
	queueOfMessagePackage []*DGMessagePackage
}

type DGMessagePackage struct {
	data2Send map[string]interface{}
	players2Send []*DGPlayerInformation
}

func newMessagePackage(data map[string]interface{}, players []*DGPlayerInformation) *DGMessagePackage {
	pack := DGMessagePackage{}
	pack.data2Send = data
	pack.players2Send = players

	return &pack
}

func newDGRoom(roomID string, countOfFullSeats int, typeOfRoom RoomTypeEnum, server *DGGameServer) *DGRoom {
	room := DGRoom{}

	room.countOfAvailableSeats = countOfFullSeats

	room.serverBelongTo = server
	room.roomID = roomID
	room.typeOfRoom = typeOfRoom
	room.players = make([]*DGPlayerInformation, 0)
	room.guessHistory = make([]*DGGuessHistoryElement, 0)

	room.whenLastActive = time.Now()

	room.isSendingMessage = false
	room.queueOfMessagePackage = make([]*DGMessagePackage, 0)

	room.inviteRobotChannel = make(chan bool, 0)
	room.isWaiting2InviteRobot = false

	return &room
}

func (self *DGRoom) releaseResources() {
	self.noNeed2InviteRobot()
}

var TIME_OUT_OF_INACTIVE_ROOM = time.Duration(2) * time.Minute

func (self *DGRoom) isTimeout() bool {
	return time.Now().Sub(self.whenLastActive) > TIME_OUT_OF_INACTIVE_ROOM
}

func (self *DGRoom) noNeed2InviteRobot() {
	if self.isWaiting2InviteRobot {
		self.inviteRobotChannel <- true
		self.isWaiting2InviteRobot = false
	}
}

/*
 * beNotifiedByClient
 */
// return 是否成功加入Room
func (self *DGRoom) addPlayer(isHuman bool, simplePlayer *DGPlayer, cardsOwned map[string]int, sender base.MessageSender2Client) bool {
	if len(self.players) == self.countOfAvailableSeats {
		return false
	}
	// 看一下新要加进去的玩家的ID是不是已经在Room里了
	for _, player := range self.players {
		if player.simplePlayer.uuid == simplePlayer.uuid {
			return false
		}
	}

	playerInfor := newDGPlayerInformation(isHuman, simplePlayer, cardsOwned, sender)
	self.players = append(self.players, playerInfor)

	self.notifyOnNewPlayerIn(simplePlayer.uuid)
	self.beNotifiedOfSomeoneReady4NewRound(simplePlayer.uuid)

	if len(self.players) == self.countOfAvailableSeats {
		go self.serverBelongTo.updateSummary2DB()

		if self.typeOfRoom == PrivateRoom {
			for _, player := range self.players {
				if self.serverBelongTo.reward4PlayInPrivateRoomIfShould(player.simplePlayer.uuid) {
					self.notifyPlayerOfNewRewardGot(player.simplePlayer.uuid, map[string]int{
						base.CARD_NAME_RESHAKE: 1,
					}, 20, "每日私密房间游戏奖励")
				}
			}
		}
	}

	return true
}

func (self *DGRoom) getPlayerInformationByUUID(uuid string) (*DGPlayerInformation, bool) {
	for _, player := range self.players {
		if player.simplePlayer.uuid == uuid {
			return player, true
		}
	}

	return nil, false
}

func (self *DGRoom) waitingRandomSecondsInCaseOfBoring() {
	randomTime2Wait := base2.CreateRandomInt(3)
	self.isWaiting2InviteRobot = true
	select {
	case <-self.inviteRobotChannel:
		break
	case <-time.After(time.Duration(randomTime2Wait) * time.Second):
		self.isWaiting2InviteRobot = false
		self.inviteARobot2Play(0)
	}
}

func (self *DGRoom) inviteARobot2Play(startupScoreOfRound int) {
	// 当执行该方法时,如果该房间里面还只有一个玩家
	if len(self.players) < self.countOfAvailableSeats {
		var exceptionsOfNumberID = make([]string, 0)
		for _, p := range self.players {
			if !p.isHuman {
				exceptionsOfNumberID = append(exceptionsOfNumberID, p.simplePlayer.uuid)
			}
		}

		robot := newRobot(self.serverBelongTo, exceptionsOfNumberID)
		if robot == nil {
			return
		}
		self.serverBelongTo.addPlayer2Room(false, newDGPlayer(robot.mgo.NumberID, robot.mgo.Name, robot.figure, robot.mgo.Win, robot.mgo.Attack, robot.mgo.Defend, robot.mgo.Crown, robot.mgo.Gold, startupScoreOfRound), map[string]int{}, self, robot)
	}
}

func (self *DGRoom) allPlayersAreRobot() bool {
	for _, player := range self.players {
		if player.isHuman {
			return false
		}
	}

	return true
}

func (self *DGRoom) beNotifiedOfSomeoneHasShakedDice(matchPlayerUUID string) {
	if actionPlayer, ok := self.getPlayerInformationByUUID(matchPlayerUUID); ok {
		allHaveShakedDice := true

		actionPlayer.haveShakedDice = true
		for _, player := range self.players {
			if !player.haveShakedDice {
				allHaveShakedDice = false
				break
			}
		}

		self.notifyPlayersOfPlayerHasShakedDice(matchPlayerUUID)

		if allHaveShakedDice {
			self.notifyNextPlayer2Guess()
		}
	}
}

func (self *DGRoom) beNotifiedOfTry2UseCard(typeOfCard string, sourceUUID string, targetUUID []string) {
	if sourcePlayer, ok := self.getPlayerInformationByUUID(sourceUUID); ok {
		if countOfCard, ok := sourcePlayer.cardsOwned[typeOfCard]; ok && countOfCard > 0 {
			sourcePlayer.cardsOwned[typeOfCard] = countOfCard - 1
			self.notifyPlayersOfSomeoneIsUsingCard(typeOfCard, sourceUUID, targetUUID)
			go sourcePlayer.updateOnCardUsed(typeOfCard)

			return
		}

		self.notifyPlayerOfInvalidCard2Use(sourcePlayer, typeOfCard+" not available")
	}
}

func (self *DGRoom) beNotifiedOfGuessOfSomeone(matchPlayerUUID string, guess *DGGuess) {
	if self.isRoundOver() || matchPlayerUUID != self.uuidOfNextGuesser {
		self.notifyPlayerOfNotHisTurn2Guess(matchPlayerUUID)
		return
	}

	ok, message := validNewGuess(guess, self.guessHistory, self.countOfAvailableSeats)
	if ok {
		self.guessHistory = append(self.guessHistory, newGuessHistoryElement(guess, matchPlayerUUID))
		self.notifyPlayersOfGuess(guess, matchPlayerUUID)
	} else {
		self.notifyLastGuessOfInvalidation(message)
	}
}

func (self *DGRoom) beNotifiedOfSomeoneNotBelieve(matchPlayerUUID string) {
	if actionPlayer, ok := self.getPlayerInformationByUUID(matchPlayerUUID); ok {
		if len(self.guessHistory) > 0 && !self.isRoundOver() && self.guessHistory[len(self.guessHistory)-1].guesserUUID != matchPlayerUUID {
			self.roundOver()
			actionPlayer.isNotBelieveGuy = true
			self.notifyPlayersOfOpenCup(matchPlayerUUID)
		} else {
			self.notifyPlayerOfNotTime2PointOutLiar(matchPlayerUUID)
		}
	}
}

func (self *DGRoom) roundOver() {
	self.uuidOfNextGuesser = ""
}

func (self *DGRoom) isRoundOver() bool {
	return len(self.uuidOfNextGuesser) == 0
}

func (self *DGRoom) beNotifiedOfDicesOfSomeone(matchPlayerUUID string, dices []int) {
	if actionPlayer, ok := self.getPlayerInformationByUUID(matchPlayerUUID); ok {
		actionPlayer.matchedDices = checkMatchableOfEachDiceByRoundHistory(dices, self.guessHistory)
		for _, player := range self.players {
			if len(player.matchedDices) == 0 {
				return
			}
		}

		countOfMatchedDices := 0
		for _, player := range self.players {
			for _, matchedDice := range player.matchedDices {
				if matchedDice.matched {
					countOfMatchedDices++
				}
			}
		}

		if len(self.guessHistory) == 0 {
			self.serverBelongTo.destroyRoom(self)
			log.Println("Oh My God, guess history is empty")
			return
		}

		lastGuessHistoryEl := self.guessHistory[len(self.guessHistory)-1]
		lastGuess := lastGuessHistoryEl.guess
		isLastGuessRight := lastGuess.count <= countOfMatchedDices
		roundResultArray := make([]*DGPlayerDicesTossedAndRoundResult, len(self.players))
		var winnerPlayer *DGPlayerInformation
		for index, player := range self.players {
			roundResult := 0 // 0:参与;1:Win;-1:Lose
			crownModification := 0
			goldModification := 0

			if isLastGuessRight {
				if player.isNotBelieveGuy {
					roundResult = -1
				} else if player.simplePlayer.uuid == lastGuessHistoryEl.guesserUUID {
					roundResult = 1
				}
			} else if !isLastGuessRight {
				if player.isNotBelieveGuy {
					roundResult = 1
				} else if player.simplePlayer.uuid == lastGuessHistoryEl.guesserUUID {
					roundResult = -1
				}
			}

			if roundResult == 1 {
				goldModification = 10
				crownModification = self.calculateCrownModification(true, player.simplePlayer.countOfCrowns)
				player.updateOnWin(self, 10, crownModification)

				winnerPlayer = player
			} else if roundResult == -1 {
				goldModification = -10
				crownModification = self.calculateCrownModification(false, player.simplePlayer.countOfCrowns)
				player.updateOnLose(10, crownModification)
			}

			player.simplePlayer.countOfCrowns = player.simplePlayer.countOfCrowns + crownModification

			roundResultArray[index] = newDGPlayerDicesTossedAndRoundResult(
				player.simplePlayer.uuid,
				player.simplePlayer.dbTimesOfAllWins,
				player.simplePlayer.dbTimesOfAllAttackWins,
				player.simplePlayer.dbMaxTimesOfAllDefendWins,
				player.simplePlayer.countOfCrowns,
				player.matchedDices,
				crownModification,
				goldModification,
			)
		}

		self.notifyPlayersOfRoundResult(roundResultArray)
		self.reset4NextRound()

		if self.typeOfRoom == Ring && winnerPlayer != nil {
			if winnerPlayer.isHuman {
				self.players = []*DGPlayerInformation{winnerPlayer}
			} else {
				self.serverBelongTo.destroyRoom(self)
			}
		}
	}
}

func (self *DGRoom) calculateCrownModification(win bool, originalCountOfCrown int) int {
	if win {
		return 30
	} else {
		if originalCountOfCrown > 200 {
			return -30
		} else if originalCountOfCrown > 100 {
			return -15
		} else if originalCountOfCrown > 50 {
			return -5
		} else if originalCountOfCrown > 20 {
			return -3
		} else if originalCountOfCrown > 0 {
			return -1
		} else {
			return 0
		}
	}
}

func (self *DGRoom) beNotifiedOfSomeoneReady4NewRound(matchPlayerUUID string) {
	if actionPlayer, ok := self.getPlayerInformationByUUID(matchPlayerUUID); ok {
		actionPlayer.isReady4NewRound = true

		if len(self.players) == self.countOfAvailableSeats {
			self.noNeed2InviteRobot()

			allPlayersAreReady := true

			for _, player := range self.players {
				if !player.isReady4NewRound {
					allPlayersAreReady = false
					break
				}
			}

			if allPlayersAreReady {
				self.notifyPlayersOfNewRoundStarted()
			} else {
				self.notifyPlayersOfSomeoneIsReady4NewRound(matchPlayerUUID)
			}
		} else if self.typeOfRoom == PublicRoom || self.typeOfRoom == Ring {
			// alex:如果这是一个公开的房间,且该玩家进来后还没法开始游戏
			go self.waitingRandomSecondsInCaseOfBoring()
		}
	}
}

func (self *DGRoom) beNotifiedOfSomeoneWant2EndGame(matchPlayerUUID string) {
	foundMatchedPlayer := false
	newPlayers := make([]*DGPlayerInformation, 0)
	for _, player := range self.players {
		if player.simplePlayer.uuid == matchPlayerUUID {
			foundMatchedPlayer = true
			continue
		}
		newPlayers = append(newPlayers, player)
	}

	if foundMatchedPlayer {
		self.reset4NextRound()

		self.players = newPlayers
		for _, newPlayer := range self.players {
			newPlayer.updateOnWin(self, 10, 0)
		}

		self.notifyPlayersEndGameBecauseOfSomebodyAskToExitGame(matchPlayerUUID)

		if self.typeOfRoom != Ring || self.allPlayersAreRobot() {
			self.serverBelongTo.destroyRoom(self)
		}
	}
}

func (self *DGRoom) beNotifiedOfSomeoneLostConnection(sessionIDOfPlayer string) {
	newPlayers := make([]*DGPlayerInformation, 0)
	var playerUUIDWhoLostConnection string
	for _, playerInfor := range self.players {
		if playerInfor.sender.UniqueIDOfSender() == sessionIDOfPlayer {
			playerUUIDWhoLostConnection = playerInfor.simplePlayer.uuid
		} else {
			newPlayers = append(newPlayers, playerInfor)
		}
	}

	if len(playerUUIDWhoLostConnection) > 0 {
		self.reset4NextRound()

		self.players = newPlayers
		for _, newPlayer := range self.players {
			newPlayer.updateOnWin(self, 10, 0)
		}

		self.notifyPlayersEndGameBecauseOfSomebodyLostConnectionFromServer(playerUUIDWhoLostConnection)

		if self.typeOfRoom != Ring || self.allPlayersAreRobot() {
			self.serverBelongTo.destroyRoom(self)
		}
	}
}

func (self *DGRoom) reset4NextRound() {
	for _, player := range self.players {
		player.reset4NextRound()
	}

	self.releaseResources()
	self.guessHistory = make([]*DGGuessHistoryElement, 0)
}

/*
 * sendMessages2Client
 */
func (self *DGRoom) sendData2Players(data map[string]interface{}, players []*DGPlayerInformation) {
	if self.isSendingMessage {
		self.queueOfMessagePackage = append(self.queueOfMessagePackage, newMessagePackage(data, players))
		return
	}

	self.isSendingMessage = true
	mess := base.NewBytesMessage(data)
	for _, playerInfor := range players {
		//log.Println(time.Now(), "\tSending to ", playerInfor.simplePlayer.playerName, ":", data)

		go playerInfor.sender.Send2Client(mess)
	}

	lenOfQueue := len(self.queueOfMessagePackage)
	if lenOfQueue > 0 {
		first := self.queueOfMessagePackage[0]
		self.queueOfMessagePackage = self.queueOfMessagePackage[1:]

		self.isSendingMessage = false
		self.sendData2Players(first.data2Send, first.players2Send)
	} else {
		self.isSendingMessage = false
	}
}

func (self *DGRoom) notifyPlayerOfNewRewardGot(targetPlayerUUID string, cardsGot map[string]int, goldGot int, reason string) {
	if targetPlayer, ok := self.getPlayerInformationByUUID(targetPlayerUUID); ok {
		go targetPlayer.updateOnNewCardsGot(cardsGot)
		go targetPlayer.updateOnGoldGot(goldGot)

		self.sendData2Players(map[string]interface{}{
			keyOP:               opServer2ClientNewCardsGot,
			keyCARD_INFORMATION: cardsGot,
			keyGOLD_GOT:         goldGot,
			keyREASON:           reason,
		}, []*DGPlayerInformation{targetPlayer})
	}
}

func (self *DGRoom) notifyOnNewPlayerIn(newPlayerUUID string) {
	if playerInfor, ok := self.getPlayerInformationByUUID(newPlayerUUID); ok {
		self.sendData2Players(map[string]interface{}{
			keyOP:      opServer2ClientYourRoomID,
			keyROOM_ID: self.roomID,
			keyTYPE_OF_ROOM:self.typeOfRoom,
		}, []*DGPlayerInformation{playerInfor})

		if self.serverBelongTo.reward4AttendanceIfShould(newPlayerUUID) {
			self.notifyPlayerOfNewRewardGot(newPlayerUUID, map[string]int{
				base.CARD_NAME_RESHAKE: 1,
			}, 10, "每日签到奖励")
		}
	} else {
		fmt.Println("not ok")
	}
}

/*
func (self *DGRoom) notifyOnNewPlayerIn(newPlayerUUID string) {
	for _, player := range self.players {
		if player.simplePlayer.uuid == newPlayerUUID {
			self.notifyNewPlayerOfRoomID(newPlayerUUID)
		} else {
			self.notifyOldPlayerOfNewPlayer(player.simplePlayer.uuid, newPlayerUUID)
		}
	}
}

func (self *DGRoom) notifyNewPlayerOfRoomID(newPlayerUUID string) {
	if playerInfor, ok := self.getPlayerInformationByUUID(newPlayerUUID); ok {
		jsonablePlayersAlreadyInRoom := make([]map[string]interface{}, len(self.players))
		for index, playerInfor := range self.players {
			jsonablePlayersAlreadyInRoom[index] = playerInfor.simplePlayer.writeAsJsonable()
		}

		self.sendData2Players(map[string]interface{}{
			keyOP:                    opServer2ClientYourRoomID,
			keyROOM_ID:               self.roomID,
			keyCARD_INFORMATION:      playerInfor.cardsOwned,
			keyCOUNT_OF_FULL_PLAYERS: self.countOfAvailableSeats,
			keyPLAYERS:               jsonablePlayersAlreadyInRoom,
		}, []*DGPlayerInformation{playerInfor})

		if self.serverBelongTo.reward4AttendanceIfShould(newPlayerUUID) {
			self.notifyPlayerOfNewRewardGot(newPlayerUUID, map[string]int{
				base.CARD_NAME_RESHAKE: 1,
			}, 10, "每日签到奖励")
		}
	}
}

func (self *DGRoom) notifyOldPlayerOfNewPlayer(oldPlayerUUID string, newPlayerUUID string) {
	if messageTargetPlayerInfor, ok := self.getPlayerInformationByUUID(oldPlayerUUID); ok {
		if newPlayerPlayerInfor, ok := self.getPlayerInformationByUUID(newPlayerUUID); ok {
			self.sendData2Players(map[string]interface{}{
				keyOP:         opServer2ClientSomeoneIntoRoom,
				keyONE_PLAYER: newPlayerPlayerInfor.simplePlayer.writeAsJsonable(),
			}, []*DGPlayerInformation{messageTargetPlayerInfor})
		}
	}
}
*/

func (self *DGRoom) notifyPlayersOfSomeoneIsReady4NewRound(playerUUID string) {
	self.sendData2Players(map[string]interface{}{
		keyOP:        opServer2ClientOneClientIsReady4NewRound,
		keyPLAYER_ID: playerUUID,
	}, self.players)
}

func (self *DGRoom) notifyPlayersOfNewRoundStarted() {
	/*
	 * 在开始新回合时,检查一下,是不是剩下的都是机器人了,如果是的话,就不玩了
	 */
	if self.allPlayersAreRobot() {
		self.notifyPlayersEndGameBecauseOfServerCrash()
		return
	}

	go self.saveRoundInformation2DB()

	self.roundIndex++

	jsonablePlayersOfRoom := make([]map[string]interface{}, len(self.players))
	for index, playerInfor := range self.players {
		jsonablePlayersOfRoom[index] = playerInfor.simplePlayer.writeAsJsonable()
	}

	for _, player := range self.players {
		self.sendData2Players(map[string]interface{}{
			keyOP:               opServer2ClientStartRoundAndShakeDice,
			keyROUND_INDEX:      self.roundIndex,
			keyCARD_INFORMATION: player.cardsOwned,
			keyPLAYERS:          jsonablePlayersOfRoom,
		}, []*DGPlayerInformation{player})
	}
}

func (self *DGRoom) saveRoundInformation2DB() {
	countOfHuman := 0
	countOfRobot := 0
	for _, player := range self.players {
		if player.isHuman {
			countOfHuman++
		} else {
			countOfRobot++
		}
	}

	typeOfRoomAsString := "public"
	if self.typeOfRoom == PrivateRoom {
		typeOfRoomAsString = "private"
	} else if self.typeOfRoom == Ring {
		typeOfRoomAsString = "ring"
	}

	if err := db.InsertRoundSummary(countOfHuman, countOfRobot, self.roomID, typeOfRoomAsString); err == nil {
		// do nothing
	} else {
		log.Println("execute error:", err)
	}
}
func (self *DGRoom) notifyPlayersOfPlayerHasShakedDice(playerUUIDWhoShakedDice string) {
	self.sendData2Players(map[string]interface{}{
		keyOP:        opServer2ClientOneClientHasShakedDice,
		keyPLAYER_ID: playerUUIDWhoShakedDice,
	}, self.players)
}
func (self *DGRoom) changeIndexOfPlayerWhoGaveLastGuess() {
	if len(self.players) == 0 {
		return
	}

	indexOfLastGuesser := -1
	for index, p := range self.players {
		if p.simplePlayer.uuid == self.uuidOfNextGuesser {
			indexOfLastGuesser = index
			break
		}
	}

	nextIndex := (indexOfLastGuesser + 1) % len(self.players)
	self.uuidOfNextGuesser = self.players[nextIndex].simplePlayer.uuid
}
func (self *DGRoom) notifyPlayersOfSomeoneIsUsingCard(typeOfCard string, sourceUUID string, targetUUID []string) {
	self.sendData2Players(map[string]interface{}{
		keyOP:                opServer2ClientCardUsed,
		keyTYPE_OF_CARD:      typeOfCard,
		keyPLAYER_ID:         sourceUUID,
		keySOME_PLAYER_UUIDS: targetUUID,
	}, self.players)
}
func (self *DGRoom) notifyPlayerOfInvalidCard2Use(messageTarget *DGPlayerInformation, message string) {
	self.sendData2Players(map[string]interface{}{
		keyOP:              opServer2ClientCardNotAvailable,
		keyINVALID_MESSAGE: message,
	}, []*DGPlayerInformation{messageTarget})
}
func (self *DGRoom) notifyNextPlayer2Guess() {
	self.changeIndexOfPlayerWhoGaveLastGuess()

	self.sendData2Players(map[string]interface{}{
		keyOP:        opServer2ClientOneClientCanGuessDiceNow,
		keyPLAYER_ID: self.uuidOfNextGuesser,
	}, self.players)
}
func (self *DGRoom) notifyPlayerOfNotHisTurn2Guess(playerUUID string) {
	if targetPlayer, ok := self.getPlayerInformationByUUID(playerUUID); ok {
		self.sendData2Players(map[string]interface{}{
			keyOP: opServer2ClientItIsNotYourTurn2Guess,
		}, []*DGPlayerInformation{targetPlayer})
	}
}
func (self *DGRoom) notifyPlayerOfNotTime2PointOutLiar(playerUUID string) {
	if targetPlayer, ok := self.getPlayerInformationByUUID(playerUUID); ok {
		self.sendData2Players(map[string]interface{}{
			keyOP: opServer2ClientItIsNotTime2PointOurLiar,
		}, []*DGPlayerInformation{targetPlayer})
	}
}
func (self *DGRoom) notifyLastGuessOfInvalidation(invalidMessage string) {
	if player2Notify, ok := self.getPlayerInformationByUUID(self.uuidOfNextGuesser); ok {
		self.sendData2Players(map[string]interface{}{
			keyOP:              opServer2ClientYourLastGuessIsNotValid,
			keyINVALID_MESSAGE: invalidMessage,
		}, []*DGPlayerInformation{player2Notify})
	}
}
func (self *DGRoom) notifyPlayersOfGuess(guess *DGGuess, ofPlayerUUID string) {
	self.changeIndexOfPlayerWhoGaveLastGuess()

	self.sendData2Players(map[string]interface{}{
		keyOP:             opServer2ClientSomeoneTakeAGuess,
		keyPLAYER_ID:      ofPlayerUUID,
		keyGUESS:          guess.writeAsJsonable(),
		keyNEXT_PLAYER_ID: self.uuidOfNextGuesser,
	}, self.players)
}

func (self *DGRoom) notifyPlayersOfOpenCup(uuidOfNotBelieveGuy string) {
	self.sendData2Players(map[string]interface{}{
		keyOP:        opServer2ClientSomeoneNotBelieveAndOpenCupNow,
		keyPLAYER_ID: uuidOfNotBelieveGuy,
	}, self.players)
}
func (self *DGRoom) notifyPlayersOfRoundResult(result []*DGPlayerDicesTossedAndRoundResult) {
	jsonableResult := make([]map[string]interface{}, len(result))
	for index, playerDicesTossedAndRoundResult := range result {
		jsonableResult[index] = playerDicesTossedAndRoundResult.writeAsJsonable()
	}

	self.sendData2Players(map[string]interface{}{
		keyOP:           opServer2ClientRoundOverAndResultIsAndGo4NextRound,
		keyROUND_RESULT: jsonableResult,
	}, self.players)
}

func (self *DGRoom) notifyPlayersEndGameBecauseOfServerCrash() {
	self.sendData2Players(map[string]interface{}{
		keyOP: opServer2ClientEndGameOfServerCrash,
	}, self.players)

	self.serverBelongTo.destroyRoom(self)
}
func (self *DGRoom) notifyPlayersEndGameBecauseOfSomebodyAskToExitGame(playerUUID string) {
	self.sendData2Players(map[string]interface{}{
		keyOP:        opServer2ClientEndGameOfSomeoneAsk4Exit,
		keyPLAYER_ID: playerUUID,
	}, self.players)
}

func (self *DGRoom) notifyPlayersEndGameBecauseOfSomebodyLostConnectionFromServer(playerUUIDWhoLostConnection string) {
	self.sendData2Players(map[string]interface{}{
		keyOP:        opServer2ClientEndGameOfSomeoneLostConnection2Server,
		keyPLAYER_ID: playerUUIDWhoLostConnection,
	}, self.players)
}

type DGPlayerInformation struct {
	isHuman      bool
	simplePlayer *DGPlayer
	/*
		playerUUID                string
		playerName                string
		figure                    *DGFigure
		dbTimesOfAllWins          int
		dbTimesOfAllAttackWins    int
		dbMaxTimesOfAllDefendWins int
		timesWinOfRound int
	*/

	sender base.MessageSender2Client

	cardsOwned map[string]int

	isReady4NewRound bool
	haveShakedDice   bool
	isLastGuyGuessed bool
	isNotBelieveGuy  bool
	matchedDices     []*DGMatchedDiceNumber

	isOnline bool
}

func newDGPlayerInformation(isHuman bool, simplePlayer *DGPlayer, cardsOwned map[string]int, sender base.MessageSender2Client) *DGPlayerInformation {
	ret := DGPlayerInformation{}
	ret.isHuman = isHuman
	ret.simplePlayer = simplePlayer
	ret.sender = sender

	ret.cardsOwned = cardsOwned

	ret.isOnline = true

	return &ret
}

func (self *DGPlayerInformation) reset4NextRound() {
	self.isReady4NewRound = false
	self.haveShakedDice = false
	self.isLastGuyGuessed = false
	self.isNotBelieveGuy = false
	self.matchedDices = make([]*DGMatchedDiceNumber, 0)
}

func (self *DGPlayerInformation) updateOnWin(roomBelongTo *DGRoom, goldWin int, crownModification int) {
	self.simplePlayer.timesOfRoundWins++
	self.simplePlayer.dbTimesOfAllWins++

	var attackWin = false
	var currentDefendWins = 0
	if roomBelongTo.typeOfRoom == Ring {
		if self.simplePlayer.timesOfRoundWins == 1 {
			self.simplePlayer.dbTimesOfAllAttackWins++
			attackWin = true
		} else {
			currentDefendWins = self.simplePlayer.timesOfRoundWins - 1
			if self.simplePlayer.dbMaxTimesOfAllDefendWins < self.simplePlayer.timesOfRoundWins-1 {
				self.simplePlayer.dbMaxTimesOfAllDefendWins = self.simplePlayer.timesOfRoundWins - 1
			}
		}
	}

	if self.isHuman {
		db.UpdatePlayerOnWinByUUID(goldWin, attackWin, currentDefendWins, crownModification, self.simplePlayer.uuid)
	} else {
		db.UpdateRobotOnWinByUUID(goldWin, attackWin, currentDefendWins, crownModification, self.simplePlayer.uuid)
	}
}

func (self *DGPlayerInformation) updateOnLose(goldLose int, crownModification int) {
	if self.isHuman {
		db.UpdatePlayerOnLoseByUUID(goldLose, crownModification, self.simplePlayer.uuid)
	} else {
		db.UpdateRobotOnLoseByUUID(goldLose, crownModification, self.simplePlayer.uuid)
	}
}

func (self *DGPlayerInformation) updateOnCardUsed(typeOfCard string) {
	if self.isHuman {
		db.UpdateOnCardUsageByUUID(typeOfCard, self.simplePlayer.uuid)
	}
}

func (self *DGPlayerInformation) updateOnNewCardsGot(cards map[string]int) {
	if self.isHuman {
		db.UpdateOnNewCardsGotByUUID(self.simplePlayer.uuid, cards)
	}
}

func (self *DGPlayerInformation) updateOnGoldGot(gold int) {
	if self.isHuman {
		db.UpdatePlayerOnGoldGotByUUID(gold, self.simplePlayer.uuid)
	} else {
		db.UpdateRobotOnGoldGotByUUID(gold, self.simplePlayer.uuid)
	}
}

func (self *DGPlayerInformation) updateOnGoldUsed(db *sql.DB, gold int) {

}

type DGPlayer struct {
	uuid                      string
	playerName                string
	figure                    *DGFigure
	dbTimesOfAllWins          int
	dbTimesOfAllAttackWins    int
	dbMaxTimesOfAllDefendWins int
	timesOfRoundWins          int
	countOfCrowns             int
	gold                      int
}

func (self *DGPlayer) writeAsJsonable() map[string]interface{} {
	ret := map[string]interface{}{
		"uuid":                      self.uuid,
		"playername":                self.playerName,
		"dbtimesofallwins":          float64(self.dbTimesOfAllWins),
		"dbtimesofallattackwins":    float64(self.dbTimesOfAllAttackWins),
		"dbmaxtimesofalldefendwins": float64(self.dbMaxTimesOfAllDefendWins),
		"timesofroundwins":          float64(self.timesOfRoundWins),
		"countofallcrowns":          float64(self.countOfCrowns),
		"gold":                      float64(self.gold),
	}

	// 不明什么原因uuid在数据库中会找不到,导致figure为nil
	if self.figure != nil {
		ret["figure"] = self.figure.writeAsJsonable()
	}

	return ret
}

func newDGPlayerByMap(json map[string]interface{}) *DGPlayer {
	var figure *DGFigure = nil
	figureOb := json["figure"]
	if figureOb != nil {
		figure = newDGFigureByMap(figureOb.(map[string]interface{}))
	}

	return newDGPlayer(
		json["uuid"].(string),
		json["playername"].(string),
		figure,
		int(json["dbtimesofallwins"].(float64)),
		int(json["dbtimesofallattackwins"].(float64)),
		int(json["dbmaxtimesofalldefendwins"].(float64)),
		int(json["timesofroundwins"].(float64)),
		int(json["countofallcrowns"].(float64)),
		int(json["gold"].(float64)),
	)
}

func newDGPlayer(uuid string, playerName string, figure *DGFigure, dbTimesOfAllWins int, dbTimesOfAllAttackWins int, dbMaxTimesOfAllDefendWins int, countOfCrowns int, gold int, timesOfRoundWins int) *DGPlayer {
	ret := DGPlayer{}
	ret.uuid = uuid
	ret.playerName = playerName
	ret.figure = figure
	ret.dbTimesOfAllWins = dbTimesOfAllWins
	ret.dbTimesOfAllAttackWins = dbTimesOfAllAttackWins
	ret.dbMaxTimesOfAllDefendWins = dbMaxTimesOfAllDefendWins
	ret.timesOfRoundWins = timesOfRoundWins
	ret.countOfCrowns = countOfCrowns
	ret.gold = gold

	return &ret
}

type DGFigure struct {
	isURL bool
	path  string
}

func (self *DGFigure) writeAsJsonable() map[string]interface{} {
	return map[string]interface{}{
		"isurl": self.isURL,
		"path":  self.path,
	}
}

func newDGFigureByMap(json map[string]interface{}) *DGFigure {
	return newDGFigure(json["isurl"].(bool), json["path"].(string))
}

func newDGFigure(isURL bool, path string) *DGFigure {
	ret := DGFigure{}
	ret.isURL = isURL
	ret.path = path
	return &ret
}

type DGGuess struct {
	count  int
	factor int
}

func (self *DGGuess) writeAsJsonable() map[string]interface{} {
	return map[string]interface{}{
		"count":  float64(self.count), // todo 因为json.Marshal和unMarshal之后，所有数值都变成了float64，这里不强转成float64的话，Robot传过去的值在服务器那边拿到的就是int，与Web环境下就不一样了
		"factor": float64(self.factor),
	}
}
func newDGGuess(count int, factor int) *DGGuess {
	ret := DGGuess{}
	ret.count = count
	ret.factor = factor
	return &ret
}
func newDGGuessByMap(ob map[string]interface{}) *DGGuess {
	return newDGGuess(int(ob["count"].(float64)), int(ob["factor"].(float64)))
}

type DGMatchedDiceNumber struct {
	diceNumber int
	matched    bool
}

func newDGMatchedDiceNumber(diceNumber int, matched bool) *DGMatchedDiceNumber {
	ret := DGMatchedDiceNumber{}
	ret.diceNumber = diceNumber
	ret.matched = matched

	return &ret
}

func (self *DGMatchedDiceNumber) writeAsJsonable() map[string]interface{} {
	return map[string]interface{}{
		"dicenumber": self.diceNumber,
		"matched":    self.matched,
	}
}

type DGPlayerDicesTossedAndRoundResult struct {
	uuid                      string
	dbTimesOfAllWins          int
	dbTimesOfAllAttackWins    int
	dbMaxTimesOfAllDefendWins int
	dbCurrentCountOfCrowns    int

	matchedInforOfDicesTossed []*DGMatchedDiceNumber
	crownModification         int
	goldModification          int
}

func newDGPlayerDicesTossedAndRoundResult(
	uuid string,
	dbTimesOfAllWins int,
	dbTimesOfAllAttackWins int,
	dbMaxTimesOfAllDefendWins int,
	dbCountOfCrown int,
	matchedDices []*DGMatchedDiceNumber,
	crownModification int,
	goldModification int,
) *DGPlayerDicesTossedAndRoundResult {
	ret := DGPlayerDicesTossedAndRoundResult{}
	ret.matchedInforOfDicesTossed = matchedDices
	ret.goldModification = goldModification
	ret.crownModification = crownModification

	ret.uuid = uuid
	ret.dbTimesOfAllWins = dbTimesOfAllWins
	ret.dbTimesOfAllAttackWins = dbTimesOfAllAttackWins
	ret.dbMaxTimesOfAllDefendWins = dbMaxTimesOfAllDefendWins
	ret.dbCurrentCountOfCrowns = dbCountOfCrown

	return &ret
}

func (self *DGPlayerDicesTossedAndRoundResult) writeAsJsonable() map[string]interface{} {
	jsonableMatchedDiceNumber := make([]map[string]interface{}, len(self.matchedInforOfDicesTossed))
	for index, matchedDiceNumber := range self.matchedInforOfDicesTossed {
		jsonableMatchedDiceNumber[index] = matchedDiceNumber.writeAsJsonable()
	}

	return map[string]interface{}{
		"uuid":                      self.uuid,
		"timesofallwins":            self.dbTimesOfAllWins,
		"timesofallattackwins":      self.dbTimesOfAllAttackWins,
		"maxtimesofalldefendwins":   self.dbMaxTimesOfAllDefendWins,
		"currentcountofcrowns":      self.dbCurrentCountOfCrowns,
		"matchedinforofdicestossed": jsonableMatchedDiceNumber,
		"crownmodification":         self.crownModification,
		"goldmodification":          self.goldModification,
	}
}

type DGGuessHistoryElement struct {
	guess       *DGGuess
	guesserUUID string
}

func newGuessHistoryElement(guess *DGGuess, guesser string) *DGGuessHistoryElement {
	el := DGGuessHistoryElement{}
	el.guess = guess
	el.guesserUUID = guesser

	return &el
}
