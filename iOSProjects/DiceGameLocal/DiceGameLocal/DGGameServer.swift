//
//  DGGameServer.swift
//  DiceGame
//
//  Created by Alex Chen on 15/6/1.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import Foundation
import DiceGameLib

private let DEFAULTS_DATA_I_WIN = "DG_LOCAL_I_WIN"
private let DEFAULTS_DATA_I_LOSE = "DG_LOCAL_I_LOSE"

private let DEFAULTS_DATA_COUNT_OF_CROWN_OF_ME = "DEFAULTS_DATA_COUNT_OF_CROWN_OF_ME"
private let DEFAULTS_DATA_COUNT_OF_CROWN_OF_ROBOT = "DEFAULTS_DATA_COUNT_OF_CROWN_OF_ROBOT"

open class DGGameServer {
    fileprivate let COUNT_OF_FULL_PLAYERS = 2
    
    fileprivate var players = [DGPlayerInformation]()
    fileprivate var indexOfPlayerWhoGaveLastGuess:Int = -1
    fileprivate var guessHistory = [DGGuess]()
    fileprivate var roundIndex:Int = 0
    
    fileprivate var isSendingMessage:Bool = false
    fileprivate var queueOfData2Send = [[String:AnyObject]]()
    fileprivate var queueOfPlayers2Send = [[DGPlayerInformation]]()
    
    func savePlayerInformation(_ uuid:String, messageSender:DGMessageSender2Client) {
        let name:String, figure:DGFigure
        if uuid == DGComputerClient.UUID_ROBOT {
            name = DGComputerClient.NAME_ROBOT
            figure = DGComputerClient.FIGURE_ROBOT
        } else {
            name = DGHumanClient.NAME_HUMAN
            figure = DGHumanClient.FIGURE_HUMAN
        }
        
        if self.players.count < COUNT_OF_FULL_PLAYERS {
            self.players.append(DGPlayerInformation(uuid:uuid, playerName:name, figure:figure, countOfCrown:self.readCountOfCrownByUUID(uuid), sender:messageSender))
        }
        
        if self.players.count == COUNT_OF_FULL_PLAYERS {
            self.notifyPlayersOfNewRoundStarted()
        }
    }
    
    fileprivate func getPlayerInformationByUUID(_ uuid:String) -> DGPlayerInformation? {
        for playerInfor in self.players {
            if playerInfor.uuid == uuid {
                return playerInfor
            }
        }
        
        return nil
    }
    
    // MARK: - Send Data To Client
    fileprivate func sendData2Players(_ data:[String:AnyObject], players:[DGPlayerInformation]) {
        if self.isSendingMessage {
            self.queueOfData2Send.append(data)
            self.queueOfPlayers2Send.append(players)
            return;
        }
        
        self.isSendingMessage = true;
        
        for player in players {
            player.server2ClientSender.sendMessage2Client(data)
        }
        
        if self.queueOfData2Send.count > 0 {
            let lastData2SendInQueue = self.queueOfData2Send.remove(at: 0)
            let lastPlayers2SendInQueue = self.queueOfPlayers2Send.remove(at: 0)
            
            self.isSendingMessage = false
            self.sendData2Players(lastData2SendInQueue, players: lastPlayers2SendInQueue)
        } else {
            self.isSendingMessage = false
        }
    }
    
    fileprivate func sendMessages2Players(_ message:DGMessagesServer2Client, players:[DGPlayerInformation]) {
        self.sendData2Players(message.encode(), players: players)
    }
    
    fileprivate func notifyPlayersOfNewRoundStarted() {
        self.roundIndex += 1
        
        let simplePlayers = self.players.map { (playerInfor) -> DGPlayer in
            return playerInfor.asDGPlayer()
        }
        
        self.players.forEach { (playerOfMessageTarget) in
            self.sendMessages2Players(
                DGMessagesServer2Client.startRound(roundIndex: self.roundIndex, myCards: playerOfMessageTarget.cardOwned, playersInRoom: simplePlayers),
                players: [playerOfMessageTarget]
            )
        }
    }
    
    fileprivate func notifyPlayersOfPlayerHasShakedDice(_ playerUUIDWhoShakedDice:String) {
        self.sendMessages2Players(DGMessagesServer2Client.oneClientHasShakedDice(playerUUIDWhoShakedDice: playerUUIDWhoShakedDice), players: self.players)
    }
    
    fileprivate func notifyNextPlayer2Guess() {
        self.indexOfPlayerWhoGaveLastGuess = (self.indexOfPlayerWhoGaveLastGuess + 1) % COUNT_OF_FULL_PLAYERS
        
        self.sendMessages2Players(DGMessagesServer2Client.oneClientCanGuessDiceNow(playerUUID2GuessDice: self.players[self.indexOfPlayerWhoGaveLastGuess].uuid), players: self.players)
    }
    
    fileprivate func notifyPlayerOfNotHisTurn2Guess(_ playerUUID:String) {
        if let sourcePlayer = self.getPlayerInformationByUUID(playerUUID) {
            self.sendMessages2Players(DGMessagesServer2Client.itIsNotYourTurn2Guess, players: [sourcePlayer])
        }
    }
    
    fileprivate func notifyPlayerOfNotTime2PointOutLiar(_ playerUUID:String) {
        if let sourcePlayer = self.getPlayerInformationByUUID(playerUUID) {
            self.sendMessages2Players(DGMessagesServer2Client.itIsNotTime2PointOutLiar, players: [sourcePlayer])
        }
    }
    
    fileprivate func notifyLastGuessOfInvalidation(_ invalidationMessage:String) {
        self.sendMessages2Players(DGMessagesServer2Client.yourLastGuessIsNotValid(invalidMessage: invalidationMessage), players: [self.players[indexOfPlayerWhoGaveLastGuess]])
    }
    
    fileprivate func notifyPlayerOfInvalidCard2Use(_ messageTarget:DGPlayerInformation, message:String) {
        self.sendMessages2Players(DGMessagesServer2Client.cardNotAvailable(message: message), players: [messageTarget])
    }
    
    fileprivate func notifyPlayersOfSomeoneIsUsingCard(_ typeOfCard:String, sourceUUID:String, targetUUID:[String]) {
        self.sendMessages2Players(DGMessagesServer2Client.cardUsed(typeOfCard: typeOfCard, sourceUUID: sourceUUID, targetUUID: targetUUID), players: self.players)
    }
    
    fileprivate func notifyPlayersOfGuess(_ guess:DGGuess, ofPlayerUUID:String) {
        self.indexOfPlayerWhoGaveLastGuess = (self.indexOfPlayerWhoGaveLastGuess + 1) % COUNT_OF_FULL_PLAYERS
        
        self.sendMessages2Players(DGMessagesServer2Client.someoneTakeAGuess(playerUUID: ofPlayerUUID, guess: guess, nextPlayerUUID:self.players[self.indexOfPlayerWhoGaveLastGuess].uuid), players: self.players)
    }
    
    fileprivate func notifyPlayersOfOpenCup(_ uuidOfNotBelieveGuy:String) {
        self.sendMessages2Players(DGMessagesServer2Client.someoneNotBelieveTheGuessAndOpenCupNow(uuidOfNotBelieveGuy: uuidOfNotBelieveGuy), players: self.players)
    }
    
    fileprivate func notifyPlayersOfRoundResult(_ result:[DGPlayerDicesTossedAndRoundResult]) {
        self.sendMessages2Players(DGMessagesServer2Client.roundOverAndResultIsAndGo4NextRound(result: result), players: self.players)
    }
    
    fileprivate func notifyPlayersOfSomeoneIsReady4NewRound(_ playerUUID:String) {
        self.sendMessages2Players(DGMessagesServer2Client.oneClientIsReady4NewRound(playerUUID: playerUUID), players: self.players)
    }
    
    fileprivate func notifyPlayersEndGameBecauseOfServerCrash() {
        self.sendMessages2Players(DGMessagesServer2Client.endGameOfServerCrashed, players: self.players)
    }
    
    fileprivate func notifyPlayersEndGameBecauseOfSomebodyAskToExitGame(_ playerUUID:String) {
        self.sendMessages2Players(DGMessagesServer2Client.endGameOfSomeoneAsk4Exit(playerUUID: playerUUID), players: self.players)
    }
    
    fileprivate func notifyPlayersEndGameBecauseOfSomebodyLostConnectionFromServer(_ playerUUID:String) {
        self.sendMessages2Players(DGMessagesServer2Client.endGameOfSomeoneLostConnection2Server(playerUUID: playerUUID), players: self.players)
    }
    
    // MARK: - Receive Data From Client
    func receiveDataFromClient(_ data:[String:AnyObject], sender:DGClientServerOnSameDeviceMessageSender) {
        if let message = DGMessagesClient2Server.decodeAsMessagesClient2Server(data) {
            message.triggerServerAction(self, sender: sender)
        }
    }
    
    func beNotifiedOfQuickStart(_ uuid:String, sender:DGClientServerOnSameDeviceMessageSender) {
        self.savePlayerInformation(
            uuid,
            messageSender:sender
        )
    }
    
    func beNotifiedOfSomeoneHasShakedDice(_ playerUUID:String) {
        if let sourcePlayer = self.getPlayerInformationByUUID(playerUUID) {
            var allHaveShakedDice = true
            sourcePlayer.haveShakedDice = true
            for player in self.players {
                if !player.haveShakedDice {
                    allHaveShakedDice = false
                    break
                }
            }
            
            self.notifyPlayersOfPlayerHasShakedDice(playerUUID)

            if allHaveShakedDice {
                self.notifyNextPlayer2Guess()
            }
        }
    }
    
    func beNotifiedOfTry2UseCard(_ typeOfCard:String, sourceUUID:String, targetUUID:[String]) {
        if let sourcePlayer = self.getPlayerInformationByUUID(sourceUUID) {
            if let countOfCard = sourcePlayer.cardOwned[typeOfCard], countOfCard > 0 {
                sourcePlayer.cardOwned[typeOfCard] = countOfCard - 1
                self.notifyPlayersOfSomeoneIsUsingCard(typeOfCard, sourceUUID: sourceUUID, targetUUID: targetUUID)
                
                return
            }
            self.notifyPlayerOfInvalidCard2Use(sourcePlayer, message: "\(typeOfCard) not available")
        }
    }
    
    func beNotifiedOfGuessOfSomeone(_ playerUUID:String, guess:DGGuess) {
        if playerUUID != self.players[self.indexOfPlayerWhoGaveLastGuess].uuid {
            self.notifyPlayerOfNotHisTurn2Guess(playerUUID)
            return
        }
        
        let invalidateMessage = DGGameRules.validateNewGuess(guess, history: self.guessHistory, countOfFullPlayers:COUNT_OF_FULL_PLAYERS)
        switch invalidateMessage {
        case .ok:
            self.guessHistory.append(guess)
            self.notifyPlayersOfGuess(guess, ofPlayerUUID: playerUUID)
        default:
            self.notifyLastGuessOfInvalidation(invalidateMessage.description())
        }
    }
    func beNotifiedOfSomeoneNotBelieve(_ playerUUID:String) {
        if let sourcePlayer = self.getPlayerInformationByUUID(playerUUID) {
            if self.guessHistory.count > 0 {
                sourcePlayer.isNotBelieveGuy = true
                self.notifyPlayersOfOpenCup(playerUUID)
            } else {
                self.notifyPlayerOfNotTime2PointOutLiar(playerUUID)
            }
        }
    }
    func beNotifiedOfDicesOfSomeone(_ playerUUID:String, dices:[Int]) {
        if let sourcePlayer = self.getPlayerInformationByUUID(playerUUID) {
            sourcePlayer.matchedDices = DGGameRules.checkMatchableOfEachDiceByRoundHistory(dices, history: self.guessHistory)
            // 如果不是所有玩家都告知色子数,则return继续等待其他玩家告知色子数
            for player in self.players {
                if player.matchedDices.count == 0 {
                    return
                }
            }
            
            var countOfMatchedDices = 0
            for player in self.players {
                for matchedDice in player.matchedDices {
                    if matchedDice.matched {
                        countOfMatchedDices += 1
                    }
                }
            }
            
            if let lastGuess = self.guessHistory.last {
                let isLastGuessRight = countOfMatchedDices >= lastGuess.count
                var roundResultArray = [DGPlayerDicesTossedAndRoundResult]()
                for player in self.players {
                    let result:DGPlayerDicesTossedAndRoundResult
                    if player.isNotBelieveGuy != isLastGuessRight {
                        let crownModification = self.calculateCrownModification(true, originalCountOfCrown: player.countOfCrown)
                        
                        result = DGPlayerDicesTossedAndRoundResult(uuid:player.uuid, timesOfAllWins:0, timesOfAllAttackWins:0, maxTimesOfAllDefendWins:0,currentCountOfCrowns: player.countOfCrown+crownModification,
                                                                   matchedInforOfDicesTossed: player.matchedDices, crownModification: crownModification, goldModification:0)
                        
                        player.countOfCrown = player.countOfCrown + crownModification
                        self.synchronizeCountOfCrown(player.countOfCrown, byUUID: player.uuid)
                    } else {
                        let crownModification = self.calculateCrownModification(false, originalCountOfCrown: player.countOfCrown)

                        result = DGPlayerDicesTossedAndRoundResult(uuid:player.uuid, timesOfAllWins:0, timesOfAllAttackWins:0, maxTimesOfAllDefendWins:0, currentCountOfCrowns: player.countOfCrown+crownModification,
                                                                   matchedInforOfDicesTossed: player.matchedDices, crownModification: crownModification, goldModification:0)
                        
                        player.countOfCrown = player.countOfCrown + crownModification
                        self.synchronizeCountOfCrown(player.countOfCrown, byUUID: player.uuid)
                    }
                    
                    roundResultArray.append(result)
                }
                
                self.notifyPlayersOfRoundResult(roundResultArray)
            }
        }
    }
    
    fileprivate func calculateCrownModification(_ win:Bool, originalCountOfCrown:Int) -> Int {
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
    
    fileprivate func readCountOfCrownByUUID(_ uuid:String) -> Int {
        let defaults = UserDefaults.standard

        if uuid == DGHumanClient.UUID_HUMAN {
            return defaults.integer(forKey: DEFAULTS_DATA_COUNT_OF_CROWN_OF_ME)
        } else {
            return defaults.integer(forKey: DEFAULTS_DATA_COUNT_OF_CROWN_OF_ROBOT)
        }
    }
    
    fileprivate func synchronizeCountOfCrown(_ countOfCrown:Int, byUUID uuid:String) {
        let defaults = UserDefaults.standard

        if uuid == DGHumanClient.UUID_HUMAN {
            defaults.set(countOfCrown, forKey: DEFAULTS_DATA_COUNT_OF_CROWN_OF_ME)
            if countOfCrown > 0 {
                defaults.set(defaults.integer(forKey: DEFAULTS_DATA_I_WIN) + 1, forKey: DEFAULTS_DATA_I_WIN)
            }
        } else {
            defaults.set(countOfCrown, forKey: DEFAULTS_DATA_COUNT_OF_CROWN_OF_ROBOT)
            if countOfCrown > 0 {
                defaults.set(defaults.integer(forKey: DEFAULTS_DATA_I_LOSE) + 1, forKey: DEFAULTS_DATA_I_LOSE)
            }
        }
        
        defaults.synchronize()
    }
    
    func beNotifiedOfSomeoneReady4NewRound(_ playerUUID:String) {
        if let sourcePlayer = self.getPlayerInformationByUUID(playerUUID) {
            sourcePlayer.isReady4NewRound = true
            
            var allPlayersAreReady = true
            for player in self.players {
                if !player.isReady4NewRound {
                    allPlayersAreReady = false
                    break
                }
            }
            
            if allPlayersAreReady {
                self.reset4NextRound()
                self.notifyPlayersOfNewRoundStarted()
            } else {
                self.notifyPlayersOfSomeoneIsReady4NewRound(playerUUID)
            }
        }
    }
    func beNotifiedOfSomeoneWant2EndGame(_ playerUUID:String) {
        self.notifyPlayersEndGameBecauseOfSomebodyAskToExitGame(playerUUID)
    }
    
    fileprivate func reset4NextRound() {
        for player in self.players {
            player.reset4NewRound()
        }
        
        self.guessHistory.removeAll(keepingCapacity: false)
    }
}


private class DGPlayerInformation {
    fileprivate let uuid:String
    fileprivate let playerName:String
    fileprivate let figure:DGFigure
    fileprivate let server2ClientSender:DGMessageSender2Client
    
    fileprivate var countOfCrown:Int

    fileprivate var cardOwned:[String:Int]
    
    fileprivate var isReady4NewRound = false
    fileprivate var haveShakedDice = false
    fileprivate var isLastGuyGuessed = false
    fileprivate var isNotBelieveGuy = false
    fileprivate var matchedDices = [DGMatchedDiceNumber]()
    
    init(uuid:String, playerName:String, figure:DGFigure, countOfCrown:Int, sender:DGMessageSender2Client) {
        self.uuid = uuid
        self.playerName = playerName
        self.figure = figure
        self.countOfCrown = countOfCrown
        self.cardOwned = [CARD_NAME_RESHAKE:1]
        
        self.server2ClientSender = sender
        
        self.reset4NewRound()
    }
    
    fileprivate func reset4NewRound() {
        self.isReady4NewRound = false
        self.haveShakedDice = false
        self.isLastGuyGuessed = false
        self.isNotBelieveGuy = false
        self.matchedDices.removeAll(keepingCapacity: true)
    }
    
    func asDGPlayer() -> DGPlayer {
        let defaults = UserDefaults.standard
        
        let timesOfAllWins:Int
        if self.uuid == DGHumanClient.UUID_HUMAN {
            timesOfAllWins = defaults.integer(forKey: DEFAULTS_DATA_I_WIN)
        } else {
            timesOfAllWins = defaults.integer(forKey: DEFAULTS_DATA_I_LOSE)
        }
        
        return DGPlayer(uuid: self.uuid, playerName: self.playerName, figure: self.figure, timesOfAllWins: timesOfAllWins, timesOfAllAttackWins: 0, maxTimesOfAllDefendWins: 0, startupRoundScore: 0, countOfAllCrowns: self.countOfCrown)
    }
}

extension DGMessagesClient2Server {
    
    fileprivate func triggerServerAction(_ actions:DGGameServer, sender:DGClientServerOnSameDeviceMessageSender) {
        switch self {
        case let .quickStart(uuid):
            actions.beNotifiedOfQuickStart(uuid, sender:sender)
        case let .iHaveShakedDice(playerUUID):
            actions.beNotifiedOfSomeoneHasShakedDice(playerUUID)
        case let .try2UseCard(typeOfCard, sourceUUID, targetUUID):
            actions.beNotifiedOfTry2UseCard(typeOfCard, sourceUUID:sourceUUID, targetUUID:targetUUID)
        case let .myGuessIs(playerUUID, guess):
            actions.beNotifiedOfGuessOfSomeone(playerUUID, guess: guess)
        case let .iDoNotBelieve(playerUUID):
            actions.beNotifiedOfSomeoneNotBelieve(playerUUID)
        case let .myDicesAre(playerUUID, dices):
            actions.beNotifiedOfDicesOfSomeone(playerUUID, dices: dices)
        case let .iAmReady4NewRound(playerUUID):
            actions.beNotifiedOfSomeoneReady4NewRound(playerUUID)
        case let .iWant2EndGame(playerUUID):
            actions.beNotifiedOfSomeoneWant2EndGame(playerUUID)
        case .quickStart4:
            break
        case .createANewRoom:
            break
        case .go2ASpecifiedRoom:
            break
        case .ring:
            break
        }
    }
}
