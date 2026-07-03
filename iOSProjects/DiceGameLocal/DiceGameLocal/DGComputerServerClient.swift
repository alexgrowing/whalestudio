//
//  DGComputerServer.swift
//  DiceGame
//
//  Created by Alex Chen on 15/4/28.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import Foundation
import DiceGameLib

class DGComputerServer : DGGameServer {
    
    
    func createHumanClient() -> DGGameClient {
        self.createComputerClient()
        
        let bothSidesSender = DGClientServerOnSameDeviceMessageSender(server:self)
        
        return DGHumanClient(sender:bothSidesSender)
    }
    
    fileprivate func createComputerClient() {
        let bothSidesSender = DGClientServerOnSameDeviceMessageSender(server:self)

        let computerClient = DGComputerClient(sender:bothSidesSender)
        
        computerClient.notifyServerOfQuickStart()
    }
}

class DGHumanClient : DGGameClient {
    static let UUID_HUMAN = "__human__"
    static let NAME_HUMAN = DGUIUtils.myDevicePlayerName()
    static let FIGURE_HUMAN = DGFigure(isURL: false, path: "")
    
    fileprivate init(sender:DGClientServerOnSameDeviceMessageSender) {
        super.init(uuid:DGHumanClient.UUID_HUMAN, sender:sender)
        sender.client = self
    }
}

class DGComputerClient : DGGameClient, DGActionsOnMessageReceivedFromServer {
    static let UUID_ROBOT = "__robot__"
    static let NAME_ROBOT = NSLocalizedString("Name_Of_Robot", comment:"")
    static let FIGURE_ROBOT = DGFigure(isURL: false, path: "")

    fileprivate var players = [DGPlayer]()
    fileprivate var dicesITossed:[Int] = [Int]()
    fileprivate var guessHistory:[DGGuessHistoryElement] = [DGGuessHistoryElement]()
    
    fileprivate init(sender:DGClientServerOnSameDeviceMessageSender) {
        super.init(uuid: DGComputerClient.UUID_ROBOT, sender: sender)
        sender.client = self
        self.actionsOnMessageReceivedFromServer = self
    }
    
    fileprivate func getPlayerNameByUUID(_ uuid:String) -> String {
        for player in self.players {
            if player.uuid == uuid {
                return player.playerName
            }
        }
        
        return uuid
    }
    
    // MARK: - DGActionsOnMessageReceivedFromServer
    func beNotifiedOfIGotNewCards(_ cardsGot:[String:Int], gold:Int, forReason:String) {
    }
    
    func beNotifiedOfRoomIDNotAvailable(_ roomID:String) {
        
    }
    /*
    func beNotifiedOfMyRoomID(roomID:String, myCards:[String:Int], countOfFullPlayers:Int, playersAlreadyInRoom:[DGPlayer]) {
        for player in playersAlreadyInRoom {
            self.players.append(player)
        }
    }
    func beNotifiedOfSomeoneIntoRoom(player:DGPlayer) {
        self.players.append(player)
    }
    
    func beNotified2StartRound(roundIndex:Int, orderOfPlayers:[String]) {
        self.guessHistory.removeAll(keepCapacity: false)
        self.dicesITossed = DGGameRules.randomDicesTossed()
        self.notifyServerIHaveShakedDice()
    }
 */
    func beNotifiedOfMyRoomID(_ roomID: String) {
        // do nothing
    }
    func beNotified2StartRound(_ roundIndex: Int, myCards: [String : Int], playersInRoom: [DGPlayer]) {
        self.players.removeAll()
        self.players.append(contentsOf: playersInRoom)
        
        self.guessHistory.removeAll(keepingCapacity: false)
        self.dicesITossed = DGGameRules.randomDicesTossed()
        
        DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(5 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) { () -> Void in
            self.notifyServerIHaveShakedDice()
        }
    }
    
    func beNotifiedOfCardUsed(_ typeOfCard:String, sourceUUID:String, targetUUID:[String]) {
        
    }
    
    func beNotifiedOfMyCard2UseNotAvailable(_ message: String) {
        
    }
    
    func beNotifiedOfOneClientHasShakedDice(_ playerUUID: String) {
        // do nothing
    }
    
    func beNotifiedOfOneClient2Guess(_ playerUUID: String) {
        if playerUUID == DGComputerClient.UUID_ROBOT {
            // 要执行这个方法，target必须是NSObject，selector不可以private
            Timer.scheduledTimer(timeInterval: 2, target: self, selector: #selector(DGComputerClient.simulateAsHuman2GiveAGuessOrPointOutLiar), userInfo: nil, repeats: false)
        }
    }
    
    @objc func simulateAsHuman2GiveAGuessOrPointOutLiar() {
        if let suggestGuess = DGGameRules.suggestGuessByHistoryAndDices(self.guessHistory, dices: self.dicesITossed, countOfFullPlayers:self.players.count) {
            self.notifyServerMyGuess(suggestGuess)
        } else {
            self.notifyServerIDoNotBelieve()
        }
    }
    
    func beNotifiedOfGuessByPlayer(_ guess: DGGuess, playerUUID: String, nextPlayerUUID:String) {
        
        let historyEl = DGGuessHistoryElement(guess: guess, uuidOfGuesser: playerUUID, isMyself: playerUUID == DGComputerClient.UUID_ROBOT)
        self.guessHistory.append(historyEl)
        
        self.beNotifiedOfOneClient2Guess(nextPlayerUUID)
    }
    
    func beNotified2OpenCup(_ uuidOfNotBelieveGuy: String) {
        self.notifyServerMyDicesShaked(self.dicesITossed)
    }
    
    func beNotifiedOfRoundResult(_ result: [DGPlayerDicesTossedAndRoundResult]) {
    }
    
    func beNotifiedOfNotMyTurn2Guess() {
        // do nothing
    }
    
    func beNotifiedOfNotTime2PointOutLiar() {
        // do nothing
    }
    
    func beNotifiedOfMyLastGuessIsInvalid(_ invalidMessage: String) {
        // do nothing
    }
    
    func beNotifiedOfOneClientIsReady4NewRound(_ playerUUID: String) {
        // do nothing
        if playerUUID != self.playerUUID {
            self.notifyServerIAmReady4NewRound()
        }
    }
    
    func beNotified2EndGameOfServerCrashed() {
        // do nothing
    }
    
    func beNotified2EndGameOfSomeoneAsk2ExitGame(_ playerUUID: String) {
        // do nothing
    }
    
    func beNotified2EndGameOfSomeoneLostConnectionFromServer(_ playerUUID: String) {
        // do nothing
    }
}

// MARK: - DGClientServerOnSameDeviceMessageSender
class DGClientServerOnSameDeviceMessageSender : DGClientMessageSender, DGMessageSender2Client {
    fileprivate var client:DGGameClient!
    fileprivate let server:DGGameServer
    
    init(server:DGGameServer) {
        self.server = server
    }
    
    func sendData2Server(_ data:[String:AnyObject]) {
        self.server.receiveDataFromClient(data, sender: self)
    }
    
    func sendMessage2Client(_ data: [String:AnyObject]) {
        self.client.receiveDataFromServer(data)
    }
}
