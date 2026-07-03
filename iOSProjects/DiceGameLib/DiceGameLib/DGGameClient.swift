//
//  DGGameServer.swift
//  DiceGame
//
//  Created by Alex Chen on 15/4/24.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import Foundation

public protocol DGMessageSender2Client {
    func sendMessage2Client(_ data:[String:AnyObject])
}

enum DGKeysOfMessages {
    static let OP = "operation"
    static let PLAYER_ID = "playerid"
    static let NEXT_PLAYER_ID = "nextplayerid"
    static let ONE_PLAYER = "oneplayer"
    static let PLAYERS = "players"
    static let SOME_PLAYER_UUIDS = "someplayeruuids"
    static let ROUND_INDEX = "roundindex"
    static let CARD_INFORMATION = "cardinformation"
    static let GOLD_GOT = "goldgot"
    static let TYPE_OF_CARD = "typeofcard"
    static let INVALID_MESSAGE = "invalidmessage"
    static let REASON = "reason"
    static let GUESS = "guess"
    static let ROUND_RESULT = "roundresult"
    
    static let ROOM_ID = "roomid"
    static let COUNT_OF_FULL_PLAYERS = "countoffullplayers"
    static let PLAYER_UUID = "uuid"
    static let DICES = "dices"
}

// MARK: - MessageServer2ClientBuilder
class DGMessagesServer2ClientBuiler {
    fileprivate static var All = [
        DGMessagesServer2ClientBuiler(
            operationString:"yougotreward", instanceBuilder: {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.youGetCards(
                    cardsGot: data[DGKeysOfMessages.CARD_INFORMATION] as! [String:Int],
                    goldGot:data[DGKeysOfMessages.GOLD_GOT] as! Int,
                    reason: data[DGKeysOfMessages.REASON] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString:"roomidnotavailable", instanceBuilder: {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.roomIDNotAvailable(
                    roomID:data[DGKeysOfMessages.ROOM_ID] as! String
                )
            }
        ),
        
        /*
        DGMessagesServer2ClientBuiler(
            operationString: "yourroomid",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.YourRoomID(
                    roomID:data[DGKeysOfMessages.ROOM_ID] as! String,
                    myCards:data[DGKeysOfMessages.CARD_INFORMATION] as! [String:Int],
                    countOfFullPlayers:data[DGKeysOfMessages.COUNT_OF_FULL_PLAYERS] as! Int,
                    playersAlreadyInRoom:(data[DGKeysOfMessages.PLAYERS] as! [[String:AnyObject]]).map() {
                        return DGPlayer(dict:$0)
                    }
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "someoneintoroom", instanceBuilder: {
                (data:[String : AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.SomeoneIntoRoom(
                    player:DGPlayer(dict:data[DGKeysOfMessages.ONE_PLAYER] as! [String:AnyObject])
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "startroundandshakedice",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.StartRoundAndShakeDice(
                    orderOfPlayers:data[DGKeysOfMessages.SOME_PLAYER_UUIDS] as! [String],
                    roundIndex:data[DGKeysOfMessages.ROUND_INDEX] as! Int
                )
            }
        ),
*/
        DGMessagesServer2ClientBuiler(
            operationString: "roomid",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.roomID(
                    roomID:data[DGKeysOfMessages.ROOM_ID] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "startround",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.startRound(
                    roundIndex:data[DGKeysOfMessages.ROUND_INDEX] as! Int,
                    myCards:data[DGKeysOfMessages.CARD_INFORMATION] as! [String:Int],
                    playersInRoom:(data[DGKeysOfMessages.PLAYERS] as! [[String:AnyObject]]).map() {
                        return DGPlayer(dict:$0)
                    }
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "cardused",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.cardUsed(
                    typeOfCard: data[DGKeysOfMessages.TYPE_OF_CARD] as! String,
                    sourceUUID: data[DGKeysOfMessages.PLAYER_ID] as! String,
                    targetUUID: data[DGKeysOfMessages.SOME_PLAYER_UUIDS] as! [String]
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "cardnotavailable",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.cardNotAvailable(
                    message:data[DGKeysOfMessages.INVALID_MESSAGE] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "onclienthasshakeddice", instanceBuilder: {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.oneClientHasShakedDice(
                    playerUUIDWhoShakedDice:data[DGKeysOfMessages.PLAYER_ID] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "oneclientcanguessdicenow",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.oneClientCanGuessDiceNow(
                    playerUUID2GuessDice:data[DGKeysOfMessages.PLAYER_ID] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "itisnotyourturn2guess",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.itIsNotYourTurn2Guess
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "itisnottime2pointoutliar", instanceBuilder: {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.itIsNotTime2PointOutLiar
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "yourlastguessisnotvalid",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.yourLastGuessIsNotValid(
                    invalidMessage:data[DGKeysOfMessages.INVALID_MESSAGE] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "someonetakeaguess",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.someoneTakeAGuess(
                    playerUUID:data[DGKeysOfMessages.PLAYER_ID] as! String,
                    guess:DGGuess(dict:data[DGKeysOfMessages.GUESS] as! [String:AnyObject]),
                    nextPlayerUUID:data[DGKeysOfMessages.NEXT_PLAYER_ID] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "someonenotbelievetheguessandopencupnow", instanceBuilder: {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.someoneNotBelieveTheGuessAndOpenCupNow(
                    uuidOfNotBelieveGuy: data[DGKeysOfMessages.PLAYER_ID] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "roundoverandresultisandgo4nextround",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.roundOverAndResultIsAndGo4NextRound(
                    result:(data[DGKeysOfMessages.ROUND_RESULT] as! [[String:AnyObject]]).map() {
                        return DGPlayerDicesTossedAndRoundResult(dict:$0)
                    }
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "oneclientisready4newround",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.oneClientIsReady4NewRound(
                    playerUUID:data[DGKeysOfMessages.PLAYER_ID] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "endgameofservercrashed",  instanceBuilder : {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.endGameOfServerCrashed
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "endgameofsomeonelostconnection2server", instanceBuilder: {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.endGameOfSomeoneLostConnection2Server(
                    playerUUID:data[DGKeysOfMessages.PLAYER_ID] as! String
                )
            }
        ),
        
        DGMessagesServer2ClientBuiler(
            operationString: "endgameofsomeoneask4exit", instanceBuilder: {
                (data:[String:AnyObject]) -> DGMessagesServer2Client in
                DGMessagesServer2Client.endGameOfSomeoneAsk4Exit(
                    playerUUID:data[DGKeysOfMessages.PLAYER_ID] as! String
                )
            }
        )
    ]
    
    fileprivate let operationString : String
    fileprivate let instanceBuilder : ([String:AnyObject]) -> DGMessagesServer2Client
    
    init(operationString : String, instanceBuilder : @escaping ([String:AnyObject]) -> DGMessagesServer2Client) {
        self.operationString = operationString
        self.instanceBuilder = instanceBuilder
    }
}

// MARK: - MessageServer2Client
public enum DGMessagesServer2Client {
    case youGetCards(cardsGot:[String:Int], goldGot:Int, reason:String)
    case roomIDNotAvailable(roomID:String)
    /*
    case YourRoomID(roomID:String, myCards:[String:Int], countOfFullPlayers:Int,playersAlreadyInRoom:[DGPlayer]/*self included*/)
    case SomeoneIntoRoom(player:DGPlayer)
    case StartRoundAndShakeDice(orderOfPlayers:[String], roundIndex:Int)
 */
    case roomID(roomID:String)
    case startRound(roundIndex:Int, myCards:[String:Int], playersInRoom:[DGPlayer]/*self included*/)
    case cardUsed(typeOfCard:String, sourceUUID:String, targetUUID:[String])
    case cardNotAvailable(message:String)
    case oneClientHasShakedDice(playerUUIDWhoShakedDice:String)
    case oneClientCanGuessDiceNow(playerUUID2GuessDice:String)
    case itIsNotYourTurn2Guess
    case itIsNotTime2PointOutLiar
    case yourLastGuessIsNotValid(invalidMessage:String)
    case someoneTakeAGuess(playerUUID:String, guess:DGGuess, nextPlayerUUID:String)
    case someoneNotBelieveTheGuessAndOpenCupNow(uuidOfNotBelieveGuy:String)
    case roundOverAndResultIsAndGo4NextRound(result:[DGPlayerDicesTossedAndRoundResult])
    case oneClientIsReady4NewRound(playerUUID:String)
    case endGameOfServerCrashed
    case endGameOfSomeoneLostConnection2Server(playerUUID:String)
    case endGameOfSomeoneAsk4Exit(playerUUID:String)
    
    public func encode() -> [String:AnyObject] {
        var dic = [String:AnyObject]()
        dic.updateValue(self.builder().operationString as AnyObject, forKey: DGKeysOfMessages.OP)
        
        switch self {
        case let .youGetCards(cardsGot, goldGot, reason):
            dic.updateValue(cardsGot as AnyObject, forKey:DGKeysOfMessages.CARD_INFORMATION)
            dic.updateValue(reason as AnyObject, forKey:DGKeysOfMessages.REASON)
            dic.updateValue(goldGot as AnyObject, forKey:DGKeysOfMessages.GOLD_GOT)
        case let .roomIDNotAvailable(roomID):
            dic.updateValue(roomID as AnyObject, forKey:DGKeysOfMessages.ROOM_ID)
            /*
        case let .YourRoomID(roomID, myCards, countOfFullPlayers, playersAlreadyInRoom):
            dic.updateValue(roomID, forKey:DGKeysOfMessages.ROOM_ID)
            dic.updateValue(myCards, forKey: DGKeysOfMessages.CARD_INFORMATION)
            dic.updateValue(countOfFullPlayers, forKey:DGKeysOfMessages.COUNT_OF_FULL_PLAYERS)
            dic.updateValue(playersAlreadyInRoom.map({
                return $0.encodeAsDictionary()
            }), forKey:DGKeysOfMessages.PLAYERS)
            
        case let .SomeoneIntoRoom(player):
            dic.updateValue(player.encodeAsDictionary(), forKey: DGKeysOfMessages.ONE_PLAYER)
            
        case let .StartRoundAndShakeDice(orderOfPlayers, roundIndex):
            dic.updateValue(orderOfPlayers, forKey: DGKeysOfMessages.SOME_PLAYER_UUIDS)
            dic.updateValue(roundIndex, forKey: DGKeysOfMessages.ROUND_INDEX)
            */
        case let .roomID(roomID):
            dic.updateValue(roomID as AnyObject, forKey:DGKeysOfMessages.ROOM_ID)
        case let .startRound(roundIndex, myCards, playersInRoom):
            dic.updateValue(roundIndex as AnyObject, forKey: DGKeysOfMessages.ROUND_INDEX)
            dic.updateValue(myCards as AnyObject, forKey: DGKeysOfMessages.CARD_INFORMATION)
            dic.updateValue(playersInRoom.map({
                return $0.encodeAsDictionary()
            }) as AnyObject, forKey:DGKeysOfMessages.PLAYERS)
            
        case let .cardUsed(typeOfCard, sourceUUID, targetUUID):
            dic.updateValue(typeOfCard as AnyObject, forKey: DGKeysOfMessages.TYPE_OF_CARD)
            dic.updateValue(sourceUUID as AnyObject, forKey:DGKeysOfMessages.PLAYER_ID)
            dic.updateValue(targetUUID as AnyObject, forKey: DGKeysOfMessages.SOME_PLAYER_UUIDS)
            
        case let .cardNotAvailable(message):
            dic.updateValue(message as AnyObject, forKey:DGKeysOfMessages.INVALID_MESSAGE)
            
        case let .oneClientHasShakedDice(playerUUIDWhoShakedDice):
            dic.updateValue(playerUUIDWhoShakedDice as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            
        case let .oneClientCanGuessDiceNow(playerUUID2GuessDice):
            dic.updateValue(playerUUID2GuessDice as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            
        case .itIsNotYourTurn2Guess:
            break
            
        case .itIsNotTime2PointOutLiar:
            break
            
        case let .yourLastGuessIsNotValid(invalidMessage):
            dic.updateValue(invalidMessage as AnyObject, forKey: DGKeysOfMessages.INVALID_MESSAGE)
            
        case let .someoneTakeAGuess(playerUUID, guess, nextPlayerUUID):
            dic.updateValue(playerUUID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            dic.updateValue(guess.encodeAsDictionary() as AnyObject, forKey: DGKeysOfMessages.GUESS)
            dic.updateValue(nextPlayerUUID as AnyObject, forKey:DGKeysOfMessages.NEXT_PLAYER_ID)
            
        case let .someoneNotBelieveTheGuessAndOpenCupNow(uuidOfNotBelieveGuy):
            dic.updateValue(uuidOfNotBelieveGuy as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            
        case let .roundOverAndResultIsAndGo4NextRound(result):
            dic.updateValue(result.map({
                return $0.encodeAsDictionary()
            }) as AnyObject, forKey: DGKeysOfMessages.ROUND_RESULT)
            
        case let .oneClientIsReady4NewRound(playerUUID):
            dic.updateValue(playerUUID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            
        case .endGameOfServerCrashed:
            break
            
        case let .endGameOfSomeoneLostConnection2Server(playerUUID):
            dic.updateValue(playerUUID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            
        case let .endGameOfSomeoneAsk4Exit(playerUUID):
            dic.updateValue(playerUUID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
        }
        
        return dic
    }
    
    func builder() -> DGMessagesServer2ClientBuiler {
        switch self {
        case .youGetCards:
            return DGMessagesServer2ClientBuiler.All[0]
        case .roomIDNotAvailable:
            return DGMessagesServer2ClientBuiler.All[1]
        case .roomID:
            return DGMessagesServer2ClientBuiler.All[2]
        case .startRound:
            return DGMessagesServer2ClientBuiler.All[3]
            /*
        case .YourRoomID:
            return DGMessagesServer2ClientBuiler.All[2]
        case .SomeoneIntoRoom:
            return DGMessagesServer2ClientBuiler.All[3]
        case .StartRoundAndShakeDice:
            return DGMessagesServer2ClientBuiler.All[4]
 */
        case .cardUsed:
            return DGMessagesServer2ClientBuiler.All[4]
        case .cardNotAvailable:
            return DGMessagesServer2ClientBuiler.All[5]
        case .oneClientHasShakedDice:
            return DGMessagesServer2ClientBuiler.All[6]
        case .oneClientCanGuessDiceNow:
            return DGMessagesServer2ClientBuiler.All[7]
        case .itIsNotYourTurn2Guess:
            return DGMessagesServer2ClientBuiler.All[8]
        case .itIsNotTime2PointOutLiar:
            return DGMessagesServer2ClientBuiler.All[9]
        case .yourLastGuessIsNotValid:
            return DGMessagesServer2ClientBuiler.All[10]
        case .someoneTakeAGuess:
            return DGMessagesServer2ClientBuiler.All[11]
        case .someoneNotBelieveTheGuessAndOpenCupNow:
            return DGMessagesServer2ClientBuiler.All[12]
        case .roundOverAndResultIsAndGo4NextRound:
            return DGMessagesServer2ClientBuiler.All[13]
        case .oneClientIsReady4NewRound:
            return DGMessagesServer2ClientBuiler.All[14]
        case .endGameOfServerCrashed:
            return DGMessagesServer2ClientBuiler.All[15]
        case .endGameOfSomeoneLostConnection2Server:
            return DGMessagesServer2ClientBuiler.All[16]
        case .endGameOfSomeoneAsk4Exit:
            return DGMessagesServer2ClientBuiler.All[17]
        }
    }
    
    func triggerClientAction(_ action:DGActionsOnMessageReceivedFromServer) {
        switch self {
        case let .youGetCards(cardsGot, goldGot, reason):
            action.beNotifiedOfIGotNewCards(cardsGot, gold:goldGot, forReason: reason)
        case let .roomIDNotAvailable(roomID):
            action.beNotifiedOfRoomIDNotAvailable(roomID)
            /*
        case let .YourRoomID(roomID, myCards, countOfFullPlayers, playersAlreadyInRoom):
            action.beNotifiedOfMyRoomID(roomID, myCards:myCards, countOfFullPlayers:countOfFullPlayers, playersAlreadyInRoom: playersAlreadyInRoom)
            
        case let .SomeoneIntoRoom(player):
            action.beNotifiedOfSomeoneIntoRoom(player)
            
        case let .StartRoundAndShakeDice(orderOfPlayers, roundIndex):
            action.beNotified2StartRound(roundIndex, orderOfPlayers: orderOfPlayers)
            */
        case let .roomID(roomID):
            action.beNotifiedOfMyRoomID(roomID)
        case let .startRound(roundIndex, myCards, playersInRoom):
            action.beNotified2StartRound(roundIndex, myCards: myCards, playersInRoom: playersInRoom)
            
        case let .cardUsed(typeOfCard, sourceUUID, targetUUID):
            action.beNotifiedOfCardUsed(typeOfCard, sourceUUID:sourceUUID, targetUUID:targetUUID)
        case let .cardNotAvailable(message):
            action.beNotifiedOfMyCard2UseNotAvailable(message)
            
        case let .oneClientHasShakedDice(playerIDWhoShakedDice):
            action.beNotifiedOfOneClientHasShakedDice(playerIDWhoShakedDice)
            
        case let .oneClientCanGuessDiceNow(playerID2GuessDice):
            action.beNotifiedOfOneClient2Guess(playerID2GuessDice)
            
        case .itIsNotYourTurn2Guess:
            action.beNotifiedOfNotMyTurn2Guess()
            
        case .itIsNotTime2PointOutLiar:
            action.beNotifiedOfNotTime2PointOutLiar()
            
        case let .yourLastGuessIsNotValid(invalidMessage):
            action.beNotifiedOfMyLastGuessIsInvalid(invalidMessage)
            
        case let .someoneTakeAGuess(playerUUID, guess, nextPlayerUUID):
            action.beNotifiedOfGuessByPlayer(guess, playerUUID: playerUUID, nextPlayerUUID:nextPlayerUUID)
            
        case let .someoneNotBelieveTheGuessAndOpenCupNow(uuidOfNotBelieveGuy):
            action.beNotified2OpenCup(uuidOfNotBelieveGuy)
            
        case let .roundOverAndResultIsAndGo4NextRound(result):
            action.beNotifiedOfRoundResult(result)
            
        case let .oneClientIsReady4NewRound(playerUUID):
            action.beNotifiedOfOneClientIsReady4NewRound(playerUUID)
            
        case .endGameOfServerCrashed:
            action.beNotified2EndGameOfServerCrashed()
            
        case let .endGameOfSomeoneLostConnection2Server(playerUUID):
            action.beNotified2EndGameOfSomeoneLostConnectionFromServer(playerUUID)
            
        case let .endGameOfSomeoneAsk4Exit(playerUUID):
            action.beNotified2EndGameOfSomeoneAsk2ExitGame(playerUUID)
        }
    }
    
    static func decodeAsMessagesServer2Client(_ data:[String:AnyObject])-> DGMessagesServer2Client? {
        if let operation = data[DGKeysOfMessages.OP] as? String {
            for availableBuilder in DGMessagesServer2ClientBuiler.All {
                if operation == availableBuilder.operationString {
                    return availableBuilder.instanceBuilder(data)
                }
            }
        }
        
        return nil
    }
}

public protocol DGActionsOnMessageReceivedFromServer {
    func beNotifiedOfIGotNewCards(_ cardsGot:[String:Int], gold:Int, forReason:String)
    func beNotifiedOfRoomIDNotAvailable(_ roomID:String)
    /*
    func beNotifiedOfMyRoomID(roomID:String, myCards:[String:Int], countOfFullPlayers:Int, playersAlreadyInRoom:[DGPlayer])
    func beNotifiedOfSomeoneIntoRoom(player:DGPlayer)
    func beNotified2StartRound(roundIndex:Int, orderOfPlayers:[String])
 */
    func beNotifiedOfMyRoomID(_ roomID:String)
    func beNotified2StartRound(_ roundIndex:Int, myCards:[String:Int], playersInRoom:[DGPlayer])
    func beNotifiedOfCardUsed(_ typeOfCard:String, sourceUUID:String, targetUUID:[String])
    func beNotifiedOfMyCard2UseNotAvailable(_ message:String)
    func beNotifiedOfOneClientHasShakedDice(_ playerUUID:String)
    func beNotifiedOfOneClient2Guess(_ playerUUID:String)
    func beNotifiedOfNotMyTurn2Guess()
    func beNotifiedOfNotTime2PointOutLiar()
    func beNotifiedOfMyLastGuessIsInvalid(_ invalidMessage:String)
    func beNotifiedOfGuessByPlayer(_ guess:DGGuess, playerUUID:String, nextPlayerUUID:String)
    func beNotified2OpenCup(_ uuidOfNotBelieveGuy:String)
    func beNotifiedOfRoundResult(_ result:[DGPlayerDicesTossedAndRoundResult])
    func beNotifiedOfOneClientIsReady4NewRound(_ playerUUID:String)
    
    func beNotified2EndGameOfServerCrashed()
    func beNotified2EndGameOfSomeoneAsk2ExitGame(_ playerUUID:String)
    func beNotified2EndGameOfSomeoneLostConnectionFromServer(_ playerUUID:String)
}

// MARK: - DGMessagesClient2ServerBuilder
private class DGMessagesClient2ServerBuilder {
    fileprivate static var All = [DGMessagesClient2ServerBuilder]()

    fileprivate let operationString:String
    fileprivate let instanceBuilder : ([String:AnyObject]) -> DGMessagesClient2Server

    
    init(op:String, builder:@escaping ([String:AnyObject]) -> DGMessagesClient2Server) {
        self.operationString = op
        self.instanceBuilder = builder
        
        DGMessagesClient2ServerBuilder.All.append(self)
    }
}

private let messageC2SQuickStart = DGMessagesClient2ServerBuilder(op:"quickstart", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.quickStart(uuid:data[DGKeysOfMessages.PLAYER_UUID] as! String)
})

private let messageC2SQuickStartOf4 = DGMessagesClient2ServerBuilder(op:"quickstart4", builder: {
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.quickStart4(uuid:data[DGKeysOfMessages.PLAYER_UUID] as! String)
})

private let messageC2SRing = DGMessagesClient2ServerBuilder(op:"ring", builder: {
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.ring(uuid:data[DGKeysOfMessages.PLAYER_UUID] as! String)
})

private let messageC2SCreateANewRoom = DGMessagesClient2ServerBuilder(op:"createanewroom", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.createANewRoom(uuid:data[DGKeysOfMessages.PLAYER_UUID] as! String)
})

private let messageC2SMyPlayerName = DGMessagesClient2ServerBuilder(op:"go2aspecifiedroom", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.go2ASpecifiedRoom(
        uuid:data[DGKeysOfMessages.PLAYER_UUID] as! String,
        roomID:data[DGKeysOfMessages.ROOM_ID] as! String
    )
})

private let messageC2SIHaveShakedDice = DGMessagesClient2ServerBuilder(op:"ihaveshakeddice", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.iHaveShakedDice(
        uuid:data[DGKeysOfMessages.PLAYER_ID] as! String
    )
})
private let messageC2STry2UseCard = DGMessagesClient2ServerBuilder(op:"try2usecard", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.try2UseCard(
        typeOfCard:data[DGKeysOfMessages.TYPE_OF_CARD] as! String,
        sourceUUID:data[DGKeysOfMessages.PLAYER_ID] as! String,
        targetUUID:data[DGKeysOfMessages.SOME_PLAYER_UUIDS] as! [String]
    )
})

private let messageC2SMyGuessIs = DGMessagesClient2ServerBuilder(op:"myguessis", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.myGuessIs(
        uuid:data[DGKeysOfMessages.PLAYER_ID] as! String,
        guess:DGGuess(dict:data[DGKeysOfMessages.GUESS] as! [String:AnyObject])
    )
})
private let messageC2SIDoNotBelieve = DGMessagesClient2ServerBuilder(op:"idonotbelieve", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.iDoNotBelieve(
        uuid:data[DGKeysOfMessages.PLAYER_ID] as! String
    )
})
private let messageC2SMyDicesAre = DGMessagesClient2ServerBuilder(op:"mydicesare", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.myDicesAre(
        uuid:data[DGKeysOfMessages.PLAYER_ID] as! String,
        dices:data[DGKeysOfMessages.DICES] as! [Int]
    )
})
private let messageC2SIAmReady4NewRound = DGMessagesClient2ServerBuilder(op:"iamready4newround", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.iAmReady4NewRound(
        uuid:data[DGKeysOfMessages.PLAYER_ID] as! String
    )
})
private let messageC2SIWant2EndGame = DGMessagesClient2ServerBuilder(op:"iwant2endgame", builder:{
    (data:[String:AnyObject]) -> DGMessagesClient2Server in
    DGMessagesClient2Server.iWant2EndGame(
        uuid:data[DGKeysOfMessages.PLAYER_ID] as! String
    )
})

// MARK: - DGMessagesClient2Server
public enum DGMessagesClient2Server {
    case quickStart(uuid:String)
    case quickStart4(uuid:String)
    case ring(uuid:String)
    case createANewRoom(uuid:String)
    case go2ASpecifiedRoom(uuid:String, roomID:String)
    case iHaveShakedDice(uuid:String)
    case try2UseCard(typeOfCard:String, sourceUUID:String, targetUUID:[String])
    case myGuessIs(uuid:String, guess:DGGuess)
    case iDoNotBelieve(uuid:String)
    case myDicesAre(uuid:String, dices:[Int])
    case iAmReady4NewRound(uuid:String)
    case iWant2EndGame(uuid:String)
    
    func encode() -> [String:AnyObject] {
        var dic = [String:AnyObject]()
        dic.updateValue(self.builder().operationString as AnyObject, forKey: DGKeysOfMessages.OP)
        
        switch self {
        case let .quickStart(uuid):
            dic.updateValue(uuid as AnyObject, forKey:DGKeysOfMessages.PLAYER_UUID)
        case let .quickStart4(uuid):
            dic.updateValue(uuid as AnyObject, forKey:DGKeysOfMessages.PLAYER_UUID)
        case let .ring(uuid):
            dic.updateValue(uuid as AnyObject, forKey:DGKeysOfMessages.PLAYER_UUID)
        case let .createANewRoom(uuid):
            dic.updateValue(uuid as AnyObject, forKey:DGKeysOfMessages.PLAYER_UUID)
        case let .go2ASpecifiedRoom(uuid, roomID):
            dic.updateValue(uuid as AnyObject, forKey: DGKeysOfMessages.PLAYER_UUID)
            dic.updateValue(roomID as AnyObject, forKey:DGKeysOfMessages.ROOM_ID)
            
        case let .iHaveShakedDice(playerID):
            dic.updateValue(playerID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
        case let .try2UseCard(typeOfCard, sourceUUID, targetUUID):
            dic.updateValue(typeOfCard as AnyObject, forKey: DGKeysOfMessages.TYPE_OF_CARD)
            dic.updateValue(sourceUUID as AnyObject, forKey:DGKeysOfMessages.PLAYER_ID)
            dic.updateValue(targetUUID as AnyObject, forKey: DGKeysOfMessages.SOME_PLAYER_UUIDS)
            
        case let .myGuessIs(playerID, guess):
            dic.updateValue(playerID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            dic.updateValue(guess.encodeAsDictionary() as AnyObject, forKey: DGKeysOfMessages.GUESS)
            
        case let .iDoNotBelieve(playerID):
            dic.updateValue(playerID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            
        case let .myDicesAre(playerID, dices):
            dic.updateValue(playerID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            dic.updateValue(dices as AnyObject, forKey: DGKeysOfMessages.DICES)
            
        case let .iAmReady4NewRound(playerID):
            dic.updateValue(playerID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
            
        case let .iWant2EndGame(playerID):
            dic.updateValue(playerID as AnyObject, forKey: DGKeysOfMessages.PLAYER_ID)
        }
        
        return dic
    }
    
    fileprivate func builder() -> DGMessagesClient2ServerBuilder {
        switch self {
        case .quickStart:
            return messageC2SQuickStart
        case .quickStart4:
            return messageC2SQuickStartOf4
        case .ring:
            return messageC2SRing
        case .createANewRoom:
            return messageC2SCreateANewRoom
        case .go2ASpecifiedRoom:
            return messageC2SMyPlayerName
        case .iHaveShakedDice:
            return messageC2SIHaveShakedDice
        case .try2UseCard:
            return messageC2STry2UseCard
        case .myGuessIs:
            return messageC2SMyGuessIs
        case .iDoNotBelieve:
            return messageC2SIDoNotBelieve
        case .myDicesAre:
            return messageC2SMyDicesAre
        case .iAmReady4NewRound:
            return messageC2SIAmReady4NewRound
        case .iWant2EndGame:
            return messageC2SIWant2EndGame
        }
    }
    
    public static func decodeAsMessagesClient2Server(_ data:[String:AnyObject]) -> DGMessagesClient2Server? {
        if let operation = data[DGKeysOfMessages.OP] as? String {
            for availableBuilder in DGMessagesClient2ServerBuilder.All {
                if operation == availableBuilder.operationString {
                    return availableBuilder.instanceBuilder(data)
                }
            }
        }
        
        return nil
    }
}


// MARK: - DGGameClient
open class DGGameClient : NSObject {
    public let playerUUID:String
    
    fileprivate let sender2Server:DGClientMessageSender!
    open var actionsOnMessageReceivedFromServer:DGActionsOnMessageReceivedFromServer!
    fileprivate var timeOfLastMessageSent:DGMessageSentTime?
    
    public init(uuid:String, sender:DGClientMessageSender) {
        self.playerUUID = uuid
        self.sender2Server = sender
    }
    
    open func releaseResources() {
        // do nothing
    }
    
    // MARK: - Send Messages To Server
    fileprivate func sendMessages2Server(_ message:DGMessagesClient2Server) {
        self.timeOfLastMessageSent = DGMessageSentTime(message:message.builder().operationString, time:Date().timeIntervalSince1970)
        self.sender2Server.sendData2Server(message.encode())        
    }
    
    open func notifyServerOfQuickStart() {
        self.sendMessages2Server(DGMessagesClient2Server.quickStart(uuid: self.playerUUID))
    }
    
    open func notifyServerOfQuickStartOf4() {
        self.sendMessages2Server(DGMessagesClient2Server.quickStart4(uuid: self.playerUUID))
    }
    
    open func notifyServerOfRing() {
        self.sendMessages2Server(DGMessagesClient2Server.ring(uuid:self.playerUUID))
    }
    
    open func notifyServerOfCreateANewRoom() {
        self.sendMessages2Server(DGMessagesClient2Server.createANewRoom(uuid: self.playerUUID))
    }
    
    open func notifyServerOfGo2ASpecifiedRoom(_ roomID:String) {
        self.sendMessages2Server(DGMessagesClient2Server.go2ASpecifiedRoom(uuid: self.playerUUID, roomID:roomID))
    }
    
    open func notifyServerOfTry2UseCard(_ typeOfCard:String) {
        self.sendMessages2Server(DGMessagesClient2Server.try2UseCard(typeOfCard: typeOfCard, sourceUUID: self.playerUUID, targetUUID: [self.playerUUID]))
    }
    
    open func notifyServerIHaveShakedDice() {
        self.sendMessages2Server(DGMessagesClient2Server.iHaveShakedDice(uuid: self.playerUUID))
    }
    
    open func notifyServerMyGuess(_ guess:DGGuess) {
        self.sendMessages2Server(DGMessagesClient2Server.myGuessIs(uuid: self.playerUUID, guess: guess))
    }
    
    open func notifyServerIDoNotBelieve() {
        self.sendMessages2Server(DGMessagesClient2Server.iDoNotBelieve(uuid: self.playerUUID))
    }
    
    open func notifyServerMyDicesShaked(_ dices:[Int]) {
        self.sendMessages2Server(DGMessagesClient2Server.myDicesAre(uuid: self.playerUUID, dices: dices))
    }
    
    open func notifyServerIAmReady4NewRound() {
        self.sendMessages2Server(DGMessagesClient2Server.iAmReady4NewRound(uuid: self.playerUUID))
    }
    
    open func notifyServerIWant2EndGame() {
        self.sendMessages2Server(DGMessagesClient2Server.iWant2EndGame(uuid: self.playerUUID))
    }
    
    // MARK: - Receive Messages From Server
    open func receiveDataFromServer(_ data:[String:AnyObject]) {
        if let message = DGMessagesServer2Client.decodeAsMessagesServer2Client(data) {
            if self.actionsOnMessageReceivedFromServer != nil {
                message.triggerClientAction(self.actionsOnMessageReceivedFromServer)
            }
        }
    }
    
    fileprivate func recordTimeIntervalSinceLastMessageSent() {
//        if self.timeOfLastMessageSent != nil {
//            let interval = Date().timeIntervalSince1970 - self.timeOfLastMessageSent!.time
//            printLog("time interval is \(interval) since \(self.timeOfLastMessageSent!.message) sent")
//        }
    }
}

private class DGMessageSentTime {
    fileprivate let message:String
    fileprivate let time:TimeInterval
    
    init(message:String, time:TimeInterval) {
        self.message = message
        self.time = time
    }
}

public protocol DGClientMessageSender {
    func sendData2Server(_ data:[String:AnyObject])
}
