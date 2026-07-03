//
//  DGBeans.swift
//  DiceGame
//
//  Created by Alex Chen on 15/4/24.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import Foundation

public let CARD_NAME_RESHAKE = "cardnamereshake"
public func CARD_NAME_DESCRIPTION(_ typeOfCard:String) -> String {
    switch typeOfCard {
    case CARD_NAME_RESHAKE:
        return DGBundle.i18n(key: "Lucky_Card")
    default:
        return DGBundle.i18n(key: "Unknown_Card")
    }
}

open class DGPlayer : NSObject {
    public let uuid:String
    public let playerName:String
    let figure:DGFigure
    let dbTimesOfAllWins:Int
    let dbTimesOfAllAttackWins:Int
    let dbMaxTimesOfAllDefendWins:Int
    let startupRoundScore:Int
    
    let countOfAllCrowns:Int
    
    public init(uuid:String, playerName:String, figure:DGFigure, timesOfAllWins:Int, timesOfAllAttackWins:Int, maxTimesOfAllDefendWins:Int, startupRoundScore:Int, countOfAllCrowns:Int) {
        self.uuid = uuid
        self.playerName = playerName
        self.figure = figure
        self.dbTimesOfAllWins = timesOfAllWins
        self.dbTimesOfAllAttackWins = timesOfAllAttackWins
        self.dbMaxTimesOfAllDefendWins = maxTimesOfAllDefendWins
        self.startupRoundScore = startupRoundScore
        
        self.countOfAllCrowns = countOfAllCrowns
    }
    
    convenience init(dict:[String:AnyObject]) {
        self.init(
            uuid:dict["uuid"] as! String,
            playerName:dict["playername"] as! String,
            figure:DGFigure(dict:dict["figure"] as! [String:AnyObject]),
            timesOfAllWins:dict["dbtimesofallwins"] as! Int,
            timesOfAllAttackWins:dict["dbtimesofallattackwins"] as! Int,
            maxTimesOfAllDefendWins:dict["dbmaxtimesofalldefendwins"] as! Int,
            startupRoundScore:dict["timesofroundwins"] as! Int,
            
            countOfAllCrowns: dict["countofallcrowns"] as! Int
        )
    }
    
    func encodeAsDictionary() -> [String:AnyObject] {
        return [
            "uuid":self.uuid as AnyObject,
            "playername" : self.playerName as AnyObject,
            "figure":self.figure.encodeAsDictionary() as AnyObject,
            "dbtimesofallwins":self.dbTimesOfAllWins as AnyObject,
            "dbtimesofallattackwins":self.dbTimesOfAllAttackWins as AnyObject,
            "dbmaxtimesofalldefendwins":self.dbMaxTimesOfAllDefendWins as AnyObject,
            "timesofroundwins":self.startupRoundScore as AnyObject,
            
            "countofallcrowns":self.countOfAllCrowns as AnyObject
        ]
    }
}

open class DGFigure:NSObject {
    let isURL:Bool
    let path:String
    
    public init(isURL:Bool, path:String) {
        self.isURL = isURL
        self.path = path
    }
    
    convenience init(dict:[String:AnyObject]) {
        self.init(isURL:dict["isurl"] as! Bool, path:dict["path"] as! String)
    }
    
    func encodeAsDictionary() -> [String:AnyObject] {
        return [
            "isurl":self.isURL as AnyObject,
            "path":self.path as AnyObject
        ]
    }
    
    open func asImage() -> UIImage {
        if isURL {
            if let url = URL(string: path) {
                if let data = try? Data(contentsOf: url) {
                    if let image = UIImage(data: data) {
                        return image
                    }
                }
            }
        } else {
            if let bundleImage = UIImage(named:path) {
                return bundleImage
            }
        }
        
        return UIImage(named:DGBundle.DEFAULT_FIGURE_IMAGE)!
    }
}

open class DGGuess : NSObject {
    public let count:Int
    public let factor:Int
    
    init(count:Int, factor:Int) {
        self.count = count
        self.factor = factor
    }
    
    convenience init(dict:[String:AnyObject]) {
        self.init(count:dict["count"] as! Int,factor:dict["factor"] as! Int)
    }
    
    func encodeAsDictionary() -> [String:AnyObject] {
        return [
            "count" : self.count as AnyObject,
            "factor" : self.factor as AnyObject
        ]
    }
}

open class DGMatchedDiceNumber : NSObject {
    public let diceNumber:Int
    public let matched:Bool
    
    init(diceNumber:Int, matched:Bool) {
        self.diceNumber = diceNumber
        self.matched = matched
    }
    
    convenience init(dict:[String:AnyObject]) {
        self.init(diceNumber:dict["dicenumber"] as! Int, matched:dict["matched"] as! Bool)
    }
    
    func encodeAsDictionary() -> [String:AnyObject] {
        return [
            "dicenumber" : self.diceNumber as AnyObject,
            "matched":self.matched as AnyObject
        ]
    }
}

open class DGPlayerDicesTossedAndRoundResult : NSObject {
    public let playerUUID:String
    public let timesOfAllWins:Int
    public let timesOfAllAttackWins:Int
    public let maxTimesOfAllDefendWins:Int
    public let currentCountOfCrowns:Int
    
    public let matchedInforOfDicesTossed:[DGMatchedDiceNumber]
//    public let roundResult:RoundResult
    public let crownModification:Int
    public let goldModification:Int
    
    public init(uuid:String,
                timesOfAllWins:Int, timesOfAllAttackWins:Int, maxTimesOfAllDefendWins:Int,
                currentCountOfCrowns:Int,
                matchedInforOfDicesTossed:[DGMatchedDiceNumber], crownModification:Int, goldModification:Int) {
        self.playerUUID = uuid
        self.timesOfAllWins = timesOfAllWins
        self.timesOfAllAttackWins = timesOfAllAttackWins
        self.maxTimesOfAllDefendWins = maxTimesOfAllDefendWins
        self.currentCountOfCrowns = currentCountOfCrowns
        
        self.matchedInforOfDicesTossed = matchedInforOfDicesTossed
        self.crownModification = crownModification
        self.goldModification = goldModification
    }
    
    convenience init(dict:[String:AnyObject]) {
        self.init(
            uuid:dict["uuid"] as! String,
            timesOfAllWins:dict["timesofallwins"] as! Int,
            timesOfAllAttackWins:dict["timesofallattackwins"] as! Int,
            maxTimesOfAllDefendWins:dict["maxtimesofalldefendwins"] as! Int,
            currentCountOfCrowns: dict["currentcountofcrowns"] as! Int,
            matchedInforOfDicesTossed:(dict["matchedinforofdicestossed"] as! [[String:AnyObject]]).map() {DGMatchedDiceNumber(dict:$0)},
//            result:RoundResult(rawValue:dict["roundresult"] as! Int)!,
            crownModification:dict["crownmodification"] as! Int,
            goldModification:dict["goldmodification"] as! Int
        )
    }
    
    func encodeAsDictionary() -> [String:AnyObject] {
        return [
            "uuid":self.playerUUID as AnyObject,
            "timesofallwins":self.timesOfAllWins as AnyObject,
            "timesofallattackwins":self.timesOfAllAttackWins as AnyObject,
            "maxtimesofalldefendwins":self.maxTimesOfAllDefendWins as AnyObject,
            "currentcountofcrowns":self.currentCountOfCrowns as AnyObject,
            "matchedinforofdicestossed" : self.matchedInforOfDicesTossed.map() {$0.encodeAsDictionary()} as AnyObject,
//            "roundresult":self.roundResult.rawValue,
            "crownmodification":self.crownModification as AnyObject,
            "goldmodification":self.goldModification as AnyObject
        ]
    }
}

/*
public enum RoundResult : Int {
    case Win = 0, Lose = 1, Participate = -1
}
 */

open class DGGuessHistoryElement {
    let guess:DGGuess
    let uuidOfGuesser:String
    let isMyself:Bool
    
    public init(guess:DGGuess, uuidOfGuesser:String, isMyself:Bool) {
        self.guess = guess
        self.uuidOfGuesser = uuidOfGuesser
        self.isMyself = isMyself
    }
}
