//
//  RLUser.swift
//  Land
//
//  Created by apple on 15/12/22.
//  Copyright © 2015年 G & B. All rights reserved.
//

import Foundation
import GameKit
import LandLib
import WhaleLib

private let DEFAULTS_USER_ACCOUNT_ID = "defaults_user_account_id"
private let DEFAULTS_USER_NAME = "defaults_user_name"
private let DEFAULTS_SAVED_FOOTPRINTS = "defaults_saved_json_string_footprints"
private let DEFAULTS_LAST_TIME_OF_CHECK_MY_FIGHTS = "defaults_last_time_of_check_my_fights"

let PRICE_OF_EACH_SOLDIOR_2_RECRUIT = 100
let PRICE_OF_EACH_SOLDIER_2_CAMPAIGN = 2
let PRICE_OF_DIAMOND_2_RENAME = 10
let COUNT_OF_SOLDIER_TRAINING_PER_MINUTE = 10
let COUNT_OF_SECONDS_PER_DIAMOND = 200

let ERROR_NONE = 0
let ERROR_CODE_NOT_ENOUGH_DIAMOND = 1

private let SCORE_TERRITORIES_VISITED = "territories_visited"
private let SCORE_TERRITORIES_OWNED = "territories_owned"

class RLUser {
    let uuid:String
    var name:String
    var countOfGold:Int = 0
    var countOfSoldier:Int = 0
    var training:RLTraining?
    // RLTraining(count: 100, start: NSDate().dateByAddingTimeInterval(-1000), end: NSDate().dateByAddingTimeInterval(200))
    fileprivate var levelOfSoldier:Int = 0
    var countOfDiamond:Int = 0
    fileprivate var footprints:Set<Territory>
    fileprivate var myTerritories:Set<Territory>
    
    var free2Rename:Bool
    
    var readOnlyFootprints : Set<Territory> {
        get {
            return self.footprints
        }
    }
    
    var readOnlyMyTerritories : Set<Territory> {
        get {
            return self.myTerritories
        }
    }
    
    var readOnlyCountOfDiamond : Int {
        get {
            return self.countOfDiamond
        }
    }
    
    var isTrainingSoldier : Bool {
        return self.training != nil
    }
    
    fileprivate init(uuid:String, name:String, countOfGold:Int, countOfSoldier:Int, training:RLTraining?, levelOfSoldier:Int, countOfDiamond:Int, footprints:Set<Territory>, myTerritories:[Territory], free2Rename:Bool) {
        self.uuid = uuid
        self.name = name
        self.countOfGold = countOfGold
        self.countOfSoldier = countOfSoldier
        self.training = training
        self.levelOfSoldier = levelOfSoldier
        self.countOfDiamond = countOfDiamond
        self.footprints = footprints
        self.myTerritories = Set<Territory>(myTerritories)
        
        self.free2Rename = free2Rename
        
        self.reportScoreOfTerritoriesVisited()
        self.reportScoreOfTerritoriesOccupied()
        
        RLUser.saveFootprints2Defaults(self.footprints)
    }
    
    func matchCurrentGameCenterID() -> Bool {
        let localPlayer = GKLocalPlayer.local
        if localPlayer.isAuthenticated && self.uuid == getUUIDFromLocalPlayer(localPlayer) {
            return true
        }
        
        return false
    }
    
    func updateMyTerritoriesOnFightResult(_ result:FightResultInfo, target:TerritoryInfo) {
        if result.attackerWins {
            self.myTerritories.insert(Territory(latitude100: target.latitude100, longitude100: target.longitude100))
            
            self.reportScoreOfTerritoriesOccupied()
        }
    }
    
    func insertFootprint(_ fp:Territory) {
        self.footprints.insert(fp)
        
        self.reportScoreOfTerritoriesVisited()
        RLUser.saveFootprints2Defaults(self.footprints)
    }
    
    func visitedTerritory(_ territory:Territory) -> Bool {
        return self.footprints.contains(territory)
    }
    
    func reportScoreOfTerritoriesVisited() {
        if !self.matchCurrentGameCenterID() {
            return
        }
        
        let scoreOfVisited = GKScore(leaderboardIdentifier: SCORE_TERRITORIES_VISITED)
        scoreOfVisited.value = Int64(self.footprints.count)
        
        GKScore.report([scoreOfVisited], withCompletionHandler: nil)
    }
    
    func reportScoreOfTerritoriesOccupied() {
        if !self.matchCurrentGameCenterID() {
            return
        }
        
        let scoreOfOwned = GKScore(leaderboardIdentifier: SCORE_TERRITORIES_OWNED)
        scoreOfOwned.value = Int64(self.myTerritories.count)
        
        GKScore.report([scoreOfOwned], withCompletionHandler: nil)
    }
    
    // MARK: Static Methods
    fileprivate static var currentUser : RLUser?
    
    static func getCurrentUser() -> RLUser? {
        return RLUser.currentUser
    }
    
    static func getUUIDLastSuccessLogin() -> String? {
        return UserDefaults.standard.string(forKey: DEFAULTS_USER_ACCOUNT_ID)
    }
    
    static func getNameLastSuccesLogin() -> String? {
        return UserDefaults.standard.string(forKey: DEFAULTS_USER_NAME)
    }
    
    static func buildCurrentUser(_ uuid:String, name:String, countOfGold:Int, countOfSoldier:Int, training:RLTraining?, levelOfSoldier:Int, countOfDiamond:Int, footprints:Set<Territory>, myTerritories:[Territory], free2Rename:Bool) {
        let defaults = UserDefaults.standard
        
        defaults.set(uuid, forKey: DEFAULTS_USER_ACCOUNT_ID)
        defaults.set(name, forKey: DEFAULTS_USER_NAME)
        
        defaults.synchronize()
        
        RLUser.currentUser = RLUser(uuid: uuid, name: name, countOfGold:countOfGold, countOfSoldier:countOfSoldier, training:training, levelOfSoldier:levelOfSoldier, countOfDiamond: countOfDiamond, footprints: footprints, myTerritories:myTerritories, free2Rename:free2Rename)
    }
    
    static func getSavedFootprintsFromDefaultsAsNSData() -> Data? {
        let defaults = UserDefaults.standard
        
        return defaults.object(forKey: DEFAULTS_SAVED_FOOTPRINTS) as? Data
    }
    
    static func saveFootprints2Defaults(_ prints:Set<Territory>) {
        let defaults = UserDefaults.standard

        var jsonArray = [[String:Int]]()
        for ter in prints {
            jsonArray.append(ter.asJson())
        }
        
        if let jsonableData = try? JSONSerialization.data(withJSONObject: jsonArray, options: JSONSerialization.WritingOptions.prettyPrinted) {
            defaults.set(jsonableData, forKey: DEFAULTS_SAVED_FOOTPRINTS)
        }
        
        defaults.synchronize()
    }
    
    static func getSavedLastTimeOfCheckMyFights() -> Date {
        let defaults = UserDefaults.standard
        
        let timeInterval = defaults.double(forKey: DEFAULTS_LAST_TIME_OF_CHECK_MY_FIGHTS)
        return Date(timeIntervalSince1970:timeInterval)
    }
    
    static func saveNowAsLastTimeOfCheckMyFights() {
        let defaults = UserDefaults.standard
        defaults.set(Date().timeIntervalSince1970, forKey: DEFAULTS_LAST_TIME_OF_CHECK_MY_FIGHTS)
        defaults.synchronize()
    }
    
    static func cleanupSavedFootprints() {
        let defaults = UserDefaults.standard
        defaults.removeObject(forKey: DEFAULTS_SAVED_FOOTPRINTS)
    }
}

class RLTraining {
    let countOfSoldier:Int
    let start:Date
    let end:Date
    
    init(count:Int, start:Date, end:Date) {
        self.countOfSoldier = count
        self.start = start
        self.end = end
    }
    
    static func build(_ json:[String:AnyObject]) -> RLTraining? {
        guard let countOfSoldierFromJson = json["countofsoldier"] as? Int else {return nil}
        guard let startFromJson = json["start"] as? Int else {return nil}
        guard let endFromJson = json["end"] as? Int else {return nil}
        
        if countOfSoldierFromJson <= 0 {
            return nil
        }
        if startFromJson >= endFromJson {
            return nil
        }
        if TimeInterval(endFromJson) <= Date().timeIntervalSince1970 {
            return nil
        }
        
        return RLTraining(count: countOfSoldierFromJson, start: Date(timeIntervalSince1970: TimeInterval(startFromJson)), end: Date(timeIntervalSince1970: TimeInterval(endFromJson)))
    }
    
    var allTime:TimeInterval {
        get {
            return self.end.timeIntervalSince(self.start)
        }
    }
    var passedTime:TimeInterval {
        get {
            return -self.start.timeIntervalSinceNow
        }
    }
    var leftTime:TimeInterval {
        get {
            return self.end.timeIntervalSinceNow
        }
    }
    var countOfSoldierFinished:Int {
        get {
            return Int(Double(self.countOfSoldier) * self.passedTime / self.allTime)
        }
    }
}
