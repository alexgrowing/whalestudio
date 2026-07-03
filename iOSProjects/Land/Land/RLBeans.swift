//
//  RLBeans.swift
//  Land
//
//  Created by apple on 15/12/29.
//  Copyright © 2015年 G & B. All rights reserved.
//

import Foundation

class TerritoryInfo : NSObject {
    let latitude100:Int
    let longitude100:Int
    let name:String
    let levelOfTerritory:Int
    let ownerUUID:String
    var ownerName:String
    let armyQuantity:Int
    let armyLevel:Int
    
    fileprivate init(latitude100:Int, longitude100:Int, name:String, levelOfTerritory:Int, ownerUUID:String, ownerName:String, armyQuantity:Int, armyLevel:Int) {
        self.latitude100 = latitude100
        self.longitude100 = longitude100
        self.name = name
        self.levelOfTerritory = levelOfTerritory
        self.ownerUUID = ownerUUID
        self.ownerName = ownerName
        self.armyQuantity = armyQuantity
        self.armyLevel = armyLevel
    }
    
    convenience init(json:[String:AnyObject]) {
        self.init(
            latitude100:json["latitude"] as! Int,
            longitude100:json["longitude"] as! Int,
            name:json["name"] as! String,
            levelOfTerritory:json["levelofterritory"] as! Int,
            ownerUUID:json["owneruuid"] as! String,
            ownerName:json["ownername"] as! String,
            armyQuantity:json["armyquantity"] as! Int,
            armyLevel:json["armylevel"] as! Int
        )
    }
    
    override var description : String {
        get {
            return "\(self.name):[\(self.latitude100),\(self.longitude100)]{army:\(self.armyQuantity),armyLevel:\(self.armyLevel),terlevel:\(self.levelOfTerritory)}->\(self.ownerName)"
        }
    }
}

class FightResultInfo : NSObject {
    fileprivate let attackerName:String
    fileprivate let defenderName:String
    
    let occured:Date
    
    let latitude100:Int
    let longitude100:Int
    
    let goldCost:Int
    let soldierOfAttacker:Int
    let soldierOfDefender:Int
    
    let attackerWins:Bool
    let deathOfWinner:Int
    let captive:Int
    
    var nameOfAttacker:String {
        if self.attackerName.count == 0 {
            return "蛮荒势力"
        }
        
        return self.attackerName
    }
    
    var nameOfDefender:String {
        if self.defenderName.count == 0 {
            return "蛮荒势力"
        }
        
        return self.defenderName
    }
    
    var deathOfAttacker:Int {
        if self.attackerWins {
            return self.deathOfWinner
        } else {
            return self.soldierOfAttacker - self.captive
        }
    }
    
    var deathOfDefender:Int {
        if self.attackerWins {
            return self.soldierOfDefender - self.captive
        } else {
            return self.deathOfWinner
        }
    }
    
    init(json:[String:AnyObject]) {
        self.attackerName = json["attacker"] as! String
        self.defenderName = json["defender"] as! String
        self.latitude100 = json["lat"] as! Int
        self.longitude100 = json["lon"] as! Int
        self.occured = Date(timeIntervalSince1970: json["occured"] as! Double)
        
        self.goldCost = json["goldcost"] as! Int
        self.soldierOfAttacker = json["soldierofattacker"] as! Int
        self.soldierOfDefender = json["soldierofdefender"] as! Int
        
        self.attackerWins = json["attackerwins"] as! Bool
        self.deathOfWinner = json["deathofwinner"] as! Int
        self.captive = json["captive"] as! Int
    }
}
