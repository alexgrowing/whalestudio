//
//  RLClient.swift
//  Land
//
//  Created by apple on 15/12/20.
//  Copyright © 2015年 G & B. All rights reserved.
//

import Foundation
import GameKit
import WhaleLib
import LandLib

private let SERVER_URL_HOST = "http://land.whalestudio.cn"
//private let SERVER_URL_HOST = "http://192.168.31.248"
//private let SERVER_URL_HOST = "http://192.168.2.1"
//private let SERVER_URL_HOST = "http://127.0.0.1"

private let SERVER_URL_PORT:Int = 9999
private let SERVER_URL = "\(SERVER_URL_HOST):\(SERVER_URL_PORT)"

private let URL_LOGIN = "\(SERVER_URL)/login13"
private let URL_RENAME = "\(SERVER_URL)/rename"
private let URL_PURCHASE = "\(SERVER_URL)/purchase"
private let URL_FOOTPRINT = "\(SERVER_URL)/foot"
private let URL_STEP = "\(SERVER_URL)/step"
private let URL_TERRITORY = "\(SERVER_URL)/ter"
private let URL_RECRUIT = "\(SERVER_URL)/rec"
private let URL_QUICK_FINISH_TRAINING = "\(SERVER_URL)/quickfinishtraining"
private let URL_CHECK_TRAINING = "\(SERVER_URL)/checktraining"
private let URL_ATTACK = "\(SERVER_URL)/atta"
private let URL_BRIEF_FIGHTS = "\(SERVER_URL)/brieffights"
private let URL_COUNT_OF_NEW_FIGHTS = "\(SERVER_URL)/countofnewfights"
private let URL_GOVER = "\(SERVER_URL)/gover"
private let URL_SEARCH_TREASURE = "\(SERVER_URL)/searchtreasure"
private let URL_PART_OF_COUNTRY = "\(SERVER_URL)/partofcountry"

private let URL_SHOW_OFF = "\(SERVER_URL_HOST)/land/showoff?pid="

class RLClientActions {
    // MARK: - LOGIN
    static func login(_ localPlayer:GKLocalPlayer, callback:@escaping (_ success:Bool) -> Void) {
        if let idOfGameCenter = getUUIDFromLocalPlayer(localPlayer) {
            let nameOfGameCenter = localPlayer.alias
            
            RLClientActions.login(idOfGameCenter, nameOfPlayer: nameOfGameCenter, callback: callback)
            return
        }
        
        RLClientActions.registerAndLogin(callback)
    }
    
    static func login(_ uuidOfPlayer:String, nameOfPlayer:String?, callback:@escaping (_ success:Bool) -> Void) {
        var parameters = [String:String]()
        parameters["pid"] = uuidOfPlayer
        if let theNameOfPlayer = nameOfPlayer {
            parameters["pname"] = theNameOfPlayer
        }
        
        RLClientActions.ajaxLogin(parameters, callback: callback)
    }
    
    static func registerAndLogin(_ callback:@escaping (_ success:Bool) -> Void) {
        RLClientActions.ajaxLogin(nil, callback: callback)
    }
    
    fileprivate static func ajaxLogin(_ parameters:[String:String]?, callback:@escaping (_ success:Bool) -> Void) {
        var ajaxParameters = [String:AnyObject]()
        if let theParameters = parameters {
            for (k, v) in theParameters {
                ajaxParameters[k] = v as AnyObject?
            }
        }
        
        var clientSavedFootprints = Set<Territory>()
        if let thePrintsData = RLUser.getSavedFootprintsFromDefaultsAsNSData() {
            ajaxParameters["prints"] = thePrintsData as AnyObject
            clientSavedFootprints = Territory.decode(thePrintsData)
        }
        
        ajax(URL_LOGIN, parameters: ajaxParameters) { (error, response) -> Void in
            if let theError = error {
                printLog("login failed:\(theError)")
                return
            }
            guard let theResponse = response else {return}
            
            // 加一个标记,如果返回有deprecated参数且为true时callback(success:false)以UpdateVersion
            if let deprecated = theResponse["deprecated"] as? Bool , deprecated {
                callback(false)
                return
            }
            
            guard let validUUID = theResponse["validuuid"] as? String else {return}
            guard let validName = theResponse["validname"] as? String else {return}
            guard let countOfGold = theResponse["countofgold"] as? Int else {return}
            guard let countOfSoldier = theResponse["countofsoldier"] as? Int else {return}
            guard let jsonTraining = theResponse["training"] as? [String:AnyObject] else {return}
            guard let levelOfSoldier = theResponse["levelofsoldier"] as? Int else {return}
            guard let countOfDiamond = theResponse["countofdiamond"] as? Int else {return}
            guard let jsonFootprints = theResponse["footprints"] as? [[String:AnyObject]] else {return}
            guard let jsonMyTerritories = theResponse["myterritories"] as? [[String:AnyObject]] else {return}
            
            guard let free2Rename = theResponse["free2rename"] as? Bool else {return}
            
            for jsonFp in jsonFootprints {
                if let fp = Territory.build(jsonFp) {
                    clientSavedFootprints.insert(fp)
                }
            }
            
            var myTerritories = [Territory]()
            for jsonTer in jsonMyTerritories {
                if let ter = Territory.build(jsonTer) {
                    myTerritories.append(ter)
                }
            }
            
            RLUser.buildCurrentUser(validUUID, name: validName, countOfGold: countOfGold, countOfSoldier: countOfSoldier, training:RLTraining.build(jsonTraining), levelOfSoldier: levelOfSoldier, countOfDiamond: countOfDiamond, footprints: clientSavedFootprints, myTerritories: myTerritories, free2Rename:free2Rename)
            
            callback(true)
        }
    }
    
    // MARK: - Rename
    static func rename(_ newName:String, callback:@escaping (_ errorCode:Int) -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_RENAME, parameters: [
                "pid":theUser.uuid as AnyObject,
                "pname":newName as AnyObject
            ], callback: { (error, response) -> Void in
                if let theError = error {
                    printLog("addFootprint failed:\(theError)")
                    return
                }
                guard let theResponse = response else {return}
                
                if let errorCode = theResponse["error"] as? Int , errorCode != ERROR_NONE {
                    callback(errorCode)
                } else {
                    guard let newName = theResponse["newname"] as? String else {return}
                    guard let newDiamond = theResponse["newdiamond"] as? Int else {return}
                    
                    theUser.name = newName
                    theUser.countOfDiamond = newDiamond
                    theUser.free2Rename = false
                    
                    callback(ERROR_NONE)
                }
            })
        }
    }
    
    // MARK: - Purchase
    static func purchase(_ bundleID:String, callback:@escaping (_ countOfDiamond:Int) -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_PURCHASE, parameters: [
                "pid":theUser.uuid as AnyObject,
                "bundle":bundleID as AnyObject
            ]) {(error, response) -> Void in
                if let theError = error {
                    printLog("purchase failed:\(theError)")
                    return
                }
                
                guard let theResponse = response else {return}
                
                if let countOfDiamond = theResponse["countofdiamondpurchased"] as? Int {
                    callback(countOfDiamond)
                }
            }
        }
    }
    
    // MARK: - Footprint
    static func addFootprint(_ fp:Territory) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_FOOTPRINT, parameters: [
                "pid":theUser.uuid as AnyObject,
                "fp":fp.asJson() as AnyObject
            ]) { (error, response) -> Void in
                if let theError = error {
                    printLog("addFootprint failed:\(theError)")
                    return
                }
                guard let theResponse = response else {return}
                
                printLog("\(theResponse)")
            }
        } else {
            RLClientActions.tryAddFootprintLater(fp)
        }
    }
    
    fileprivate static func tryAddFootprintLater(_ fp:Territory) {
        printLog("用户尚未登录:延迟2秒添加Footprint到服务器")
        DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(2 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) { () -> Void in
            RLClientActions.addFootprint(fp)
        }
    }
    
    // MARK: - Step
    static func updateStep(_ count:Int, callback:@escaping (_ goldPlus:Int) -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_STEP, parameters: [
                "pid":theUser.uuid as AnyObject,
                "count":count as AnyObject
            ], callback: { (error, response) -> Void in
                if let theError = error {
                    printLog("update step failed:\(theError)")
                    return
                }
                
                guard let theResponse = response else {return}
                if let goldPlus = theResponse["gold"] as? Int {
                    callback(goldPlus)
                }
            })
        } else {
            RLClientActions.tryUpdateStepLater(count, callback:callback)
        }
    }
    
    fileprivate static func tryUpdateStepLater(_ count:Int, callback:@escaping (_ goldPlus:Int) -> Void) {
        printLog("用户尚未登录:延迟2秒更新Step到服务器")
        DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(2 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) { () -> Void in
            RLClientActions.updateStep(count, callback: callback)
        }
    }
    
    // MARK: - Territory
    static func lookupTerritory(_ territory:Territory, callback:@escaping (TerritoryInfo) -> Void) {
        ajax(URL_TERRITORY, parameters: [
            "lat":territory.latitude100 as AnyObject,
            "lon":territory.longitude100 as AnyObject
        ]) { (error, response) -> Void in
            if let theError = error {
                printLog("lookup territory information failed:\(theError)")
                return
            }
            
            guard let theResponse = response else {return}
            callback(TerritoryInfo(json: theResponse))
        }
    }
    
    // MARK: - SearchTreasure
    static func searchTreasure(_ ter:Territory, callback:@escaping (_ goldFound:Int) -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_SEARCH_TREASURE, parameters: [
                "pid":theUser.uuid as AnyObject,
                "lat":ter.latitude100 as AnyObject,
                "lon":ter.longitude100 as AnyObject
            ]) { (error, response) -> Void in
                if let theError = error {
                    printLog("search treasure failed:\(theError)")
                    return
                }
                
                guard let theResponse = response else {return}
                
                guard let goldFound = theResponse["goldfound"] as? Int else {return}
                
                callback(goldFound)
            }
        }
    }
    
    // MARK: - Recruit
    static func recruitSoldier(_ countOfSoldier2Recruit:Int, callback:@escaping () -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_RECRUIT, parameters: [
                "pid": theUser.uuid as AnyObject,
                "count":countOfSoldier2Recruit as AnyObject
            ], callback: { (error, response) -> Void in
                if let theError = error {
                    printLog("recruit failed:\(theError)")
                    return
                }
                
                guard let theResponse = response else {return}
                guard let goldCost = theResponse["goldcost"] as? Int else {return}
                guard let jsonOfTraining = theResponse["training"] as? [String:AnyObject] else {return}
                
                theUser.countOfGold = theUser.countOfGold - goldCost
                theUser.training = RLTraining.build(jsonOfTraining)
                
                callback()
            })
        }
    }
    
    // MARK: - Quick Finish Training
    static func quickFinishTraining(_ callback:@escaping (_ errorCode:Int) -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_QUICK_FINISH_TRAINING, parameters: [
                "pid":theUser.uuid as AnyObject
            ], callback: { (error, response) -> Void in
                if let theError = error {
                    printLog("quick finish training failed:\(theError)")
                    return
                }
                
                guard let theResponse = response else {return}
                if let errorCode = theResponse["error"] as? Int , errorCode != ERROR_NONE {
                    callback(errorCode)
                } else {
                    guard let newSoldier = theResponse["newsoldier"] as? Int else {return}
                    guard let newDiamond = theResponse["newdiamond"] as? Int else {return}
                    
                    theUser.countOfSoldier = newSoldier
                    theUser.countOfDiamond = newDiamond
                    theUser.training = nil
                    
                    callback(ERROR_NONE)
                }
            })
        }
    }
    
    // MARK: - Attack
    static func attack(_ countOfSoldier2Attack:Int, latitude100:Int, longitude100:Int, callback:@escaping (_ fightResult:FightResultInfo) -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_ATTACK, parameters: [
                "pid":theUser.uuid as AnyObject,
                "countofsoldier":countOfSoldier2Attack as AnyObject,
                "lat":latitude100 as AnyObject,
                "lon":longitude100 as AnyObject
            ], callback: { (error, response) -> Void in
                if let theError = error {
                    printLog("attack failed:\(theError)")
                    return
                }
                guard let theResponse = response else {return}

                callback(FightResultInfo(json:theResponse))
            })
        }
    }
    
    // MARK: - View Brief Fights
    static func viewBriefFights(_ callback:@escaping (_ fightsAsAttacker:[FightResultInfo], _ fightsAsDefender:[FightResultInfo]) -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_BRIEF_FIGHTS, parameters: [
                "pid":theUser.uuid as AnyObject
            ], callback: { (error, response) -> Void in
                if let theError = error {
                    printLog("view brief fights failed:\(theError)")
                    return
                }
                guard let theResponse = response else {return}
                guard let jsonOfFightsAsAttacker = theResponse["asattacker"] as? [[String:AnyObject]] else {return}
                guard let jsonOfFightsAsDefender = theResponse["asdefender"] as? [[String:AnyObject]] else {return}
                
                let fightsAsAttacker = jsonOfFightsAsAttacker.map({ (json) -> FightResultInfo in
                    return FightResultInfo(json: json)
                })
                let fightsAsDefender = jsonOfFightsAsDefender.map({ (json) -> FightResultInfo in
                    return FightResultInfo(json: json)
                })
                
                callback(fightsAsAttacker, fightsAsDefender)
            })
        }
    }
    
    // MARK: - Fetch Count Of New Fights
    static func fetchCountOfNewFights(_ callback:@escaping (_ count:Int) -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_COUNT_OF_NEW_FIGHTS, parameters: [
                "pid":theUser.uuid as AnyObject,
                "lastcheck":Int(RLUser.getSavedLastTimeOfCheckMyFights().timeIntervalSince1970) as AnyObject
            ], callback: { (error, response) -> Void in
                if let theError = error {
                    printLog("fetch count of new fights failed:\(theError)")
                    return
                }
                guard let theResponse = response else {return}
                guard let result = theResponse["result"] as? Int else {return}
                
                callback(result)
            })
        }
    }
    
    // MARK: - Gover
    static func gover(_ newName:String, newCountOfSoldier:Int, latitude100:Int, longitude100:Int, callback:@escaping (_ countOfSoliderLeft:Int) -> Void) {
        if let theUser = RLUser.getCurrentUser() {
            ajax(URL_GOVER, parameters: [
                "pid":theUser.uuid as AnyObject,
                "newname":newName as AnyObject,
                "newcountofsoldier":newCountOfSoldier as AnyObject,
                "lat":latitude100 as AnyObject,
                "lon":longitude100 as AnyObject
            ], callback: { (error, response) -> Void in
                if let theError = error {
                    printLog("gover failed:\(theError)")
                    return
                }
                guard let theResponse = response else {return}
                
                guard let countOfSoldierLeft = theResponse["soldierleft"] as? Int else {return}
                callback(countOfSoldierLeft)
            })
        }
    }
    
    static func createURL4Showoff() -> String? {
        if let theUser = RLUser.getCurrentUser() {
            return URL_SHOW_OFF + theUser.uuid
        }
        
        return nil
    }
    
    static func calculateSizeOfCountry(countOfLocations: Int, callback:@escaping (_ size:Float64, _ partOfMatchedCountry:Float64, _ nameOfMatchedCountry:String) -> Void) {
        ajax(URL_PART_OF_COUNTRY, parameters: [
            "countoflocations":countOfLocations as AnyObject
        ]) { (error, response) in
            if let theError = error {
                printLog("gover failed:\(theError)")
                return
            }
            guard let theResponse = response else {return}
            
            guard let squareOfAllLocations = theResponse["Size"] as? Float64 else {return}
            guard let partOfMatchedCountry = theResponse["PartOfMatchedCountry"] as? Float64 else {return}
            guard let nameOfMatchedCountry = theResponse["NameOfMatchedCountry"] as? String else {return}
            
            callback(squareOfAllLocations, partOfMatchedCountry, nameOfMatchedCountry)
        }
    }
}
