//
//  DGClient.swift
//  DiceGame
//
//  Created by apple on 16/2/26.
//  Copyright © 2016年 WhaleStudio. All rights reserved.
//

import Foundation
import GameKit
import WhaleLib

private let SERVER_URL_HOST = "http://dice.whalestudio.cn"
//private let SERVER_URL_HOST = "http://127.0.0.1"
//private let SERVER_URL_HOST = "http://192.168.31.248"
//private let SERVER_URL_HOST = "http://192.168.2.1"

private let SERVER_URL_PORT = 8888
private let SERVER_URL = "\(SERVER_URL_HOST):\(SERVER_URL_PORT)"

private let SERVER_CREATE_SESSION = "\(SERVER_URL)/session/create"
private let SERVER_POLL = "\(SERVER_URL)/session/poll"
private let SERVER_GAME = "\(SERVER_URL)/g"

private let SERVER_AD_CLICKED_NOTIFY_URL = "\(SERVER_URL)/ad"
private let SERVER_FEEDBACK_URL = "\(SERVER_URL)/writefeedback"
private let SERVER_FEEDBACK_HISTORY_GET_URL = "\(SERVER_URL)/readfeedback"
private let SERVER_MISSION_GET_URL = "\(SERVER_URL)/mission"
private let SERVER_USER_URL = "\(SERVER_URL)/u"

let SERVER_CHALLENGE_URL = "\(SERVER_URL)/html/app.html"
let SERVER_RANK_URL = "\(SERVER_URL)/rank"

class DGClientActions {
    static func registerAccountOfServer() {
        WLAccount.registerAccountServer(url : SERVER_URL + "/")
    }
    
    static func myInformationView(_ callback:@escaping (_ name:String, _ figure:String, _ countOfGold:Int, _ countOfCards:Int, _ countOfCrown:Int) -> Void) {
        if let theUUID = WLAccount.getUserUUID() {
            ajax(SERVER_USER_URL, parameters: [
                "uuid":theUUID as AnyObject,
                "op":"view" as AnyObject
            ]) { (error, response) in
                if let theError = error {
                    printLog("view my information failed:\(theError)")
                    return
                }
                
                guard let theResponse = response else {return}
                guard let theName = theResponse["name"] as? String else {return}
                guard let theFigure = theResponse["figure"] as? String else {return}
                guard let theCountOfGold = theResponse["countofgold"] as? Int else {return}
                guard let theCountOfCards = theResponse["countofcards"] as? Int else {return}
                guard let theCountOfCrown = theResponse["countofcrown"] as? Int else {return}

                callback(theName, theFigure, theCountOfGold, theCountOfCards, theCountOfCrown)
            }
        }
    }
    
    static func myInformationChangeName(_ newName:String, _ callback:@escaping ()->Void) {
        if let theUUID = WLAccount.getUserUUID() {
            ajax(SERVER_USER_URL, parameters: [
                "uuid":theUUID as AnyObject,
                "op":"mod" as AnyObject,
                "newname":newName as AnyObject
            ]) { (error, response) in
                if let theError = error {
                    printLog("change my name failed:\(theError)")
                    return
                }
                
                callback()
            }
        }
    }
    
    // MARK: - Check Mission
    static func checkMyMission(_ callback:@escaping (_ mission:[String]) -> Void) {
        if let theUUID = WLAccount.getUserUUID() {
            ajax(SERVER_MISSION_GET_URL, parameters: [
                "uuid":theUUID as AnyObject
            ]){(error, response) -> Void in
                if let theError = error {
                    printLog("purchase failed:\(theError)")
                    return
                }
                
                guard let theResponse = response else {return}
                guard let missions = theResponse["mission"] as? [String] else {return}
                
                callback(missions)
            }
        }
    }
    
    // MARK: - Ad Clicked
    static func notifyServerIHaveClickedAd() {
        if let theUUID = WLAccount.getUserUUID() {
            ajax(SERVER_AD_CLICKED_NOTIFY_URL, parameters: [
                "uuid":theUUID as AnyObject
            ]){(error, response) -> Void in
                    // do nothing
            }
        }
    }
    
    // MARK: - Feedback
    static func sendFeedback(_ feedbackContent:String, callback:@escaping () -> Void) {
        guard let theUUID = WLAccount.getUserUUID() else {return}
        
        ajax(SERVER_FEEDBACK_URL, parameters: [
            "name":theUUID as AnyObject,
            "content":feedbackContent as AnyObject
        ]){(error, response) -> Void in
            callback()
        }
    }
    
    static func fetchFeedbacks(_ callback:@escaping (([String]) -> Void)) {
        ajax(SERVER_FEEDBACK_HISTORY_GET_URL, parameters:[String:AnyObject]()){(error, response) -> Void in
            if let theError = error {
                printLog("purchase failed:\(theError)")
                return
            }
            
            guard let theResponse = response else {return}
            
            if let history = theResponse["information"] as? [String] {
                callback(history)
            }
        }
    }
    
    // MARK: - Refresh Rank
    static func fetchRank(_ callback:() -> Void) {
        guard let theUUID = WLAccount.getUserUUID() else {return}
        ajax(SERVER_RANK_URL, parameters:[
            "uuid":theUUID as AnyObject
        ]){(error, response) -> Void in
        }
    }
    
    // MARK: - Create SessionID
    static func createSessionID() -> String? {
        var data:Data? = nil
        let semaphore = DispatchSemaphore(value: 0)
        
        let request = URLRequest(url: URL(string: SERVER_CREATE_SESSION)!)
        let task = URLSession.shared.dataTask(with: request) { (taskData, res, error) in
            data = taskData
            semaphore.signal()
        }
        
        task.resume()
        if semaphore.wait(timeout: DispatchTime.distantFuture) == DispatchTimeoutResult.success {
            if let pureData = data {
                if let sid = NSString(data:pureData, encoding:String.Encoding.utf8.rawValue) {
                    return String(sid)
                }
            }
        }
        
        return nil
    }
    
    // MARK: - Polling
    static func polling(_ sessionID:String, callback:@escaping (NSError?, [String:AnyObject]?) -> Void) {
        ajax(SERVER_POLL, parameters:["sid":sessionID as AnyObject]){(error, response) -> Void in
            callback(error, response)
        }
    }
    
    // MARK: - Send Game Command To Server
    static func sendSessionMessage(_ sessionID:String, message:[String:AnyObject], callback:@escaping (NSError?, [String:AnyObject]?) -> Void) {
        ajax(SERVER_GAME, parameters: [
            "sid":sessionID as AnyObject,
            "json":message as AnyObject
        ]){(error, response) -> Void in
            callback(error, response)
        }
    }
}
