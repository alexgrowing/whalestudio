//
//  WebServices.swift
//  Gym
//
//  Created by alex on 2018/2/28.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import Foundation
import WhaleLib

private let SERVER = "http://gym.whalestudio.cn:9988/"
//private let SERVER = "http://localhost:9988/"

private let REQUEST_LAST_MODIFIED = SERVER + "lastmodified"
private let REQUEST_UPLOAD_ALL = SERVER + "uploadall"
private let REQUEST_DOWNLOAD_ALL = SERVER + "downloadall"

private let REQUEST_REFRESH_ALL_MOVES = SERVER + "refreshallmoves"
private let REQUEST_NEW_TRAINING = SERVER + "newtraining"

class WebServices {
    static func registerAccountOfServer() {
        WLAccount.registerAccountServer(url : SERVER)
    }
    
    static func fetchLastModified(callback:@escaping (_ success:Bool, _ lastModified:Int) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            return
        }
        
        ajax(REQUEST_LAST_MODIFIED, parameters: ["passcode":theUserPasscode as AnyObject]) { (error, res) in
            if error != nil {
                callback(false, 0)
            } else {
                callback(true, res!["lastmodified"] as! Int)
            }
        }
    }
    
    static func uploadAll(callback:@escaping (_ success:Bool) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            return
        }
        
        ajax(REQUEST_UPLOAD_ALL, parameters: [
            "passcode":theUserPasscode as AnyObject,
            "data":GCenter.instance.encodeAsJson() as AnyObject
        ]) { (error, res) in
            if error != nil {
                callback(false)
            } else {
                callback(true)
            }
        }
    }
    
    static func downloadAll(callback:@escaping (_ success:Bool) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            return
        }
        
        ajax(REQUEST_DOWNLOAD_ALL, parameters: [
            "passcode": theUserPasscode as AnyObject
        ]) { (error, res) in
            if error != nil {
                callback(false)
            } else {
                if let theDict = res {
                    GCenter.instance.refreshBy(dict: theDict)
                    callback(true)
                }
            }
        }
    }
    
    static func refreshAllMoves(callback:@escaping (_ success:Bool) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            return
        }
        
        ajax(REQUEST_REFRESH_ALL_MOVES, parameters: [
            "passcode":theUserPasscode as AnyObject,
            "data":GCenter.instance.encodeCategoriedMovesAsJson() as AnyObject
        ]) { (error, res) in
            if error != nil {
                callback(false)
            } else {
                callback(true)
            }
        }
    }
    
    static func newTraining(newTraining:GTraining, callback:@escaping (_ success:Bool) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            return
        }
        
        ajax(REQUEST_NEW_TRAINING, parameters: [
            "passcode":theUserPasscode as AnyObject,
            "data":GCenter.instance.encodeTrainingAsJson(training: newTraining) as AnyObject
        ]) { (error, res) in
            if error != nil {
                callback(false)
            } else {
                callback(true)
            }
        }
    }
}
