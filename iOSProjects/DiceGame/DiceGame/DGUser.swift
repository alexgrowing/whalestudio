//
//  DGUser.swift
//  DiceGame
//
//  Created by apple on 16/2/26.
//  Copyright © 2016年 WhaleStudio. All rights reserved.
//

import Foundation
import GameKit
import WhaleLib

private let DEFAULTS_USER_ACCOUNT_ID = "defaults_user_account_id"
private let DEFAULTS_USER_NAME = "defaults_user_name"

let CURRENT_APP_DOWNLOAD_URL = "https://itunes.apple.com/us/app/jiu-ba-tou-zi/id493902223"
let REVIEW_APP_URL = "http://itunes.apple.com/WebObjects/MZStore.woa/wa/viewContentsUserReviews?id=493902223&pageNumber=0&sortOrdering=2&type=Purple+Software&mt=8"
let LOCAL_APP_DOWNLOAD_URL = "https://itunes.apple.com/us/app/jiu-ba-tou-zi-dan-ji/id1001453467"

/*
class DGUser {
    let uuid:String
    let name:String
    
    // MARK: - Static Methods
    fileprivate static var currentUser : DGUser?
    static func getCurrentUser() -> DGUser? {
        return DGUser.currentUser
    }
    
    fileprivate init(uuid:String, name:String) {
        self.uuid = uuid
        self.name = name
    }
    
    func matchCurrentGameCenterID() -> Bool {
        let localPlayer = GKLocalPlayer.local
        if localPlayer.isAuthenticated && self.uuid == getUUIDFromLocalPlayer(localPlayer) {
            return true
        }
        
        return false
    }
    
    // MARK:- Static Methods
    static func buildCurrentUser(_ uuid:String, name:String) {
        let defaults = UserDefaults.standard
        
        defaults.set(uuid, forKey: DEFAULTS_USER_ACCOUNT_ID)
        defaults.set(name, forKey: DEFAULTS_USER_NAME)
        
        defaults.synchronize()
        
        DGUser.currentUser = DGUser(uuid:uuid, name:name)
    }
    
    static func getUUIDLastSuccessLogin() -> String? {
        if let theUUID = UserDefaults.standard.string(forKey: DEFAULTS_USER_ACCOUNT_ID) {
            return theUUID
        }
        
        return nil
    }
    
    static func getNameLastSuccesLogin() -> String? {
        if let theName = UserDefaults.standard.string(forKey: DEFAULTS_USER_NAME) {
            return theName
        }
        
        return nil
    }
}
*/
