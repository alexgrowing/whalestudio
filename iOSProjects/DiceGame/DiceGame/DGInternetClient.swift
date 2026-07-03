//
//  DGInternetClient.swift
//  DiceGame
//
//  Created by Alex Chen on 15/5/11.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import Foundation
import DiceGameLib
import WhaleLib

class DGInternetClient : DGGameClient, DGMessageBoxDelegate {
    static func create() -> DGInternetClient? {
        if let sessionIDCreatedByServer = DGClientActions.createSessionID() {
            return DGInternetClient(mBox: DGMessageBox(sessionID: sessionIDCreatedByServer))
        }
        
        return nil
    }
    
    fileprivate let mBox:DGMessageBox
    var delegate:DGInternetClientDelegate?
    
    fileprivate init(mBox:DGMessageBox) {
        self.mBox = mBox
        
        super.init(uuid:WLAccount.getUserUUID()!, sender:mBox)
        
        self.mBox.clientAsReceiver = self
        self.mBox.delegate = self
        self.mBox.longpolling()
    }
    
    override func releaseResources() {
        self.mBox.stopPolling()
    }
    
    fileprivate func errorOnConnecting2Server(_ error: NSError, retryHandler:((() -> Void) -> Void)) {
        self.delegate?.errorOnClientConnecting2Server(error, retryHandler:retryHandler)
    }
}

protocol DGInternetClientDelegate {
    func errorOnClientConnecting2Server(_ error:NSError, retryHandler:((() -> Void) -> Void))
}

class DGMessageBox : DGClientMessageSender {
    fileprivate var delegate:DGMessageBoxDelegate?

    fileprivate let sessionID:String
    fileprivate var clientAsReceiver:DGGameClient?
    fileprivate var shouldBuildConnection:Bool
    
    fileprivate init(sessionID:String) {
        self.sessionID = sessionID
        self.shouldBuildConnection = true
    }
    
    func sendData2Server(_ data: [String:AnyObject]) {
        DGClientActions.sendSessionMessage(self.sessionID, message: data) { (error, jsonResponsed) -> Void in
            self.perform(jsonResponsed, error: error, retryHandler:{(connectionLostHandler) -> Void in
                self.sendData2Server(data)
            })
        }
    }
    
    fileprivate func stopPolling() {
        self.shouldBuildConnection = false
    }
    
    fileprivate func longpolling() {
        if !self.shouldBuildConnection {
            return
        }
        
        DGClientActions.polling(self.sessionID) { (error, response) -> Void in
            self.perform(response, error: error, retryHandler:{(connectionLostHandler) -> Void in
                self.longpolling()
            })
            
            if error == nil {
                self.longpolling()
            }
        }
    }
    
    fileprivate func perform(_ data:[String:AnyObject]?, error:NSError?, retryHandler:@escaping ((() -> Void) -> Void)) {
        DispatchQueue.main.async(execute: {
            if error == nil && data != nil {
                if let connectionOK = data!["LOOP"] as? Bool {
                    if !connectionOK {
                        self.shouldBuildConnection = false
                    } else {
                        return
                    }
                } else {
                    self.clientAsReceiver?.receiveDataFromServer(data!)
                }
            } else {
                self.delegate!.errorOnConnecting2Server(error!, retryHandler:retryHandler)
            }
        })
    }
}

private protocol DGMessageBoxDelegate {
    func errorOnConnecting2Server(_ error:NSError, retryHandler:((() -> Void) -> Void))
}
