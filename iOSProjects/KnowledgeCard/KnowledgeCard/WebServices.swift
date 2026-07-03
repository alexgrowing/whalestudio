//
//  WebServices.swift
//  KnowledgeCard
//
//  Created by alex on 2018/6/5.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import Foundation
import WhaleLib

private let SERVER = "http://kc.whalestudio.cn:9527/"
//private let SERVER = "http://localhost:9527/"

private let REQUEST_LAST_MODIFIED = SERVER + "lastmodified"
private let REQUEST_UPLOAD = SERVER + "upload"
private let REQUEST_DOWNLOAD_ALL = SERVER + "downloadall"
private let REQUEST_UPLOAD_IMAGE = SERVER + "imageupload"
private let REQUEST_EDIT = SERVER + "edit"
private let REQUEST_DELETE = SERVER + "delete"

private let REQUEST_FILE_DIR = SERVER + "kc_user_files/"

class WebServices {
    static func registerAccountOfServer() {
        WLAccount.registerAccountServer(url : SERVER)
    }
    
    static func fetchLastModified(callback:@escaping (_ success:Bool, _ lastModified:Int) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            callback(false, 0)
            return
        }
        
        ajax(REQUEST_LAST_MODIFIED, parameters: [
            "passcode":theUserPasscode as AnyObject
        ]) { (err, res) in
            if err != nil {
                callback(false, 0)
            } else {
                callback(true, res!["lastmodified"] as! Int)
            }
        }
    }
    
    static func uploadTextConfigure(kc:KCKnowledge, callback:@escaping (_ success:Bool, _ lastModified:Int) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            return
        }
        
        ajax(REQUEST_UPLOAD, parameters: [
            "passcode":theUserPasscode as AnyObject,
            "data":kc.encodeAsJson() as AnyObject
        ]) { (err, res) in
            if err != nil {
                callback(false, 0)
            } else {
                callback(true, res!["lastmodified"] as! Int)
            }
        }
    }
    
    static func edit(index:Int, newText:String, callback:@escaping (_ success:Bool, _ lastModified:Int) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            return
        }
        
        ajax(REQUEST_EDIT, parameters: [
            "passcode":theUserPasscode as AnyObject,
            "index":index as AnyObject,
            "text":newText as AnyObject
        ]) { (err, res) in
            if err != nil {
                callback(false, 0)
            } else {
                callback(true, res!["lastmodified"] as! Int)
            }
        }
    }
    
    static func delete(index:Int, callback:@escaping (_ success:Bool, _ lastModified:Int) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            return
        }
        
        ajax(REQUEST_DELETE, parameters: [
            "passcode":theUserPasscode as AnyObject,
            "index":index as AnyObject
        ]) { (err, res) in
            if err != nil {
                callback(false, 0)
            } else {
                callback(true, res!["lastmodified"] as! Int)
            }
        }
    }
    
    static func uploadImage(_ image:UIImage, _ filename:String) {
        WhaleLib.upload(image: image, toURL: REQUEST_UPLOAD_IMAGE, ofFileName: filename)
    }
    
    static func downloadAll(callback:@escaping (_ success:Bool, _ knowsJson:[[
        String:AnyObject]], _ lastModified:Int) -> Void) {
        guard let theUserPasscode = WLAccount.userPasscode else {
            return
        }
        
        ajax(REQUEST_DOWNLOAD_ALL, parameters: [
            "passcode":theUserPasscode as AnyObject
        ]) { (err, res) in
            if err != nil {
                callback(false, [[String:AnyObject]](), 0)
            } else {
                callback(true, res!["knows"] as! [[String:AnyObject]], res!["lastmodified"] as! Int)
            }
        }
    }
    
    static func urlOf(filename:String) -> URL {
        return URL(string: REQUEST_FILE_DIR + filename)!
    }
}
