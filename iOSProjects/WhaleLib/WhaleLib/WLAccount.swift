//
//  WLAccount.swift
//  WhaleLib
//
//  Created by alex on 2018/5/26.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import Foundation
import GameKit

//
//  WebServices.swift
//  Gym
//
//  Created by alex on 2018/2/28.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import Foundation

private var SERVER:String?

//private let SERVER_FIGURE_URL = "http://127.0.0.1:4004"
private let SERVER_FIGURE_URL = "http://www.whalestudio.cn:4004"
private let SERVER_FIGURE_UPLOAD_URL = "\(SERVER_FIGURE_URL)/figureupload"

private func REQUEST_ASK_4_VERIRY_CODE() -> String {
    return SERVER! + "a4vc"
}

private func REQUEST_QUICK() -> String {
    return SERVER! + "quick"
}

private func REQUEST_REGISTER_BY_GAMECENTER() -> String {
    return SERVER! + "loginbygamecenter"
}

private func REQUEST_CREATE_QUICK_ACCOUNT() -> String {
    return SERVER! + "createquickaccount"
}

private let WLACCOUNT_USER_PASSCODE_KEY = "WLACCOUNT_USER_PASSCODE_KEY"

public enum DICEGAME_AUTH {
    case login_successfully
    case should_popup_gamecenter_login_first(gamecenterLoginViewController:UIViewController)
    case login_failed
}

private var triedOnceOfGameCenterLogin = false

public class WLAccount {
    public static func registerAccountServer(url:String) {
        SERVER = url
    }
    
    private static var userPasscode:String? {
        didSet {
            if userPasscode != nil {
                let data = NSKeyedArchiver.archivedData(withRootObject: WLAccount.userPasscode as Any)
                let def = UserDefaults.standard
                def.set(data, forKey: WLACCOUNT_USER_PASSCODE_KEY)
                def.synchronize()
            } else {
                UserDefaults.standard.removeObject(forKey: WLACCOUNT_USER_PASSCODE_KEY)
            }
        }
    }
    
    private static var userUUID:String?
    
    public static func getUserUUID() -> String? {
        return userUUID
    }
    
    public static func quickLogin(callback:@escaping (_ success:Bool) -> Void) {
        let def = UserDefaults.standard
        
        if let savedData = def.object(forKey: WLACCOUNT_USER_PASSCODE_KEY) as? Data {
            if let theUserPasscode = NSKeyedUnarchiver.unarchiveObject(with: savedData) as? String {
                WLAccount.ajaxQuickLogin(passcode: theUserPasscode) { (uuid, errorMessage) in
                    if uuid != nil {
                        WLAccount.userUUID = uuid
                        callback(true)
                    } else {
                        callback(false)
                    }
                }
                
                return
            }
        }
        
        callback(false)
    }
    
    public static let ERROR_LOGIN_WRONG_PASSWORD = "ERROR_LOGIN_WRONG_PASSWORD"
    public static let ERROR_LOGIN_ACCOUNT_NOT_FOUND = "ERROR_LOGIN_ACCOUNT_NOT_FOUND"
    
    fileprivate static let ERROR_FORMAT_OF_EMAIL_IS_NOT_RIGHT = "ERROR_FORMAT_OF_EMAIL_IS_NOT_RIGHT"
    fileprivate static let ERROR_PASSWORD_SHOULD_CONTAIN_NUMBERS_AND_LETTERS = "ERROR_PASSWORD_SHOULD_CONTAIN_NUMBERS_AND_LETTERS"
    fileprivate static let ERROR_VERIFY_CODE_NOT_MATCH = "ERROR_VERIFY_CODE_NOT_MATCH"
    fileprivate static let ERROR_QUCIK_LOGIN_FAILED = "ERROR_QUCIK_LOGIN_FAILED"
    fileprivate static let ERROR_VERIFY_CODE_SENT_TOO_FREQUENTLY = "ERROR_VERIFY_CODE_SENT_TOO_FREQUENTLY"
    
    static func ask4VerifyCode(email:String, callback:@escaping (_ success:Bool, _ errorMessage:WLErrorI18N?) -> Void) {
        ajax(REQUEST_ASK_4_VERIRY_CODE(), parameters: ["email":email as AnyObject]) { (error, res) in
            if error != nil {
                callback(false, i18n(error!.localizedDescription))
            } else if res!["error"] != nil {
                callback(false, i18n(res!["error"] as? String))
            } else {
                callback(true, nil)
            }
        }
    }
    
    private static func ajaxQuickLogin(passcode:String, callback:@escaping (_ uuid:String?, _ errorMessage:WLErrorI18N?) -> Void) {
        ajax(REQUEST_QUICK(), sync:true, parameters: ["passcode":passcode as AnyObject]) { (error, res) in
            if error != nil {
                callback(nil, i18n(error!.localizedDescription))
            } else {
                if let theUUID = res!["uuid"] as? String {
                    callback(theUUID, nil)
                } else {
                    callback(nil, i18n(res!["error"] as? String))
                }
            }
        }
    }
    
    public static func loginGameCenterOnly(callback:@escaping(_ loginVC:UIViewController) -> Void) {
        let localPlayer = GKLocalPlayer.local
        
        localPlayer.authenticateHandler = {(loginViewController, error) -> Void in
            if loginViewController != nil {
                callback(loginViewController!)
            }
        }
    }
    
    public static func authLoginByGameCenterOrDirectly(callback:@escaping (DICEGAME_AUTH) -> Void) {
        if triedOnceOfGameCenterLogin {
            WLAccount.loginByCreateQuickAccount { (success) in
                if success {
                    callback(.login_successfully)
                } else {
                    callback(.login_failed)
                }
            }
            
            return
        }
        
        let localPlayer = GKLocalPlayer.local
        localPlayer.authenticateHandler = {(loginViewController, error) -> Void in
            triedOnceOfGameCenterLogin = true
            var didFailLoginByGameCenter = false
            
            if error != nil {
                // 如果登录GameCenter有error,在当前系统没有User时,标记在最后以忽略GameCenter的方式登录
                printLog("\(String(describing: error))")
                
                if let _ = WLAccount.userPasscode {
                    // 虽然GameCenter验证有error,但如果CurrentUser已经存在了,那也就不用管了
                } else {
                    didFailLoginByGameCenter = true
                }
            } else if localPlayer.isAuthenticated {
                WLAccount.ajaxLoginBy(idOfGameCenter: localPlayer.playerID, nameOfGameCenter: localPlayer.alias, callback: { (success, passcode, uuid, isNewAccount) in
                    DispatchQueue.main.async {
                        if success {
                            WLAccount.userPasscode = passcode
                            WLAccount.userUUID = uuid
                            printLog("-----------------\(isNewAccount!)------------------")
                            if isNewAccount! {
                                localPlayer.loadPhoto(for: .normal, withCompletionHandler: { (photo, error) in
                                    if photo != nil {
                                        WLAccount.uploadFigure(image: photo!, callback: { (success) in
                                            // do nothing
                                        })
                                    }
                                })
                            }
                            
                            print("gamecenter login successfully")
                            callback(.login_successfully)
                        } else {
                            WLAccount.loginByCreateQuickAccount(callback: { (success2) in
                                if success2 {
                                    print("create account login successfully")
                                    callback(.login_successfully)
                                } else {
                                    callback(.login_failed)
                                }
                            })
                        }
                    }
                })
            } else if loginViewController != nil {
                /*
                 * GameCenter登录ViewController可用时,就弹出来让登录吧,即使当前系统已经有的User也弹出来
                 * 因为当前系统的User可能非GameCenter帐号,也可能是别的GameCenter帐号的,这两种情况都不大好
                 */
                callback(.should_popup_gamecenter_login_first(gamecenterLoginViewController: loginViewController!))
            } else {
                // 其他情况,同error时的处理方法一样
                if let _ = WLAccount.userPasscode {
                    // do nothing
                } else {
                    didFailLoginByGameCenter = true
                }
            }
            
            if didFailLoginByGameCenter {
                WLAccount.loginByCreateQuickAccount(callback: { (success2) in
                    if success2 {
                        print("create account login successfully")

                        callback(.login_successfully)
                    } else {
                        callback(.login_failed)
                    }
                })
            }
        }
    }
    
    private static func loginByCreateQuickAccount(callback:@escaping(Bool) -> Void) {
        WLAccount.ajaxCreateQuickAccount(callback: { (success, passcode, uuid) in
            if success {
                WLAccount.userPasscode = passcode
                WLAccount.userUUID = uuid
                callback(true)
            } else {
                callback(false)
            }
        })
    }
    
    private static func ajaxCreateQuickAccount(callback:@escaping(Bool, String?, String?) -> Void) {
        ajax(REQUEST_CREATE_QUICK_ACCOUNT(), parameters: [
            "dname":UIDevice.current.name as AnyObject
        ]) { (error, res) in
            if error != nil {
                callback(false, nil, nil)
            } else {
                if let thePasscode = res!["passcode"] as? String {
                    if let theUUID = res!["uuid"] as? String {
                        callback(true, thePasscode, theUUID)
                        return
                    }
                }
                
                callback(false, nil, nil)
            }
        }
    }
    
    private static func ajaxLoginBy(idOfGameCenter:String, nameOfGameCenter:String, callback:@escaping (Bool, String?, String?, Bool?) -> Void) {
        ajax(REQUEST_REGISTER_BY_GAMECENTER(), parameters: [
            "gamecenterid" : idOfGameCenter as AnyObject,
            "gamecentername" : nameOfGameCenter as AnyObject
        ]) { (error, res) in
            if error != nil {
                callback(false, nil, nil, nil)
            } else {
                if let thePasscode = res!["passcode"] as? String {
                    if let theUUID = res!["uuid"] as? String {
                        if let isNewAccount = res!["newaccount"] as? Bool {
                            callback(true, thePasscode, theUUID, isNewAccount)
                        }
                        return
                    }
                }
                
                callback(false, nil, nil, nil)
            }
        }
    }
    
    // MARK: - Upload Image
    public static func uploadFigure(image:UIImage, callback:@escaping (Bool) -> Void) {
        __uploadFigure__(image: image, times: 0, callback: callback)
    }
    
    private static func __uploadFigure__(image:UIImage, times:Int, callback:@escaping (Bool) -> Void) {
        guard let theUUID = WLAccount.getUserUUID() else {
            callback(false)
            return
        }
        //把图片转换成imageDate格式
        let imageData = image.jpegData(compressionQuality: 1.0)
        /*
         //建立请求对象
         let req = NSMutableURLRequest(url:URL(string:SERVER_UPLOAD_URL)!, cachePolicy:NSURLRequest.CachePolicy.reloadIgnoringLocalCacheData, timeoutInterval:REQUEST_TIMEOUT)
         req.httpMethod = "POST"
         
         //一连串上传头标签
         let boundary = "---------------------------14737809831466499882746641449"
         let contentType = "multipart/form-data; boundary=\(boundary)"
         req.addValue(contentType, forHTTPHeaderField: "Content-Type")
         
         let body = NSMutableData()
         body.append("\r\n--\(boundary)\r\n".data(using: String.Encoding.utf8)!)
         body.append("Content-Disposition: form-data; name=\"userfile\"; filename=\"\(filename)\"\r\n".data(using: String.Encoding.utf8)!)
         body.append("Content-Type: application/octet-stream\r\n\r\n".data(using: String.Encoding.utf8)!)
         body.append(NSData(data: imageData!) as Data)
         body.append("\r\n--\(boundary)--\r\n".data(using: String.Encoding.utf8)!)
         req.httpBody = body as Data
         */
        
        var req = URLRequest(url:URL(string:SERVER_FIGURE_UPLOAD_URL)!, cachePolicy:NSURLRequest.CachePolicy.reloadIgnoringLocalCacheData, timeoutInterval:REQUEST_TIMEOUT)
        req.httpMethod = "POST"
        
        //一连串上传头标签
        let boundary = "---------------------------14737809831466499882746641449"
        let contentType = "multipart/form-data; boundary=\(boundary)"
        req.addValue(contentType, forHTTPHeaderField: "Content-Type")
        
        let body = NSMutableData()
        body.append("\r\n--\(boundary)\r\n".data(using: String.Encoding.utf8)!)
        body.append("Content-Disposition: form-data; name=\"userfile\"; filename=\"\(theUUID).jpg\"\r\n".data(using: String.Encoding.utf8)!)
        body.append("Content-Type: application/octet-stream\r\n\r\n".data(using: String.Encoding.utf8)!)
        body.append(NSData(data: imageData!) as Data)
        body.append("\r\n--\(boundary)--\r\n".data(using: String.Encoding.utf8)!)
        req.httpBody = body as Data
        
        URLSession.shared.dataTask(with: req) { (data, res, error) in
            if let theError = error {
                printLog("upload figure(\(times)) failed:\(theError)")
                
                if times <= 2 {
                    __uploadFigure__(image: image, times: times + 1, callback: callback)
                } else {
                    callback(false)
                }
                
                return
            }
            
            if let jo = (try? JSONSerialization.jsonObject(with: data!, options: JSONSerialization.ReadingOptions.mutableContainers) as? [String:AnyObject]) {
                if let isSuccess = jo["success"] as? String, isSuccess == "OK" {
                    callback(true)
                } else {
                    callback(false)
                }
            }
            }.resume()
    }
}

private func i18n(_ errorMessage:String?) -> WLErrorI18N? {
    if let message = errorMessage {
        return WLErrorI18N(message:message)
    }
    
    return nil
}

public class WLErrorI18N : NSObject {
    let raw:String
    
    init(message:String) {
        self.raw = message
    }
    
    func i18n() -> String {
        switch self.raw {
        case WLAccount.ERROR_FORMAT_OF_EMAIL_IS_NOT_RIGHT:
            return "邮件格式不正确"
        case WLAccount.ERROR_LOGIN_WRONG_PASSWORD:
            return "密码错误"
        case WLAccount.ERROR_LOGIN_ACCOUNT_NOT_FOUND:
            return "帐号不存在"
        case WLAccount.ERROR_VERIFY_CODE_NOT_MATCH:
            return "验证码不匹配"
        case WLAccount.ERROR_QUCIK_LOGIN_FAILED:
            return "快速登录失败"
        case WLAccount.ERROR_VERIFY_CODE_SENT_TOO_FREQUENTLY:
            return "验证码请求过于频繁"
        case WLAccount.ERROR_PASSWORD_SHOULD_CONTAIN_NUMBERS_AND_LETTERS:
            return "密码必须是字母与数字的组合"
        default:
            return self.raw
        }
    }
    
    override public var description:String {
        return self.i18n()
    }
}
