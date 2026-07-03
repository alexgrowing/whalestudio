//
//  AppDelegate.swift
//  DiceGame
//
//  Created by Alex Chen on 15/4/23.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import UIKit
import UserNotifications
import WhaleLib

@UIApplicationMain
class AppDelegate: UIResponder, UIApplicationDelegate, WXApiDelegate {
    var window: UIWindow?
    /*
     * 启动:didFinishLaunching -> didBecomeActive
     * Home键或者电源键:willResignActive -> didEnterBackground
     * 从主屏幕回来:willEnterForeground -> didBecomeActive
     * 程序运行时,双击Home键:willResignActive
     * --从任务管理,回到程序运行时:didBecomeActive
     * 程序运行时,双击Home键:willResignActive
     * --从任务管理,选择非当前程序运行时:didEnterBackground
     * --再次双击Home进行任务管理,关闭当前程序:Message from debugger: Terminated due to signal 9（程序居然没有执行willTerminate而直接抛错了）
     * 程序运行时,双击Home键:willResignActive
     * --关闭该程序:didEnterBackground -> willTerminate
     */


    func application(_ application: UIApplication, didFinishLaunchingWithOptions launchOptions: [UIApplication.LaunchOptionsKey: Any]?) -> Bool {
//         println("application didFinishLaunching")
        // Override point for customization after application launch.
        DGClientActions.registerAccountOfServer()
        WXApi.registerApp("wx8724139126181b64")
        self.registerNotification()
        
        // Override point for customization after application launch.
        self.window = UIWindow(frame: UIScreen.main.bounds)
        // Override point for customization after application launch.
        self.window!.backgroundColor = UIColor.white
        self.window!.makeKeyAndVisible()
        
        // approach without storyboard
        // Step 1: create view controller instance
        // Step 2: create a navigation controller with view controller instance as root
        // Step 3: navigation controller instance is set as rootviewcontroller of the window
        self.window!.rootViewController = DGStartupViewController()
        
        return true
    }
    
    fileprivate func registerNotification() {
        /*
        let firstAction = UIMutableUserNotificationAction()
        firstAction.identifier = "FIRST_ACTION"
        firstAction.title = "First Action"
        firstAction.activationMode = UIUserNotificationActivationMode.Background
        firstAction.destructive = true
        firstAction.authenticationRequired = false
        
        let secondAction = UIMutableUserNotificationAction()
        secondAction.identifier = "SECOND_ACTION"
        secondAction.title = "Second Action"
        secondAction.activationMode = UIUserNotificationActivationMode.Foreground
        secondAction.destructive = false
        secondAction.authenticationRequired = false
        
        let thirdAction = UIMutableUserNotificationAction()
        thirdAction.identifier = "THIRD_ACTION"
        thirdAction.title = "Third Action"
        thirdAction.activationMode = UIUserNotificationActivationMode.Background
        thirdAction.destructive = true
        thirdAction.authenticationRequired = false
*/
        
//        let firstCategory = UIMutableUserNotificationCategory()
//        firstCategory.identifier = NOTIFICATION_CATEGORY_START_GAME
//
//        let categories:Set<UIMutableUserNotificationCategory> = [firstCategory]
//        let types: UIUserNotificationType = [UIUserNotificationType.alert, UIUserNotificationType.badge]
//        let mysettings = UIUserNotificationSettings(types: types, categories: categories)
//        UIApplication.shared.registerUserNotificationSettings(mysettings)
    }
    /*
    func application(_ application: UIApplication, didRegister notificationSettings: UIUserNotificationSettings) {
        application.cancelAllLocalNotifications()
        
        let notification = UILocalNotification()
        notification.category = NOTIFICATION_CATEGORY_START_GAME
        notification.alertBody = "大侠，快来领取手气卡"
        notification.fireDate = Date(timeIntervalSinceNow: 60 * 60 * 24)
        
        application.scheduleLocalNotification(notification)
    }
 */
    
    /*
    func application(_ application: UIApplication, handleActionWithIdentifier identifier: String?, for notification: UILocalNotification, completionHandler: @escaping () -> Void) {
        /*
        if let id = identifier {
            switch id {
            case "FIRST_ACTION":
                NSNotificationCenter.defaultCenter().postNotificationName("actionOnePressed", object: nil)
            case "SECOND_ACTION":
                NSNotificationCenter.defaultCenter().postNotificationName("actionTwoPressed", object: nil)
            default:
                break
            }
            
            completionHandler()
        }
*/
    }
 */

    func applicationWillResignActive(_ application: UIApplication) {
        // Sent when the application is about to move from active to inactive state. This can occur for certain types of temporary interruptions (such as an incoming phone call or SMS message) or when the user quits the application and it begins the transition to the background state.
        // Use this method to pause ongoing tasks, disable timers, and throttle down OpenGL ES frame rates. Games should use this method to pause the game.
//         println("application will resign active")
    }

    func applicationDidEnterBackground(_ application: UIApplication) {
        // Use this method to release shared resources, save user data, invalidate timers, and store enough application state information to restore your application to its current state in case it is terminated later.
        // If your application supports background execution, this method is called instead of applicationWillTerminate: when the user quits.
//         println("application did enter background")
    }

    func applicationWillEnterForeground(_ application: UIApplication) {
        // Called as part of the transition from the background to the inactive state; here you can undo many of the changes made on entering the background.
//         println("application will enter foreground")
    }

    func applicationDidBecomeActive(_ application: UIApplication) {
        // Restart any tasks that were paused (or not yet started) while the application was inactive. If the application was previously in the background, optionally refresh the user interface.
//         println("application did become active")
    }

    func applicationWillTerminate(_ application: UIApplication) {
        // Called when the application is about to terminate. Save data if appropriate. See also applicationDidEnterBackground:.
//        NotificationCenter.default.post(name: Notification.Name(rawValue: NOTIFICATION_APPLICATION_WILL_TERMINATED), object: nil)
    }

    func application(_ application: UIApplication, handleOpen url: URL) -> Bool {
//        println("1.\(url)")
        self.processURL(url)
        if WXApi.handleOpen(url, delegate: self) {
            return true
        }
        /*
        Tencent
        else if TencentOAuth.HandleOpenURL(url) {
            return true
        }
*/
        
        return false
    }
    
    func application(_ application: UIApplication, open url: URL, sourceApplication: String?, annotation: Any) -> Bool {
//        println("2.\(url)\t\(sourceApplication)")
        self.processURL(url)

        if WXApi.handleOpen(url, delegate: self) {
            return true
        }
        /*
        Tencent
        else if TencentOAuth.HandleOpenURL(url) {
            return true
        }
*/
        
        return false
    }
    
    fileprivate func processURL(_ url:URL) {
        /*
        println("url.schema:\(url.scheme)")
        println("url.host:\(url.host)")
        println("url.port:\(url.port)")
        println("url.path:\(url.path)")
        println("url.relativePath:\(url.relativePath)")
        println("url.pathComponents:\(url.pathComponents)")
        println("url.parameterString:\(url.parameterString)")
        println("url.query:\(url.query)")
        println("url.fragment:\(url.fragment)")
*/
        
//        if let host = url.host {
//            let pathComponents = url.pathComponents
//            // cy.i10l.dicegame://go2room/ak47
//            if host == "go2room" && pathComponents.count >= 2 {
//                let roomID = pathComponents[1]
//                NotificationCenter.default.post(name: Notification.Name(rawValue: NOTIFICATION_INTO_PRIVATE_ROOM), object: roomID)
//            }
//        }
    }
    
    /*
     *onReq是微信终端向第三方程序发起请求，要求第三方程序响应。第三方程序响应完后必须调用sendRsp返回。在调用sendRsp返回时，会切回到微信终端程序界面。
     */
    func onReq(_ req: BaseReq!) {

    }
    
    /*
     *如果第三方程序向微信发送了sendReq的请求，那么onResp会被回调。sendReq请求调用后，会切到微信终端程序界面。
     */
    func onResp(_ resp: BaseResp!) {

    }
}

/*
extension AppDelegate {
    func application(_ application: UIApplication, continue userActivity: NSUserActivity, restorationHandler: @escaping ([Any]?) -> Void) -> Bool {
        if userActivity.activityType == NSUserActivityTypeBrowsingWeb {
            let webPageUrl = userActivity.webpageURL!
            if !handleUniversalLink(url: webPageUrl) {
                UIApplication.shared.openURL(webPageUrl)
            }
        }
        
        return true
    }
    
    private func handleUniversalLink(url:URL) -> Bool {
        if let host = url.host {
            NSLog("url:%s;host:%s;path:%s", url.absoluteString, host, url.pathComponents)
            
            return true
            /*
            switch host {
            case "":
                if pathComponents.count >= 4 {
                    switch (pathComponents[0], pathComponents[1], pathComponents[2], pathComponents[3]) {
                    case ("/", "path", "to", let something):
                        if validateSomething(something) {
                            presentSomethingViewController(something)
                            return true
                        }
                    default:
                        return false
                    }
                }
            default:
                return false
            }
 */
        }
        
        return false
    }
}
 */

