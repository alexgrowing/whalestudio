//
//  AppDelegate.swift
//  VideoEditor
//
//  Created by alex on 2020/1/14.
//  Copyright © 2020 WhaleStudio. All rights reserved.
//

import UIKit

@UIApplicationMain
class AppDelegate: UIResponder, UIApplicationDelegate {

    var window: UIWindow?

    func application(_ application: UIApplication, didFinishLaunchingWithOptions launchOptions: [UIApplication.LaunchOptionsKey: Any]?) -> Bool {
        
        self.window = UIWindow(frame: UIScreen.main.bounds)
        self.window?.rootViewController = UINavigationController(rootViewController: PickingViewController())
        self.window?.makeKeyAndVisible()
        
        return true
    }

}

