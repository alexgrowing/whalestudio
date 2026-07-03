//
//  DGStartupViewController.swift
//  DiceGame
//
//  Created by Alex Chen on 15/4/23.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import UIKit
import GameKit
import DiceGameLib
import WhaleLib
import GoogleMobileAds

let NOTIFICATION_CATEGORY_START_GAME = "NOTIFICATION_CATEGORY_START_GAME"

let DEFAULTS_PERMISSION_UPLOAD_YOUR_SCORE = "DEFAULTS_PERMISSION_UPLOAD_YOUR_SCORE"

class DGStartupViewController : UIViewController, /*TencentSessionDelegate,*/ GKGameCenterControllerDelegate, GADBannerViewDelegate {
    fileprivate var buttonView: UIView!
    fileprivate var belowButtonView:UIView!
    fileprivate var loginFailedView: UIView!
    
    fileprivate var loadingView: UIView!
    fileprivate var loadingIndicator: UIActivityIndicatorView!
    fileprivate var loadingInfoLabel:UILabel!
    
    /*private var tencentOAuth:TencentOAuth!*/
    
    fileprivate var markLabel:UILabel!
    fileprivate var currentMissions = [String]() {
        didSet {
            self.markLabel.text = "\(self.currentMissions.count)"
        }
    }
    
    fileprivate var justShowRankOfGameCenter = false
    
    override var prefersStatusBarHidden : Bool {
        return true
    }
    
    override func viewDidLoad() {
        // 腾讯的SDK很神经病,一定要调用一下这个,否则连分享到QQ或QZone都不行
        /*self.tencentOAuth = TencentOAuth(appId: TENCENT_APP_ID, andDelegate: self)*/
        
        let frameSize = self.view.bounds.size

        DGUIUtils.addMainBackgroundImageViewTo(parentView: self.view)
        
        let contentView = UIView()
        self.view.addSubview(contentView)
        contentView.snp.makeConstraints { (make) in
            make.edges.equalTo(self.view.safeAreaLayoutGuide.snp.edges)
        }
        
        let widthOfSmallHomeButton:CGFloat = 120
        let heightOfHomeButton:CGFloat = 80
        let verticalPaddingOfHomeButton:CGFloat = 20
        let horizontalPaddingOfHomeButton:CGFloat = 20
        let widthOfLargeHomeButton:CGFloat = widthOfSmallHomeButton*2+horizontalPaddingOfHomeButton
        
        let widthOfCardArea:CGFloat = widthOfLargeHomeButton
        let heightOfCardArea:CGFloat = heightOfHomeButton*3+verticalPaddingOfHomeButton*2
        
        // buttonView
        self.buttonView = UIView()
        contentView.addSubview(self.buttonView)
        self.buttonView.snp.makeConstraints { (make) in
            make.width.equalTo(widthOfCardArea)
            make.height.equalTo(heightOfCardArea)
            make.center.equalTo(contentView)
        }
        
        let quickStartButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Quick_Start", comment:""), target: self, action: #selector(DGStartupViewController.playWithInternetQuickStartOf4))
        self.buttonView.addSubview(quickStartButton)
        quickStartButton.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.top.equalTo(0)
            make.width.equalTo(widthOfSmallHomeButton)
            make.height.equalTo(heightOfHomeButton)
        }
        
        let ringButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Arena", comment:""), target: self, action: #selector(DGStartupViewController.playWithRing))
        self.buttonView.addSubview(ringButton)
        ringButton.snp.makeConstraints { (make) in
            make.right.equalTo(0)
            make.top.equalTo(0)
            make.width.equalTo(widthOfSmallHomeButton)
            make.height.equalTo(heightOfHomeButton)
        }
        
        let createPrivateRoomButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Create_Private_Room", comment:""), target: self, action: #selector(DGStartupViewController.playWithInternetCreateANewRoom))
        self.buttonView.addSubview(createPrivateRoomButton)
        createPrivateRoomButton.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.top.equalTo(quickStartButton.snp.bottom).offset(verticalPaddingOfHomeButton)
            make.width.equalTo(widthOfSmallHomeButton)
            make.height.equalTo(heightOfHomeButton)
        }
        
        let go2PrivateRoomButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Go_2_Private_Room", comment:""), target: self, action: #selector(DGStartupViewController.playWithInternetGo2ASpecifiedRoom))
        self.buttonView.addSubview(go2PrivateRoomButton)
        go2PrivateRoomButton.snp.makeConstraints { (make) in
            make.right.equalTo(0)
            make.top.equalTo(createPrivateRoomButton.snp.top)
            make.width.equalTo(widthOfSmallHomeButton)
            make.height.equalTo(heightOfHomeButton)
        }
        
        let rankButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Rank", comment:""), target: self, action: #selector(DGStartupViewController.showRankOfPermission))
        self.buttonView.addSubview(rankButton)
        rankButton.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.top.equalTo(createPrivateRoomButton.snp.bottom).offset(verticalPaddingOfHomeButton)
            make.width.equalTo(widthOfSmallHomeButton)
            make.height.equalTo(heightOfHomeButton)
        }
        
        let informationButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Information", comment:""), target: self, action: #selector(DGStartupViewController.showSettings))
        self.buttonView.addSubview(informationButton)
        informationButton.snp.makeConstraints { (make) in
            make.right.equalTo(0)
            make.top.equalTo(rankButton.snp.top)
            make.width.equalTo(widthOfSmallHomeButton)
            make.height.equalTo(heightOfHomeButton)
        }
        
        // belowButtonView
        let sizeOfBelowButtons:CGFloat = 40
        
        self.belowButtonView = UIView()
        contentView.addSubview(self.belowButtonView)
        self.belowButtonView.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.bottom.equalTo(-10)
            make.height.equalTo(sizeOfBelowButtons)
        }
        let imageOfBelowButtons = ["recommend.png", "download.png", "feedback.png", "mission.png"]
        let actionsOfBelowButtons = [#selector(zan), #selector(downloadLocalVersion), #selector(showFeedback), #selector(showMission)]
        for buttonIndex in 0 ..< imageOfBelowButtons.count {
            let btn = WLUI.createUIButton(image: UIImage(named: imageOfBelowButtons[buttonIndex])!, margin:0, target: self, action: actionsOfBelowButtons[buttonIndex])
            self.belowButtonView.addSubview(btn)
            btn.snp.makeConstraints { (make) in
                make.width.equalTo(sizeOfBelowButtons)
                make.height.equalTo(sizeOfBelowButtons)
                make.centerY.equalTo(sizeOfBelowButtons/2)
                make.centerX.equalTo(frameSize.width / CGFloat(imageOfBelowButtons.count + 1) * CGFloat(buttonIndex + 1))
            }
            
            if buttonIndex == imageOfBelowButtons.count - 1 {
                let sizeOfMarkLabel:CGFloat = 20
                
                self.markLabel = WLUI.createUILabel(text: "0")
                self.belowButtonView.addSubview(self.markLabel)
                self.markLabel.snp.makeConstraints { (make) in
                    make.width.equalTo(sizeOfMarkLabel)
                    make.height.equalTo(sizeOfMarkLabel)
                    make.top.equalTo(btn.snp.top).offset(-sizeOfMarkLabel/2)
                    make.left.equalTo(btn.snp.right).offset(-sizeOfMarkLabel/2)
                }
                self.markLabel.backgroundColor = UIColor.red
                self.markLabel.layer.cornerRadius = sizeOfMarkLabel/2
                self.markLabel.clipsToBounds = true
            }
        }
        
        // UpdateClientView
        let distance2CenterYOfCardArea:CGFloat = 40
        
        self.loginFailedView = UIView()
        contentView.addSubview(self.loginFailedView)
        self.loginFailedView.snp.makeConstraints { (make) in
            make.width.equalTo(widthOfCardArea)
            make.height.equalTo(heightOfCardArea)
            make.center.equalTo(contentView)
        }
        
        let loginFailedTitleLabel = DGUIUtils.createMiddleUILabel(initString: NSLocalizedString("Login_Failed", comment:""))
        self.loginFailedView.addSubview(loginFailedTitleLabel)
        loginFailedTitleLabel.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.height.equalTo(DGFonts.MIDDLE_FONT_SIZE)
            make.bottom.equalTo(self.loginFailedView.snp.centerY).offset(-distance2CenterYOfCardArea)
        }
        
//        let continueAfterUpdateLabel = DGUIUtils.createUILabel(initString:NSLocalizedString("Continue_Game_After_Update", comment:""))
//        self.loginFailedView.addSubview(continueAfterUpdateLabel)
//        continueAfterUpdateLabel.snp.makeConstraints { (make) in
//            make.left.equalTo(0)
//            make.right.equalTo(0)
//            make.height.equalTo(DGFonts.NORMAL_FONT_SIZE)
//            make.centerY.equalTo(self.loginFailedView)
//        }
        
        let retryButton = DGUIUtils.createUIButton(titleOfButton: NSLocalizedString("Retry", comment:""), target: self, action: #selector(DGStartupViewController.retryLogin))
        retryButton.setTitleColor(DGColors.HIGHLIGHT_COLOR, for: UIControl.State.normal)
        self.loginFailedView.addSubview(retryButton)
        retryButton.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.top.equalTo(self.loginFailedView.snp.centerY).offset(distance2CenterYOfCardArea)
            make.height.equalTo(DGFonts.NORMAL_FONT_SIZE)
        }
        
        
        // LoadingView
        self.loadingView = UIView()
        contentView.addSubview(self.loadingView)
        self.loadingView.snp.makeConstraints { (make) in
            make.width.equalTo(widthOfCardArea)
            make.height.equalTo(heightOfCardArea)
            make.center.equalTo(contentView)
        }
        
        self.loadingIndicator = UIActivityIndicatorView()
        self.loadingView.addSubview(self.loadingIndicator)
        self.loadingIndicator.snp.makeConstraints { (make) in
            make.center.equalTo(self.loadingView)
            make.width.equalTo(20)
            make.height.equalTo(20)
        }
        
        self.loadingInfoLabel = DGUIUtils.createMiddleUILabel(initString: "")
        self.loadingView.addSubview(self.loadingInfoLabel)
        self.loadingInfoLabel.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.height.equalTo(DGFonts.MIDDLE_FONT_SIZE)
            make.top.equalTo(self.loadingIndicator.snp.bottom).offset(distance2CenterYOfCardArea)
        }
        
        // view did load
        super.viewDidLoad()
        
        self.login()
    }
    
    override func viewDidAppear(_ animated: Bool) {
        super.viewDidAppear(animated)
        
        // Always Show View
        let adSize = GADAdSizeFullWidthPortraitWithHeight(DGUIUtils.HEIGHT_OF_AD) // 当View Did Appear之后,GADAdSizeFullWidthPortraitWithHeight才能拿到屏幕宽度
        let admobBannerView = GADBannerView(adSize: adSize, origin: CGPoint(x: 0, y: self.view.safeAreaInsets.top))
        self.view.addSubview(admobBannerView)
        admobBannerView.snp.makeConstraints { (make) in
            make.width.equalTo(self.view.bounds.width)
            make.height.equalTo(DGUIUtils.HEIGHT_OF_AD)
            make.centerX.equalTo(self.view)
            make.top.equalTo(self.view.safeAreaInsets.top)
        }
        admobBannerView.rootViewController = self
        let req = GADRequest()
        /*
        * 这是正式的UnitID
        */
        admobBannerView.adUnitID = "ca-app-pub-9409825561491259/8203934498"
        req.testDevices = [kGADSimulatorID, "958fb333948ef8d09afed7c9eafea6e9", "ea4270fcbcf9c9a7750676e84945faf6"]
        admobBannerView.delegate = self
        /*
        6p (414.0, 736.0)
        6  (375.0, 667.0)
        5  (320.0, 568.0)
        4  (320.0, 480.0)
        */
        admobBannerView.load(req)
    }
    
    // MARK: - Instance Method
    fileprivate func login() {
        self.switchStartupCenterView(.loginView)
        
        WLAccount.quickLogin { (success) in
            if success {
                print("quick login successfully")
                self.loginCallback(true, gameCenterLoginTried: false)
            } else {
                WLAccount.authLoginByGameCenterOrDirectly(callback: self.afterAuthLogin)
            }
        }
    }
    
    private func afterAuthLogin(auth:DICEGAME_AUTH) {
        switch auth {
        case .login_successfully:
            self.loginCallback(true, gameCenterLoginTried: true)
            break
        case .login_failed:
            self.loginCallback(false, gameCenterLoginTried: true)
            break
        case let .should_popup_gamecenter_login_first(loginViewController):
            self.present(loginViewController, animated: true) {
                // do nothing
            }
            break
        }
    }
    
    fileprivate func loginCallback(_ success:Bool, gameCenterLoginTried:Bool) {
        if !gameCenterLoginTried {
            WLAccount.loginGameCenterOnly { (vc) in
                self.present(vc, animated: true, completion: {
                    // do nothing
                })
            }
        }
        
        DispatchQueue.main.async(execute: {
            if success {
                self.switchStartupCenterView(.buttonView)
            } else {
                self.switchStartupCenterView(.loginFailedView)
            }
        })
    }
    
    fileprivate func animateShowTipOfUnmatchedGameCenterID() {
        // todo
    }
    
    fileprivate func checkMyMission() {
        DGClientActions.checkMyMission { (mission) -> Void in
            DispatchQueue.main.async(execute: {
                self.currentMissions = mission
            })
        }
    }
    
    // MARK: - GKGameCenterControllerDelegate
    func gameCenterViewControllerDidFinish(_ gameCenterViewController: GKGameCenterViewController) {
        self.dismiss(animated: true, completion: nil)
        if !self.justShowRankOfGameCenter {
            self.switchStartupCenterView(.loginView)
            self.justShowRankOfGameCenter = false
        }
    }
    
    // MARK: - GADBannerViewDelegate
    func adViewWillLeaveApplication(_ adView: GADBannerView) {
        DGClientActions.notifyServerIHaveClickedAd()
    }
    
    // MARK: - IBAction
    func playWithInternetQuickStart() {
        self.playOnInternet(DGInternetAction.quickStart)
    }
    
    @objc func playWithInternetQuickStartOf4() {
        self.playOnInternet(DGInternetAction.quickStart4)
    }
    
    @objc func playWithRing() {
        self.playOnInternet(DGInternetAction.ring)
    }
    
    @objc func playWithInternetCreateANewRoom() {
        self.playOnInternet(DGInternetAction.createAPrivteRoom)
    }
    
    @objc func playWithInternetGo2ASpecifiedRoom() {
        let alertController = UIAlertController(title: title, message: NSLocalizedString("Specified_Room", comment:""), preferredStyle: UIAlertController.Style.alert)
        alertController.addTextField { (textField) -> Void in
            textField.keyboardType = UIKeyboardType.numberPad
            textField.placeholder = NSLocalizedString("Room_Number", comment:"")
        }
        alertController.addAction(UIAlertAction(title: NSLocalizedString("Yes", comment:""), style: UIAlertAction.Style.default, handler: { (action) -> Void in
            if let roomIDTextField = alertController.textFields?.first {
                if let roomID2Go = roomIDTextField.text {
                    self.go2ASpecifiedRoomPlay(roomID2Go)
                }
            }
        }))
        alertController.addAction(UIAlertAction(title:NSLocalizedString("Cancel", comment:""), style:UIAlertAction.Style.cancel, handler:nil))
        self.present(alertController, animated: true, completion: nil)
    }
    
    func go2ASpecifiedRoomPlay(_ roomID:String) {
        self.playOnInternet(DGInternetAction.go2ASpecifiedRoom(roomID:roomID))
    }
    
    fileprivate func playOnInternet(_ action:DGInternetAction) {
        if let client = DGInternetClient.create() {
            let gamevc = action.createViewController()
            self.present(gamevc, animated: false, completion: {
                action.fire(client)
            })
            gamevc.client = client
            client.delegate = gamevc
        } else {
            let alertController = UIAlertController(title: NSLocalizedString("Lost_Connection", comment:""), message: NSLocalizedString("Lost_Connection_Of_Server", comment:""), preferredStyle: UIAlertController.Style.alert)
            alertController.addAction(UIAlertAction(title:NSLocalizedString("Yes", comment:""), style:UIAlertAction.Style.cancel, handler:nil))
            self.present(alertController, animated: true, completion: nil)
        }
    }
    
    @objc func showRankOfPermission() {
        let leaderboard = GKGameCenterViewController()
        leaderboard.gameCenterDelegate = self
        self.justShowRankOfGameCenter = true
        self.present(leaderboard, animated: true, completion: nil)
        
        /*
        let defaults = NSUserDefaults.standardUserDefaults()
        let permissionPassed = defaults.boolForKey(DEFAULTS_PERMISSION_UPLOAD_YOUR_SCORE)
        if !permissionPassed {
        let alertController = UIAlertController(title: "许可证", message: "上传游戏成绩后才能查看排名", preferredStyle: UIAlertControllerStyle.Alert)
        alertController.addAction(UIAlertAction(title: "允许上传", style: UIAlertActionStyle.Default, handler: { (action) -> Void in
        defaults.setBool(true, forKey: DEFAULTS_PERMISSION_UPLOAD_YOUR_SCORE)
        self.justShowRank()
        }))
        alertController.addAction(UIAlertAction(title:"取消", style:UIAlertActionStyle.Cancel, handler:nil))
        self.presentViewController(alertController, animated: true, completion: nil)
        } else {
        self.justShowRank()
        }
        */
    }
    
    @objc func showSettings() {
        let nav = UINavigationController()
        self.present(nav, animated: true) {
            let settingsViewController = DGSettingsViewController()
            nav.pushViewController(settingsViewController, animated: true)
        }
    }
    
//    fileprivate func justShowRank() {
//        let rankViewController = DGRankViewController()
//        self.present(rankViewController, animated: true, completion: nil)
//    }
    
    fileprivate func switchStartupCenterView(_ enumView:DGStartupCenterView) {
        self.buttonView.isHidden = true
        self.belowButtonView.isHidden = true
        self.loginFailedView.isHidden = true
        self.loadingView.isHidden = true
        
        self.loadingIndicator.stopAnimating()
        
        switch enumView {
        case .buttonView:
            self.buttonView.isHidden = false
            self.belowButtonView.isHidden = false
            
            self.checkMyMission()
        case .loginFailedView:
            self.loginFailedView.isHidden = false
            
        case .loginView:
            self.loadingView.isHidden = false
            self.loadingInfoLabel.text = NSLocalizedString("Logining", comment:"")
            self.loadingIndicator.startAnimating()
        }
    }
    
//    @objc func updateClient() {
//        UIApplication.shared.open(URL(string: CURRENT_APP_DOWNLOAD_URL)!, options: [UIApplication.OpenExternalURLOptionsKey : Any]()) { (success) in
//            // do nothing
//        }
//    }
    
    @objc func retryLogin() {
        self.login()
    }
    
    @objc func zan() {
        let alertController = UIAlertController(title: NSLocalizedString("Encourage", comment:""), message: nil, preferredStyle: UIAlertController.Style.actionSheet)
        alertController.addAction(UIAlertAction(title:NSLocalizedString("Recommend_2_Wechat_Friend", comment:""), style:UIAlertAction.Style.default, handler:{(action) -> Void in
            self.recommend2WeixinFriend()
        }))
        /*
        Tencent
        alertController.addAction(UIAlertAction(title:"推荐给QQ好友", style:UIAlertActionStyle.Default, handler:{(action) -> Void in
        self.recommend2QQFriend()
        }))
        */
        alertController.addAction(UIAlertAction(title:NSLocalizedString("Support", comment:""), style:UIAlertAction.Style.default, handler:{(action) -> Void in
            self.reviewThisApp()
        }))
        alertController.addAction(UIAlertAction(title:NSLocalizedString("Cancel", comment:""), style:UIAlertAction.Style.cancel, handler:nil))
        
        self.present(alertController, animated: true, completion: nil)
    }
    
    fileprivate func recommend2WeixinFriend() {
        let req = SendMessageToWXReq()
        req.scene = Int32(WXSceneSession.rawValue) // WXSceneTimeline.value表示发到朋友圈
        
        req.bText = false
        req.message = WXMediaMessage()
        req.message.title = NSLocalizedString("I_Recommend_A_Dice_Game", comment:"")
        req.message.description = "\(NSLocalizedString("Download_Address", comment:"")):\(CURRENT_APP_DOWNLOAD_URL)"
        req.message.setThumbImage(UIImage(named:DGBundle.LOGO)!)
        
        let ext = WXWebpageObject()
        ext.webpageUrl = CURRENT_APP_DOWNLOAD_URL
        req.message.mediaObject = ext;
        
        WXApi.send(req)
    }
    
    fileprivate func openDiceGameApp() {
        let req = SendMessageToWXReq()
        req.scene = Int32(WXSceneSession.rawValue) // WXSceneTimeline.value表示发到朋友圈
        
        req.bText = false
        req.message = WXMediaMessage()
        req.message.title = NSLocalizedString("I_Recommend_A_Dice_Game", comment:"")
        req.message.description = "\(NSLocalizedString("Download_Address", comment:"")):\(CURRENT_APP_DOWNLOAD_URL)"
        req.message.setThumbImage(UIImage(named:DGBundle.LOGO)!)
        
        let ext = WXAppExtendObject()
        ext.extInfo = "HelloWorld"
        ext.url = CURRENT_APP_DOWNLOAD_URL // 若第三方程序不存在，微信终端会打开该url所指的App下载地址
        
        // fileData必须要有内容,才可以在微信里面直接打开app,至于这个fileData, extInfo, url在app打开的时候是否可以得到及使用,再研究研究吧
        var arrayOfUInt8 = Array<UInt8>()
        arrayOfUInt8.append(1)
        ext.fileData = Data(arrayOfUInt8)
        
        req.message.mediaObject = ext;
        
        WXApi.send(req)
    }
    
    /*
    func recommend2QQFriend() {
    if let newsObj = QQApiNewsObject.objectWithURL(NSURL(string: CURRENT_APP_DOWNLOAD_URL), title: "推荐休闲小游戏[酒吧骰子]", description: "下载地址:\(CURRENT_APP_DOWNLOAD_URL)", previewImageData:UIImageJPEGRepresentation(UIImage(named:DGBundle.LOGO)!, 1.0)) as? QQApiObject {
    
    let req = SendMessageToQQReq(content: newsObj)
    QQApiInterface.sendReq(req)
    }
    }
    */
    
    fileprivate func reviewThisApp() {
        UIApplication.shared.open(URL(string: REVIEW_APP_URL)!, options: [UIApplication.OpenExternalURLOptionsKey : Any]()) { (success) in
            // do nothing
        }
    }
    
    @objc func downloadLocalVersion() {
        UIApplication.shared.open(URL(string: LOCAL_APP_DOWNLOAD_URL)!, options: [UIApplication.OpenExternalURLOptionsKey : Any]()) { (success) in
            // do nothing
        }
    }
    
    @objc func showFeedback() {
        let feedbackViewController = DGFeedbackViewController()
        self.present(feedbackViewController, animated: true, completion: nil)
    }
    
    @objc func showMission() {
        var messages = [String]()
        for mission in self.currentMissions {
            if let descriptionOfMission = MISSION_DESCRIPTION(mission) {
                messages.append("\(NSLocalizedString("Mission", comment:"")) \(messages.count + 1):\(descriptionOfMission)")
            }
        }
        
        let message:String
        if messages.count > 0 {
            message = messages.joined(separator: "\n")
        } else {
            message = NSLocalizedString("All_Missions_Are_Completed", comment:"")
        }
        
        let alertController = UIAlertController(title: NSLocalizedString("Mission_With_Reward", comment:""), message: message, preferredStyle: UIAlertController.Style.alert)
        alertController.addAction(UIAlertAction(title: NSLocalizedString("Yes", comment:""), style: UIAlertAction.Style.default, handler: nil))
        self.present(alertController, animated: true, completion: nil)
    }
}

// MARK: - TencentSessionDelegate
extension DGStartupViewController {
    /*
    func loginByQQ() {
    // 这里需要填写注册APP时填写的域名。默认可以不用填写。建议不用填写。demo中注册时的地址是“www.qq.com”
    //        tencentOAuth.redirectURI = ""
    let permissions = [
    kOPEN_PERMISSION_GET_INFO,
    kOPEN_PERMISSION_GET_USER_INFO,
    kOPEN_PERMISSION_GET_SIMPLE_USER_INFO
    ]
    self.tencentOAuth.authorize(permissions, inSafari: false)
    }
    */
    
    /**
    * 登录成功后的回调
    */
    func tencentDidLogin() {
        //        if let accessToken = self.tencentOAuth.accessToken where count(accessToken) > 0 {
        //            saveTencentOAuth2Defaults(self.tencentOAuth)
        //
        //            self.tencentOAuth.getUserInfo()
        //
        //            self.switchStartupCenterView(DGStartupCenterView.RegistingUserView)
        //        }
    }
    
    /**
     * 登录失败后的回调
     * \param cancelled 代表用户是否主动退出登录
     */
    func tencentDidNotLogin(_ cancelled:Bool) {
        //        println("取消登录")
    }
    
    /**
     * 登录时网络有问题的回调
     */
    func tencentDidNotNetWork() {
        //        println("登录遇到网络问题")
    }
    
    /*
    func getUserInfoResponse(response: APIResponse!) {
    if let nickname = response.jsonResponse["nickname"] as? String {
    let gender = response.jsonResponse["gender"] as? String
    let figureurl40 = response.jsonResponse["figureurl_qq_1"] as? String
    let figureurl100 = response.jsonResponse["figureurl_qq_2"] as? String
    
    saveTencentNickname2DefaultsAndRegister2DB(nickname, gender, figureurl40, figureurl100)
    
    self.switchStartupCenterView(DGStartupCenterView.ButtonView)
    }
    }
    */
}

private enum DGInternetAction {
    case quickStart
    case quickStart4
    case ring
    case createAPrivteRoom
    case go2ASpecifiedRoom(roomID:String)
    
    fileprivate func createViewController() -> DGInternetGameViewController {
        switch self {
        case .ring:
            return DGRingGameViewController()
        case .createAPrivteRoom, .go2ASpecifiedRoom:
            return DGPrivateGameViewController()
        default:
            return DGRoundGameViewController()
        }
    }
    
    fileprivate func fire(_ client:DGInternetClient) {
        switch self {
        case  .quickStart:
            client.notifyServerOfQuickStart()
        case .quickStart4:
            client.notifyServerOfQuickStartOf4()
        case .ring:
            client.notifyServerOfRing()
        case .createAPrivteRoom:
            client.notifyServerOfCreateANewRoom()
        case let .go2ASpecifiedRoom(roomID):
            client.notifyServerOfGo2ASpecifiedRoom(roomID)
        }
    }
}

private enum DGStartupCenterView {
    case buttonView
    case loginView
    case loginFailedView
}
