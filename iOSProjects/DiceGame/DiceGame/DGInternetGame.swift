//
//  DGInternetGameViewController.swift
//  DiceGame
//
//  Created by Alex Chen on 15/6/1.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import UIKit
import GameKit
import DiceGameLib
import GoogleMobileAds

private let ALL_WINS = "boast_times_participate"
private let ATTACK_WINS = "boast_times_wins"
private let DEFEND_WINS = "boast_winning_steak"
private let COUNT_OF_CROWN = "boast_count_of_crown"

class DGInternetGameViewController : DGGameViewController, DGInternetClientDelegate, GADBannerViewDelegate {
    override func topOfSafeArea() -> CGFloat {
        return self.view.safeAreaInsets.top + DGUIUtils.HEIGHT_OF_AD
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
            make.top.equalTo(self.view.safeAreaInsets.top)
            make.centerX.equalTo(self.view)
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
    
    override func viewDidDisappear(_ animated: Bool) {
        self.client.releaseResources()
        
        self.client = nil // alex:即使client设置了nil了,client的longpolling还是不会停,必须要在longpolling处停止才可以
        super.viewDidDisappear(animated)
    }
    
    override func beNotifiedOfRoundResult(_ result: [DGPlayerDicesTossedAndRoundResult]) {
        super.beNotifiedOfRoundResult(result)
        
        if GKLocalPlayer.local.isAuthenticated {
            for resultOfOnePlayer in result {
                if self.myUUID() == resultOfOnePlayer.playerUUID {
                    let allWinsScore = GKScore(leaderboardIdentifier: ALL_WINS)
                    let allAttackWinsScore = GKScore(leaderboardIdentifier: ATTACK_WINS)
                    let maxDefendWinsScore = GKScore(leaderboardIdentifier: DEFEND_WINS)
                    let countOfCrownScore = GKScore(leaderboardIdentifier: COUNT_OF_CROWN)
                    
                    allWinsScore.value = Int64(resultOfOnePlayer.timesOfAllWins)
                    allAttackWinsScore.value = Int64(resultOfOnePlayer.timesOfAllAttackWins)
                    maxDefendWinsScore.value = Int64(resultOfOnePlayer.maxTimesOfAllDefendWins)
                    countOfCrownScore.value = Int64(resultOfOnePlayer.currentCountOfCrowns)
                    
                    GKScore.report([allWinsScore, allAttackWinsScore, maxDefendWinsScore, countOfCrownScore], withCompletionHandler: nil)
                }
            }
        }
    }
    
    // MARK: - DGInternetClientDelegate
    func errorOnClientConnecting2Server(_ error: NSError, retryHandler:((() -> Void) -> Void)) {
        retryHandler({() -> Void in
            // 当执行retryHandler发现无法连接上服务器时,会执行下面的方法
            let alertController = UIAlertController(title: NSLocalizedString("Lost_Connection", comment:""), message: NSLocalizedString("Lost_Connection_Of_Server", comment:""), preferredStyle: UIAlertController.Style.alert)
            
            
            alertController.addAction(UIAlertAction(title:NSLocalizedString("Quit", comment:""), style:UIAlertAction.Style.cancel, handler:{ (action) -> Void in
                self.dismiss(animated: true, completion: nil)
            }))
            
            self.present(alertController, animated: true, completion: nil)
        })
    }
    
    // MARK: - GADBannerViewDelegate
    func adViewWillLeaveApplication(_ adView: GADBannerView) {
        DGClientActions.notifyServerIHaveClickedAd()
    }
}

