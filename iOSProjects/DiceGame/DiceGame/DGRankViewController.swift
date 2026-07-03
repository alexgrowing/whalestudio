////
////  DGMyInformationViewController.swift
////  DiceGame
////
////  Created by Alex Chen on 15/6/28.
////  Copyright (c) 2015年 WhaleStudio. All rights reserved.
////
//
//import UIKit
//import DiceGameLib
//
//
//class DGRankViewController : UIViewController, UIScrollViewDelegate {
//    fileprivate var myNickNameButton: UIButton!
////    private var myFigure: UIImageView!
//    fileprivate var mainScrollView: UIScrollView!
//    fileprivate var pageIndicatorControl: UIPageControl!
//    
//    fileprivate var winRankView:DGRankView!
//    fileprivate var attackRankView:DGRankView!
//    fileprivate var defendRankView:DGRankView!
//    
//    fileprivate var myRank:(win:Int, attack:Int, defend:Int)?
//    fileprivate var myScore:(win:Int, attack:Int, defend:Int)?
//    
//    func back() {
//        self.dismiss(animated: true, completion: nil)
//    }
//    
//    override func viewDidLoad() {
//        self.view.backgroundColor = UIColor.lightGray
//        
//        let sizeOfFrame = self.view.frame.size
//        
//        let titleOfBackButton = "返回"
//        let preferredWidthOfBackButton = DGUIUtils.calculatePreferredWidth(titleOfBackButton, fontOfButton: DGFonts.NORMAL_BUTTON_FONT)
//        self.view.addSubview(DGUIUtils.createUIButton(CGRect(x: DGUIUtils.MARGIN_OF_VIEW, y: DGUIUtils.HEIGHT_OF_STATUS_BAR, width: preferredWidthOfBackButton, height: DGUIUtils.HEIGHT_OF_NAVIGATION_BAR), titleOfButton: titleOfBackButton, target: self, action: #selector(DGRankViewController.back)))
//        
//        var preferredWidthOfNicknameButton:CGFloat = 0
//        if let theUser = DGUser.getCurrentUser() {
//            preferredWidthOfNicknameButton = DGUIUtils.calculatePreferredWidth(theUser.name, fontOfButton: DGFonts.NORMAL_BUTTON_FONT)
//            
//            self.myNickNameButton = DGUIUtils.createUIButton(CGRect(x: sizeOfFrame.width-DGUIUtils.MARGIN_OF_VIEW-preferredWidthOfNicknameButton, y: DGUIUtils.HEIGHT_OF_STATUS_BAR, width: preferredWidthOfNicknameButton, height: DGUIUtils.HEIGHT_OF_NAVIGATION_BAR), titleOfButton: theUser.name, target: self, action: Selector())
//            self.view.addSubview(self.myNickNameButton)
//        }
//        
//        /*
//        if let figure40 = getSavedPhoto4Game() {
//            let image = DGFigure(isURL: true, path: figure40).asImage()
//            let sizeOfMyFigure = DGUIUtils.HEIGHT_OF_NAVIGATION_BAR
//            
//            self.view.addSubview(DGUIUtils.createRoundImageView(CGPointMake(sizeOfFrame.width-DGUIUtils.MARGIN_OF_VIEW-sizeOfMyFigure-preferredWidthOfNicknameButton, DGUIUtils.HEIGHT_OF_STATUS_BAR), sizeOfImage: sizeOfMyFigure, image: image))
//        }
//*/
//        
//        let paddingOfShareButton:CGFloat = 10
//        let sizeOfShareButton:CGFloat = 20
//        self.view.addSubview(DGUIUtils.createForegroundImageButton(CGRect(x: DGUIUtils.MARGIN_OF_VIEW, y: sizeOfFrame.height-sizeOfShareButton-paddingOfShareButton,width: sizeOfShareButton,height: sizeOfShareButton), imagePath: "share.png", target: self, action: #selector(DGRankViewController.share)))
//        let showOffTextButton = DGUIUtils.createUIButton(CGRect(x: DGUIUtils.MARGIN_OF_VIEW+sizeOfShareButton+paddingOfShareButton, y: sizeOfFrame.height-sizeOfShareButton-paddingOfShareButton*2,width: sizeOfFrame.width-DGUIUtils.MARGIN_OF_VIEW*2-sizeOfShareButton-paddingOfShareButton,height: sizeOfShareButton+paddingOfShareButton*2), titleOfButton: "炫耀一下", target: self, action: #selector(DGRankViewController.share))
//        showOffTextButton.contentHorizontalAlignment = UIControlContentHorizontalAlignment.left
//        self.view.addSubview(showOffTextButton)
//        
//        self.mainScrollView = UIScrollView(frame:CGRect(x: 0, y: DGUIUtils.HEIGHT_OF_STATUS_BAR+DGUIUtils.HEIGHT_OF_NAVIGATION_BAR, width: sizeOfFrame.width, height: sizeOfFrame.height-DGUIUtils.HEIGHT_OF_STATUS_BAR-DGUIUtils.HEIGHT_OF_NAVIGATION_BAR-sizeOfShareButton-paddingOfShareButton*2))
//        self.view.addSubview(self.mainScrollView)
//        self.mainScrollView.isPagingEnabled = true
//        self.mainScrollView.bounces = true
//        
//        let sizeOfPageIndicatorControl:CGFloat = 40
//        self.pageIndicatorControl = UIPageControl(frame:CGRect(x: sizeOfFrame.width/2-sizeOfPageIndicatorControl/2, y: DGUIUtils.HEIGHT_OF_NAVIGATION_BAR+DGUIUtils.HEIGHT_OF_STATUS_BAR, width: sizeOfPageIndicatorControl, height: sizeOfPageIndicatorControl))
//        self.view.addSubview(self.pageIndicatorControl)
//        self.pageIndicatorControl.numberOfPages = 3
//        
//        super.viewDidLoad()
//        
//        self.mainScrollView.delegate = self
//        self.pageIndicatorControl.isEnabled = false
//    }
//    
//    override func viewDidAppear(_ animated:Bool) {
//        super.viewDidAppear(animated)
//        
//        let sizeOfScrollView = self.mainScrollView.bounds.size
//        
//        self.winRankView = DGRankView(frame:CGRect(x: 0, y: 0, width: sizeOfScrollView.width, height: sizeOfScrollView.height), columnName2Display4Score:"胜利回合数", action2GetScoreFromDictionary:{(dict:[String:AnyObject]) -> Int in
//            return dict[DGRankView.SCORE_COLUMN_NAME_WINS] as! Int
//        })
//        self.mainScrollView.addSubview(winRankView)
//        self.winRankView.center = CGPoint(x: sizeOfScrollView.width / 2, y: sizeOfScrollView.height / 2)
//        
//        self.attackRankView = DGRankView(frame:CGRect(x: 0, y: 0, width: sizeOfScrollView.width, height: sizeOfScrollView.height), columnName2Display4Score:"夺擂次数", action2GetScoreFromDictionary:{(dict:[String:AnyObject]) -> Int in
//            return dict[DGRankView.SCORE_COLUMN_NAME_ATTACKS] as! Int
//        })
//        self.mainScrollView.addSubview(attackRankView)
//        self.attackRankView.center = CGPoint(x: sizeOfScrollView.width / 2 * 3, y: sizeOfScrollView.height / 2)
//
//        self.defendRankView = DGRankView(frame:CGRect(x: 0, y: 0, width: sizeOfScrollView.width, height: sizeOfScrollView.height), columnName2Display4Score:"最长守擂次数", action2GetScoreFromDictionary:{(dict:[String:AnyObject]) -> Int in
//            return dict[DGRankView.SCORE_COLUMN_NAME_DEFENDS] as! Int
//        })
//        self.mainScrollView.addSubview(defendRankView)
//        self.defendRankView.center = CGPoint(x: sizeOfScrollView.width / 2 * 5, y: sizeOfScrollView.height / 2)
//        
//        self.mainScrollView.contentSize = CGSize(width: sizeOfScrollView.width * 3, height: sizeOfScrollView.height)
//        
//        DGClientActions.fetchRank { () -> Void in
//            /*
//            if let dict = (try? NSJSONSerialization.JSONObjectWithData(dataResponsed!, options: NSJSONReadingOptions.MutableContainers)) as? [String:AnyObject] {
//            let myWins = dict["myWins"] as! Int
//            let myAttacks = dict["myAttacks"] as! Int
//            let myDefends = dict["myDefends"] as! Int
//            
//            self.myScore = (win:myWins, attack:myAttacks, defend:myDefends)
//            self.myRank = (win:dict["myWinRank"] as! Int, attack:dict["myAttackRank"] as! Int, defend:dict["myDefendRank"] as! Int)
//            
//            let top10Winners = dict["top10Winners"] as! [[String:AnyObject]]
//            let top10Attackers = dict["top10Attackers"] as! [[String:AnyObject]]
//            let top10Defenders = dict["top10Defenders"] as! [[String:AnyObject]]
//            
//            dispatch_async(dispatch_get_main_queue(), {
//            
//            self.winRankView.setDataSource(top10Dictionary: top10Winners, myUUID: theUser.uuid, myPlayerName: theUser.name, myRank: self.myRank!.win, myScore: myWins)
//            
//            self.attackRankView.setDataSource(top10Dictionary: top10Attackers, myUUID: theUser.uuid, myPlayerName: theUser.name, myRank: self.myRank!.attack, myScore: myAttacks)
//            
//            self.defendRankView.setDataSource(top10Dictionary: top10Defenders, myUUID: theUser.uuid, myPlayerName: theUser.name, myRank: self.myRank!.defend, myScore: myDefends)
//            })
//            }
//            */
//        }
//    }
//    
//    func share() {
//        if self.myRank == nil || self.myScore == nil {
//            let alertController = UIAlertController(title: "网络连接失败", message: "无法取到您的成绩", preferredStyle: UIAlertControllerStyle.alert)
//            alertController.addAction(UIAlertAction(title:"确定", style:UIAlertActionStyle.cancel, handler:nil))
//            self.present(alertController, animated: true, completion: nil)
//        } else {
//            let alertController = UIAlertController(title: "炫耀一下", message: nil, preferredStyle: UIAlertControllerStyle.actionSheet)
//            
//            alertController.addAction(UIAlertAction(title:"分享到微信朋友圈", style:UIAlertActionStyle.default, handler:{(action) -> Void in
//                self.share2Weixin()
//            }))
//            /*
//            Tencent
//            alertController.addAction(UIAlertAction(title:"分享到QQ空间", style:UIAlertActionStyle.Default, handler:{(action) -> Void in
//                self.share2QQ()
//            }))
//*/
//            alertController.addAction(UIAlertAction(title:"取消", style:UIAlertActionStyle.cancel, handler:nil))
//            
//            self.present(alertController, animated: true, completion: nil)
//        }
//    }
//    
//    fileprivate func createShowOffSpeech() -> String {
//        return "我在[酒吧骰子]中胜\(self.myScore!.win)回合，排名第\(self.myRank!.win)，夺擂\(self.myScore!.attack)次，排名第\(self.myRank!.attack)，最长守擂\(self.myScore!.defend)次，排名第\(self.myRank!.defend)"
//    }
//    
//    fileprivate func share2Weixin() {
//        let req = SendMessageToWXReq()
//        req.scene = Int32(WXSceneTimeline.rawValue) // WXSceneSession.value表示发到朋友圈
//        
//        req.bText = false
//        req.message = WXMediaMessage()
//        req.message.title = self.createShowOffSpeech()
//        req.message.description = "下载地址:\(CURRENT_APP_DOWNLOAD_URL)"
//        req.message.setThumbImage(UIImage(named:DGBundle.LOGO)!)
//        
//        let ext = WXWebpageObject()
//        ext.webpageUrl = CURRENT_APP_DOWNLOAD_URL
//        req.message.mediaObject = ext;
//        
//        WXApi.send(req)
//    }
//    
//    /*
//    private func share2QQ() {
//        if let newsObj = QQApiNewsObject.objectWithURL(NSURL(string: CURRENT_APP_DOWNLOAD_URL), title: "炫耀一下", description: self.createShowOffSpeech(), previewImageData:UIImageJPEGRepresentation(UIImage(named:DGBundle.LOGO)!, 1.0)) as? QQApiObject {
//            
//            let req = SendMessageToQQReq(content:newsObj)
//            QQApiInterface.SendReqToQZone(req)
//        }
//    }
//*/
//    
//    // MARK: - UIScrollViewDelegate
//    func scrollViewDidEndDecelerating(_ scrollView: UIScrollView) {
//        self.pageIndicatorControl.currentPage = Int(scrollView.contentOffset.x / self.mainScrollView.bounds.size.width)
//    }
//}
