////
////  DGFigureScoreView.swift
////  DiceGameLib
////
////  Created by apple on 15/7/15.
////  Copyright (c) 2015年 WhaleStudio. All rights reserved.
////
//
//import UIKit
//
//class DGDeprecatedFigureScoreView:UIView {
//    static let PREFERRED_HEIGHT:CGFloat = DGDeprecatedFigureScoreView.HEIGHT_OF_FIGURE_IMAGE + DGDeprecatedFigureScoreView.HEIGHT_OF_NAME_LABEL + VERTICAL_PADDING
//    static let PREFERRED_WIDTH:CGFloat = DGDeprecatedFigureScoreView.WIDTH_OF_NAME_LABEL + DGDeprecatedFigureScoreView.HORIZONTAL_PADDING + DGScoreCardView.WIDTH_OF_EACH_CARD
//    
//    static let HEIGHT_OF_FIGURE_IMAGE:CGFloat = 20
//    static let HEIGHT_OF_NAME_LABEL:CGFloat = 15
//    static let SIZE_OF_CROWN:CGFloat = 15
//    fileprivate static let WIDTH_OF_NAME_LABEL:CGFloat = 60
//    fileprivate static let HEIGHT_OF_CARD:CGFloat = DGScoreCardView.HEIGHT_OF_VIEW
//    fileprivate static let VERTICAL_PADDING:CGFloat = 2
//    fileprivate static let HORIZONTAL_PADDING:CGFloat = 2
//    
//    fileprivate let nickname:String
//    fileprivate let figure:DGFigure
//    
//    var score:Int {
//        get {
//            return self.scoreCardView.score
//        }
//        
//        set {
//            self.scoreCardView.score = newValue
//        }
//    }
//    fileprivate let crownImageView:UIImageView
//    fileprivate let figureImageView:UIImageView
//    fileprivate let scoreCardView:DGScoreCardView
//    fileprivate let countDownLabel:UILabel
//    fileprivate var countDownSecond:Int {
//        get {
//            if let labelText = self.countDownLabel.text {
//                if let labelNumber = Int(labelText) {
//                    return labelNumber
//                }
//            }
//            
//            return 0
//        }
//        
//        set {
//            self.countDownLabel.text = "\(newValue)"
//        }
//    }
//    fileprivate var timer:Timer!
//    
//    init(origin:CGPoint, nickname:String, figure:DGFigure) {
//        self.nickname = nickname
//        self.figure = figure
//        
//        let widthOfView = DGDeprecatedFigureScoreView.PREFERRED_WIDTH
//        let heightOfView = DGDeprecatedFigureScoreView.PREFERRED_HEIGHT
//        
//        let crownImage = UIImage(named: DGBundle.CROWN_IMAGE)!
//        self.crownImageView = UIImageView(image: crownImage)
//        crownImageView.frame = CGRect(x: (DGDeprecatedFigureScoreView.PREFERRED_WIDTH-DGDeprecatedFigureScoreView.SIZE_OF_CROWN)/2,y: -DGDeprecatedFigureScoreView.SIZE_OF_CROWN/2,width: DGDeprecatedFigureScoreView.SIZE_OF_CROWN,height: DGDeprecatedFigureScoreView.SIZE_OF_CROWN)
//        self.crownImageView.isHidden = true
//        
//        self.figureImageView = DGUIUtils.createRoundImageView(CGPoint(x: (DGDeprecatedFigureScoreView.PREFERRED_WIDTH-DGDeprecatedFigureScoreView.HEIGHT_OF_FIGURE_IMAGE)/2, y: 0), sizeOfImage: DGDeprecatedFigureScoreView.HEIGHT_OF_FIGURE_IMAGE, image: self.figure.asImage())
//        self.scoreCardView = DGScoreCardView(frame:CGRect(x: 0,y: heightOfView-DGDeprecatedFigureScoreView.HEIGHT_OF_CARD,width: widthOfView,height: DGDeprecatedFigureScoreView.HEIGHT_OF_CARD))
//        self.countDownLabel = DGUIUtils.createTinyUILabel(CGRect(x: widthOfView-DGFonts.TINY_FONT_SIZE, y: 0, width: DGFonts.TINY_FONT_SIZE, height: DGFonts.TINY_FONT_SIZE), initString: "")
//        
//        super.init(frame: CGRect(x: origin.x, y: origin.y, width: widthOfView, height: heightOfView))
//        
//        self.addSubview(DGUIUtils.createTinyUILabel(CGRect(x: 0, y: DGDeprecatedFigureScoreView.HEIGHT_OF_FIGURE_IMAGE+DGDeprecatedFigureScoreView.VERTICAL_PADDING, width: widthOfView, height: DGDeprecatedFigureScoreView.HEIGHT_OF_NAME_LABEL), initString: nickname))
//        
//        self.addSubview(self.figureImageView)
//        self.addSubview(self.scoreCardView)
//        self.addSubview(self.countDownLabel)
//        self.addSubview(self.crownImageView)
//    }
//
//    required init(coder aDecoder: NSCoder) {
//        fatalError("init(coder:) has not been implemented")
//    }
//    
//    func showAction() {
//        self.figureImageView.bigAndSmall { () -> Void in
//            // do nothing
//        }
//    }
//    
//    func modifyCountOfCrown() {
//        self.crownImageView.isHidden = false
//        self.crownImageView.hideAndPopup()
//    }
//    
//    func putoffCrown() {
//        self.crownImageView.isHidden = true
//    }
//    
//    func startCountDown() {
//        self.countDownSecond = 15
//        self.timer = Timer.scheduledTimer(timeInterval: 1, target: self, selector: #selector(DGDeprecatedFigureScoreView.updateCountDownLabel), userInfo: nil, repeats: true)
//    }
//    
//    @objc func updateCountDownLabel() {
//        if self.countDownSecond > 0 {
//            self.countDownSecond = self.countDownSecond - 1
//        }
//    }
//    
//    func stopCountDown() {
//        self.countDownLabel.text = ""
//        if self.timer != nil && self.timer.isValid {
//            self.timer.invalidate()
//            self.timer = nil
//        }
//    }
//}
