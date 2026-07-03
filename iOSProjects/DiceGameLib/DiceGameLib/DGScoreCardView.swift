//
//  DGVSScoreCardView.swift
//  DiceGame
//
//  Created by Alex Chen on 15/5/5.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import UIKit
import WhaleLib

/*
public class DGVSScoreCardView : UIView {
    static let HEIGHT_OF_VIEW:CGFloat = 70 / 2
    private static let WIDTH_OF_EACH_CARD:CGFloat = 51 / 2
    
    public var firstName:String? {
        didSet {
            self.firstNameLabel.text = firstName
        }
    }
    public var secondName:String? {
        didSet {
            self.secondNameLabel.text = secondName
        }
    }
    
    private let firstNameLabel:UILabel
    private let secondNameLabel:UILabel
    
    public var firstHistoryScores:(Int, Int, Int) = (0, 0, 0) {
        didSet {
            self.firstHistoryScoresLabel.text = "胜:\(self.firstHistoryScores.0) 负:\(self.firstHistoryScores.1) 连胜:\(self.firstHistoryScores.2)"
        }
    }
    public var secondHistoryScores:(Int, Int, Int) = (0, 0, 0) {
        didSet {
            self.secondHistoryScoresLabel.text = "胜:\(self.secondHistoryScores.0) 负:\(self.secondHistoryScores.1) 连胜:\(self.secondHistoryScores.2)"
        }
    }
    private let firstHistoryScoresLabel:UILabel
    private let secondHistoryScoresLabel:UILabel
    
    var firstScore = 0 {
        didSet {
            self.resetCardViews()
        }
    }
    private var firstScoreCardView:DGScoreCardView
    
    var secondScore = 0 {
        didSet {
            self.resetCardViews()
        }
    }
    private var secondScoreCardView:DGScoreCardView
    
    public override init(frame:CGRect) {
        self.firstNameLabel = DGVSScoreCardView.createNameLabelWithTextAlignment(NSTextAlignment.Right)
        self.firstHistoryScoresLabel = DGVSScoreCardView.createHistoryScoresLabelWithTextAlignment(NSTextAlignment.Right)
        self.firstScoreCardView = DGScoreCardView()
        self.secondScoreCardView = DGScoreCardView()
        self.secondNameLabel = DGVSScoreCardView.createNameLabelWithTextAlignment(NSTextAlignment.Left)
        self.secondHistoryScoresLabel = DGVSScoreCardView.createHistoryScoresLabelWithTextAlignment(NSTextAlignment.Left)
        
        super.init(frame:frame)
        
        self.addSubview(self.firstNameLabel)
        self.addSubview(self.firstHistoryScoresLabel)
        self.addSubview(self.firstScoreCardView)
        self.addSubview(self.secondScoreCardView)
        self.addSubview(self.secondNameLabel)
        self.addSubview(self.secondHistoryScoresLabel)
    }

    required public init(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    private func resetCardViews() {
        let lengthOfFirstScore = self.firstScore == 0 ? 1 : Int(log10(Float(self.firstScore))) + 1
        let lengthOfSecondScore = self.secondScore == 0 ? 1 : Int(log10(Float(self.secondScore))) + 1
        
        let countOfCards4Score = max(lengthOfFirstScore, lengthOfSecondScore)
        var needsRelayoutSubviews = false
        while (self.firstCardViews.count < countOfCards4Score) {
            let newCardView = DGScoreOneCardView.createOneCardScoreView()
            self.firstCardViews.insert(newCardView, atIndex: 0)
            self.addSubview(newCardView)
            needsRelayoutSubviews = true
        }
        while (self.secondCardViews.count < countOfCards4Score) {
            let newCardView = DGScoreOneCardView.createOneCardScoreView()
            self.secondCardViews.insert(newCardView, atIndex: 0)
            self.addSubview(newCardView)
            needsRelayoutSubviews = true
        }
        
        if needsRelayoutSubviews {
            self.layoutSubviews()
        }
        
        var firstScoreLeft = Float(self.firstScore)
        var secondScoreLeft = Float(self.secondScore)
        
        for cardIndex in 0 ..< countOfCards4Score {
            let bridge = pow(Float(10), Float(countOfCards4Score - cardIndex - 1))
            self.firstCardViews[cardIndex].scoreBetween0And9 = Int(firstScoreLeft / bridge)
            firstScoreLeft = Float(Int(firstScoreLeft % bridge))
            self.secondCardViews[cardIndex].scoreBetween0And9 = Int(secondScoreLeft / bridge)
            secondScoreLeft = Float(Int(secondScoreLeft % bridge))
        }
    }
    
    
    override public func layoutSubviews() {
        let mainFrameWidth = self.bounds.size.width
        let widthOfCardViewsAndSpacing = DGVSScoreCardView.WIDTH_OF_EACH_CARD * CGFloat(1 + self.firstCardViews.count + self.secondCardViews.count)
        let widthOfNameLabel = (mainFrameWidth - widthOfCardViewsAndSpacing) / 2
        
        self.firstNameLabel.frame = CGRectMake(0, 0, (self.bounds.size.width - widthOfCardViewsAndSpacing) / 2 - 4, DGVSScoreCardView.HEIGHT_OF_VIEW / 2)
        self.firstNameLabel.center = CGPointMake(widthOfNameLabel / 2, DGVSScoreCardView.HEIGHT_OF_VIEW / 4)
        
        self.firstHistoryScoresLabel.frame = CGRectMake(0, 0, (self.bounds.size.width - widthOfCardViewsAndSpacing) / 2 - 4, DGVSScoreCardView.HEIGHT_OF_VIEW / 2)
        self.firstHistoryScoresLabel.center = CGPointMake(widthOfNameLabel / 2, DGVSScoreCardView.HEIGHT_OF_VIEW / 4 * 3)
        
        for viewIndex in 0 ..< self.firstCardViews.count {
            self.firstCardViews[viewIndex].center = CGPointMake(widthOfNameLabel + DGVSScoreCardView.WIDTH_OF_EACH_CARD / 2 * CGFloat(1+2*viewIndex), DGVSScoreCardView.HEIGHT_OF_VIEW / 2)
        }
        for viewIndex in 0 ..< self.secondCardViews.count {
            self.secondCardViews[viewIndex].center = CGPointMake(widthOfNameLabel + DGVSScoreCardView.WIDTH_OF_EACH_CARD / 2 * CGFloat(1+2*viewIndex + 2*self.firstCardViews.count + 2), DGVSScoreCardView.HEIGHT_OF_VIEW / 2)
        }
        self.secondNameLabel.frame = CGRectMake(0, 0, (self.bounds.size.width - widthOfCardViewsAndSpacing) / 2 - 4, DGVSScoreCardView.HEIGHT_OF_VIEW / 2)
        self.secondNameLabel.center = CGPointMake(mainFrameWidth - widthOfNameLabel / 2, DGVSScoreCardView.HEIGHT_OF_VIEW / 4)
        
        self.secondHistoryScoresLabel.frame = CGRectMake(0, 0, (self.bounds.size.width - widthOfCardViewsAndSpacing) / 2 - 4, DGVSScoreCardView.HEIGHT_OF_VIEW / 2)
        self.secondHistoryScoresLabel.center = CGPointMake(mainFrameWidth - widthOfNameLabel / 2, DGVSScoreCardView.HEIGHT_OF_VIEW / 4 * 3)
    }
    
    private static func createNameLabelWithTextAlignment(align:NSTextAlignment) -> UILabel {
        let label = UILabel(frame:CGRectMake(0, 0, 0, 0))
        label.textAlignment = align
        label.backgroundColor = UIColor.clearColor()
//        label.textColor = UIColor(red: CGFloat(9)/255, green: CGFloat(10)/255, blue: CGFloat(30)/255, alpha: 1)
        label.textColor = DGColors.LABEL_COLOR
        label.font = UIFont.systemFontOfSize(10)
        
        return label
    }
    
    private static func createHistoryScoresLabelWithTextAlignment(align:NSTextAlignment) -> UILabel {
        let label = UILabel(frame:CGRectMake(0, 0, 0, 0))
        label.textAlignment = align
        label.backgroundColor = UIColor.clearColor()
        //        label.textColor = UIColor(red: CGFloat(9)/255, green: CGFloat(10)/255, blue: CGFloat(30)/255, alpha: 1)
        label.textColor = DGColors.LABEL_COLOR
        label.font = UIFont(name:"Courier", size:6)
        
        return label
    }
}
*/

open class DGScoreCardView:UIView {
    static let HEIGHT_OF_VIEW:CGFloat = 70/3
    static let WIDTH_OF_EACH_CARD:CGFloat = 51/3
    
    var score = 0 {
        didSet {
            self.resetCardViews()
        }
    }
    fileprivate var cardViews:[DGScoreOneCardView]
    
    override init(frame:CGRect) {
        self.cardViews = [DGScoreOneCardView.createOneCardScoreView()]
        
        super.init(frame:frame)
        
        for card in self.cardViews {
            self.addSubview(card)
        }
    }

    required public init(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    override open func layoutSubviews() {
        let centerXOfView = self.bounds.width/2
        let centerYOfView = self.bounds.height/2
        let widthOfAllCards = DGScoreCardView.WIDTH_OF_EACH_CARD*CGFloat(self.cardViews.count)
        let centerXOf1stCard = centerXOfView-widthOfAllCards/2+DGScoreCardView.WIDTH_OF_EACH_CARD/2
        
        for index in 0 ..< self.cardViews.count {
            self.cardViews[index].center = CGPoint(x: centerXOf1stCard+CGFloat(index)*DGScoreCardView.WIDTH_OF_EACH_CARD, y: centerYOfView)
        }
    }
    
    fileprivate func resetCardViews() {
        let lengthOfScore = self.score == 0 ? 1 : Int(log10(Float(self.score))) + 1
        
        var needsRelayoutSubviews = false
        while (self.cardViews.count < lengthOfScore) {
            let newCardView = DGScoreOneCardView.createOneCardScoreView()
            self.cardViews.insert(newCardView, at: 0)
            self.addSubview(newCardView)
            needsRelayoutSubviews = true
        }
        
        if needsRelayoutSubviews {
            self.layoutSubviews()
        }
        
        var scoreLeft = Float(self.score)
        
        for cardIndex in 0 ..< lengthOfScore {
            let bridge = pow(Float(10), Float(lengthOfScore - cardIndex - 1))
            self.cardViews[cardIndex].scoreBetween0And9 = Int(scoreLeft / bridge)
            scoreLeft = Float(Int(scoreLeft.truncatingRemainder(dividingBy: bridge)))
        }
    }
}

private class DGScoreOneCardView : UIView {
    fileprivate var scoreBetween0And9:Int = 0 {
        didSet {
            if oldValue == self.scoreBetween0And9 {
                return
            }
            
            let sourceImage = UIImage(named:DGBundle.SCORE_CARD_NUMBERS_IMAGE)!
            let newUpImageView = UIImageView(image: WLUI.clipImage(sourceImage, rect: CGRect(
                x: CGFloat(51 * self.scoreBetween0And9), y: 0, width: 51, height: 35
            )))
            let newBelowImageView = UIImageView(image: WLUI.clipImage(sourceImage, rect: CGRect(
                x: CGFloat(51 * self.scoreBetween0And9), y: 35, width: 51, height: 35
            )))
            
            let originalUpBounds = self.upImageView.bounds
            let originalUpCenter = self.upImageView.center
            let originalBelowBounds = self.belowImageView.bounds
            let originalBelowCenter = self.belowImageView.center
            
            self.addSubview(newUpImageView)
            self.sendSubviewToBack(newUpImageView)
            newUpImageView.bounds = self.upImageView.bounds
            newUpImageView.center = self.upImageView.center
            
            self.addSubview(newBelowImageView)
            self.bringSubviewToFront(newBelowImageView)
            newBelowImageView.bounds = CGRect(x: originalBelowBounds.origin.x, y: originalBelowBounds.origin.y, width: originalBelowBounds.size.width, height: 0)
            newBelowImageView.center = CGPoint(x: originalBelowCenter.x, y: originalBelowCenter.y - originalBelowBounds.size.height / 2)
            
            UIView.animate(withDuration: 1.2, animations: { () -> Void in
                self.upImageView.bounds = CGRect(x: originalUpBounds.origin.x, y: originalUpBounds.origin.y, width: originalUpBounds.size.width, height: 0)
                self.upImageView.center = CGPoint(x: originalUpCenter.x, y: originalUpCenter.y + originalUpBounds.size.height / 2)
            }, completion: { (finished) -> Void in
                UIView.animate(withDuration: 0.6, animations: { () -> Void in
                    newBelowImageView.bounds = originalBelowBounds
                    newBelowImageView.center = originalBelowCenter
                }, completion: { (finished) -> Void in
                    self.upImageView.removeFromSuperview()
                    self.belowImageView.removeFromSuperview()
                    
                    self.upImageView = newUpImageView
                    self.belowImageView = newBelowImageView
                })
            }) 
        }
    }
    
    fileprivate var upImageView:UIImageView!
    fileprivate var belowImageView:UIImageView!
    
    override init(frame:CGRect) {
        super.init(frame: frame)
        self.setup()
    }

    required init(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    fileprivate func setup() {
        self.scoreBetween0And9 = 0
        let sourceImage = UIImage(named: DGBundle.SCORE_CARD_NUMBERS_IMAGE)!
        
        let newUpImageView = UIImageView(image: WLUI.clipImage(sourceImage, rect: CGRect(
            x: CGFloat(51 * self.scoreBetween0And9), y: 0, width: 51, height: 35
        )))
        let newBelowImageView = UIImageView(image: WLUI.clipImage(sourceImage, rect: CGRect(
            x: CGFloat(51 * self.scoreBetween0And9), y: 35, width: 51, height: 35
        )))
        
        newUpImageView.center = CGPoint(x: self.bounds.size.width / 2, y: self.bounds.size.height / 4)
        newBelowImageView.center = CGPoint(x: self.bounds.size.width / 2, y: self.bounds.size.height / 4 * 3)
        
        newUpImageView.bounds = CGRect(x: 0, y: 0, width: self.bounds.size.width, height: self.bounds.size.height / 2)
        newBelowImageView.bounds = CGRect(x: 0, y: 0, width: self.bounds.size.width, height: self.bounds.size.height / 2)
        
        self.addSubview(newUpImageView)
        self.addSubview(newBelowImageView)
        
        self.upImageView = newUpImageView
        self.belowImageView = newBelowImageView
    }
    
    fileprivate static func createOneCardScoreView() -> DGScoreOneCardView {
        return DGScoreOneCardView(frame:CGRect(x: 0, y: 0, width: DGScoreCardView.WIDTH_OF_EACH_CARD, height: DGScoreCardView.HEIGHT_OF_VIEW))
    }
}
