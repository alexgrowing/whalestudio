//
//  DGPlayerView.swift
//  DiceGameLib
//
//  Created by apple on 16/3/17.
//  Copyright © 2016年 WhaleStudio. All rights reserved.
//

import UIKit

private let SIZE_OF_FIGURE_IMAGE:CGFloat = 25
private let HEIGHT_OF_NAME_LABEL:CGFloat = 10
private let WIDTH_OF_NAME_LABEL:CGFloat = 100
private let SIZE_OF_ACTION_IMAGE:CGFloat = 15
private let SIZE_OF_CROWN:CGFloat = 15
private let PADDING:CGFloat = 2

class DGPlayerView : UIView {
    static let PREFERRED_HEIGHT = DGUIUtils.SIZE_OF_DICE + PADDING * 2
    
    fileprivate let nickname:String
    fileprivate let figure:DGFigure
    
    fileprivate let countOfCrownLabel:UILabel
    fileprivate var countOfCrown:Int {
        get {
            if let labelText = self.countOfCrownLabel.text {
                if let labelNumber = Int(labelText) {
                    return labelNumber
                }
            }
            
            return 0
        }
        
        set {
            self.countOfCrownLabel.text = "\(newValue)"
        }
    }
    
    fileprivate let crownImageView:UIImageView
    fileprivate let figureImageView:UIImageView
    fileprivate let readyImageView:UIImageView
    
    fileprivate let countDownLabel:UILabel
    fileprivate var timer:Timer!
    fileprivate var countDownSecond:Int {
        get {
            if let labelText = self.countDownLabel.text {
                if let labelNumber = Int(labelText) {
                    return labelNumber
                }
            }
            
            return 0
        }
        
        set {
            self.countDownLabel.text = "\(newValue)"
        }
    }
    
    fileprivate let dices:DGFiveDices
    
    init(nickname:String, figure:DGFigure, countOfCrown:Int, below4ActionUIView:Bool) {
        self.nickname = nickname
        self.figure = figure
        
        let crownImage = UIImage(named: DGBundle.CROWN_IMAGE)!
        self.crownImageView = UIImageView(image: crownImage)
        self.countOfCrownLabel = DGUIUtils.createTinyUILabel(initString: "0")
        self.countOfCrownLabel.textAlignment = .left
        
        self.figureImageView = DGUIUtils.createRoundImageView(sizeOfImage: SIZE_OF_FIGURE_IMAGE, image: self.figure.asImage())
        self.countDownLabel = DGUIUtils.createTinyUILabel(initString: "")
        self.readyImageView = UIImageView(image: UIImage(named: DGBundle.READY_GO_IMAGE)!)
        self.readyImageView.isHidden = true
        
        self.dices = DGFiveDices()
        self.dices.isHidden = true
        
        super.init(frame:CGRect.zero)
        
        self.addSubview(self.dices)
        self.dices.snp.makeConstraints { (make) in
            make.right.equalTo(PADDING)
            make.centerY.equalTo(self)
            make.size.equalTo(DGFiveDices.size())
        }
        
        self.addSubview(self.figureImageView)
        self.figureImageView.snp.makeConstraints { (make) in
            make.left.equalTo(PADDING)
            make.centerY.equalTo(self)
            make.width.equalTo(SIZE_OF_FIGURE_IMAGE)
            make.height.equalTo(SIZE_OF_FIGURE_IMAGE)
        }
        
        let nameLabel = DGUIUtils.createTinyUILabel(initString: nickname)
        self.addSubview(nameLabel)
        nameLabel.textAlignment = .left
        nameLabel.snp.makeConstraints { (make) in
            make.left.equalTo(self.figureImageView.snp.right).offset(5)
            make.top.equalTo(PADDING)
            make.right.equalTo(self.dices.snp.left).offset(-5)
            make.height.equalTo(HEIGHT_OF_NAME_LABEL)
        }
        
        self.addSubview(self.countDownLabel)
        self.countDownLabel.snp.makeConstraints { (make) in
            make.left.top.equalTo(-5)
            make.width.height.equalTo(DGFonts.TINY_FONT_SIZE)
        }
        
        self.addSubview(self.readyImageView)
        self.readyImageView.snp.makeConstraints { (make) in
            make.left.top.equalTo(-5)
            make.width.height.equalTo(SIZE_OF_ACTION_IMAGE)
        }
        
        self.addSubview(self.crownImageView)
        self.crownImageView.snp.makeConstraints { (make) in
            make.left.equalTo(self.figureImageView.snp.right).offset(5)
            make.top.equalTo(nameLabel.snp.bottom)
            make.width.height.equalTo(SIZE_OF_CROWN)
        }
        
        self.addSubview(self.countOfCrownLabel)
        self.countOfCrownLabel.snp.makeConstraints { (make) in
            make.left.equalTo(self.crownImageView.snp.right).offset(5)
            make.centerY.equalTo(self.crownImageView)
            make.right.equalTo(self.dices.snp.left).offset(-5)
            make.height.equalTo(SIZE_OF_CROWN)
        }
        
        self.countOfCrown = countOfCrown
        
        self.backgroundColor = UIColor.white.withAlphaComponent(0.5)
        self.layer.cornerRadius = 5
    }
    
    required init(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    func showReady() {
        self.readyImageView.isHidden = false
    }
    
    func getFrameOfCrownTo(parentView:UIView) -> CGRect {
        return self.convert(self.crownImageView.frame, to: parentView)
    }
    
    func modifyCountOfCrown(_ modification:Int) {
        if modification == 0 {
            return
        }
        let frameOfCountOfCrownLabel = self.countOfCrownLabel.frame
        let modificationLabel = DGUIUtils.createTinyUILabel(initString: "\(modification)")
        modificationLabel.textAlignment = .left
        if modification > 0 {
            modificationLabel.textColor = UIColor.red
        } else {
            modificationLabel.textColor = UIColor.green
        }
        self.addSubview(modificationLabel)
        modificationLabel.snp.makeConstraints { (make) in
            make.left.equalTo(self.countOfCrownLabel)
            make.width.equalTo(self.countOfCrownLabel)
            make.top.equalTo(self.countOfCrownLabel.snp.top).offset(-20)
            make.height.equalTo(self.countOfCrownLabel)
        }
        
        UIView.animate(withDuration: 1, animations: {
            modificationLabel.frame.origin.y = frameOfCountOfCrownLabel.origin.y
        }) { (success) in
            modificationLabel.removeFromSuperview()
            self.countOfCrown = self.countOfCrown + modification
        }
    }
    
    func startCountDown() {
        self.countDownSecond = 15
        self.timer = Timer.scheduledTimer(timeInterval: 1, target: self, selector: #selector(DGPlayerView.updateCountDownLabel), userInfo: nil, repeats: true)
    }
    
    @objc func updateCountDownLabel() {
        if self.countDownSecond > 0 {
            self.countDownSecond = self.countDownSecond - 1
        }
    }
    
    func stopCountDown() {
        self.countDownLabel.text = ""
        if self.timer != nil && self.timer.isValid {
            self.timer.invalidate()
            self.timer = nil
        }
    }
    
    func setDices(_ numbers:[Int], animation:Bool) {
        self.dices.isHidden = false
        self.dices.setDices(numbers, animation: animation)
    }
    
    func getDiceViewsByIndices(_ indices:[Int]) -> [UIImageView] {
        return self.dices.getDiceViewsByIndices(indices)
    }
    
    func getCenterOfFiveDices() -> [CGPoint] {
        return self.dices.dices.map { (diceView) -> CGPoint in
            self.dices.convert(diceView.center, to: self)
        }
    }
}

private class DGFiveDices:UIView {
    fileprivate let dices = [
        UIImageView(image: DGUIUtils.getDiceImageOfQuestion()),
        UIImageView(image: DGUIUtils.getDiceImageOfQuestion()),
        UIImageView(image: DGUIUtils.getDiceImageOfQuestion()),
        UIImageView(image: DGUIUtils.getDiceImageOfQuestion()),
        UIImageView(image: DGUIUtils.getDiceImageOfQuestion())
    ]
    
    fileprivate static func size() -> CGSize {
        return CGSize(width: DGUIUtils.SIZE_OF_DICE * 5 + DGUIUtils.PADDING_BETWEEN_DICES * 4, height: DGUIUtils.SIZE_OF_DICE)
    }
    
    fileprivate func setDices(_ numbers:[Int], animation:Bool) {
        var index = 0
        self.dices.forEach { (view) in
            let targetIndex = index
            
            if animation {
                DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(NSEC_PER_SEC / 2 * UInt64(targetIndex + 1))) / Double(NSEC_PER_SEC)) { () -> Void in
                    self.dices[targetIndex].image = DGUIUtils.getFixedDiceImage(number: numbers[targetIndex])
                    self.dices[targetIndex].hideAndPopup()
                }
            } else {
                self.dices[targetIndex].image = DGUIUtils.getFixedDiceImage(number: numbers[targetIndex])
            }
            
            index = index + 1
        }
    }
    
    fileprivate init() {
        let size = DGFiveDices.size()
        
        self.dices.forEach { (view) in
            view.layer.borderWidth = 2
            view.layer.cornerRadius = 4
            view.layer.masksToBounds = true
            view.layer.borderColor = UIColor.clear.cgColor
        }
        
        super.init(frame:CGRect(x: 0,y: 0,width: size.width,height: size.height))
        
        var lastView:UIView?
        self.dices.forEach { (view) in
            self.addSubview(view)
            
            view.snp.makeConstraints({ (make) in
                make.size.equalTo(CGSize(width: DGUIUtils.SIZE_OF_DICE, height: DGUIUtils.SIZE_OF_DICE))
                make.top.equalTo(0)
                if lastView == nil {
                    make.left.equalTo(0)
                } else {
                    make.left.equalTo(lastView!.snp.right).offset(DGUIUtils.PADDING_BETWEEN_DICES)
                }
            })
            
            lastView = view
        }
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    fileprivate func getDiceViewsByIndices(_ indices:[Int]) -> [UIImageView] {
        return indices.map({ (index) -> UIImageView in
            return self.dices[index]
        })
    }
    
    /*
    fileprivate func spread() {
        UIView.animate(withDuration: 2, animations: {
            var index = 0
            self.dices.forEach({ (view) in
                view.center = CGPoint(x: SIZE_OF_DICE*CGFloat(index+1)+DGFiveDices.PADDING_BETWEEN_DICES*CGFloat(index)-SIZE_OF_DICE/2, y: SIZE_OF_DICE/2)
                
                index = index + 1
            })
        })
    }
 */
}
