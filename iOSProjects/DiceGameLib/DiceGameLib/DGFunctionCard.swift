//
//  DGFunctionCard.swift
//  DiceGameLib
//
//  Created by apple on 15/8/7.
//  Copyright (c) 2015年 WhaleStudio. All rights reserved.
//

import UIKit

open class DGFunctionCard : UIView {
    fileprivate let cardName:String
    fileprivate let functionDescription:String
    
    init(cardName:String, functionDescription:String) {
        self.cardName = cardName
        self.functionDescription = functionDescription
        
        super.init(frame:CGRect.zero)
        
        let sizeOfFrame = self.bounds.size
        
        self.backgroundColor = UIColor.lightGray
        self.layer.cornerRadius = min(sizeOfFrame.width, sizeOfFrame.height) / 10
        
        let marginOfFrame:CGFloat = 5
        let cardNameLabel = DGUIUtils.createMiddleUILabel(initString: self.cardName)
        self.addSubview(cardNameLabel)
        cardNameLabel.snp.makeConstraints { (make) in
            make.top.equalTo(marginOfFrame)
            make.left.equalTo(marginOfFrame)
            make.right.equalTo(-marginOfFrame)
            make.bottom.equalTo(self.snp.centerY)
        }
        
        let lineLabel = DGUIUtils.createTinyUILabel(initString: "")
        lineLabel.backgroundColor = UIColor.white
        self.addSubview(lineLabel)
        lineLabel.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.centerY.equalTo(self)
            make.right.equalTo(0)
            make.height.equalTo(1)
        }
        
        let descriptionLabel = DGUIUtils.createUILabel(initString: self.functionDescription)
        self.addSubview(descriptionLabel)
        descriptionLabel.snp.makeConstraints { (make) in
            make.left.equalTo(marginOfFrame)
            make.right.equalTo(-marginOfFrame)
            make.top.equalTo(self.snp.centerY)
            make.bottom.equalTo(-marginOfFrame)
        }
    }

    required public init(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
}
