//
//  DGFlickLabel.swift
//  DiceGameLib
//
//  Created by Alex Chen on 15/5/30.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import UIKit

open class DGFlickLabel : UILabel {
    init() {
        super.init(frame: CGRect.zero)
        
        self.textAlignment = NSTextAlignment.center
        self.textColor = DGColors.LABEL_COLOR
    }

    required public init(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    fileprivate var flick = FlickTag.stop {
        didSet {
            switch self.flick {
            case .repeat:
                self.fadeInOrFadeOut()
            case .stop:
                break
            }
        }
    }
    
    open func startFlick() {
        self.flick = FlickTag.repeat
    }
    
    open func stopFlick() {
        self.flick = FlickTag.stop
        self.alpha = 0
    }
    
    fileprivate func fadeInOrFadeOut() {
        UIView.animate(withDuration: 1, animations: {
            () -> Void in
            if self.alpha == 1 {
                self.alpha = 0.3
            } else {
                self.alpha = 1
            }
            }, completion: {
                (finished) -> Void in
                if self.flick == FlickTag.repeat {
                    self.fadeInOrFadeOut()
                }
        })
    }
    
    fileprivate enum FlickTag {
        case `repeat`, stop
    }
}
