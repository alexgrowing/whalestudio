//
//  DGUIUtils.swift
//  DiceGameLib
//
//  Created by apple on 15/7/8.
//  Copyright (c) 2015年 WhaleStudio. All rights reserved.
//

import UIKit
import GameKit
import SnapKit

public class DGUIUtils {
    public static let HEIGHT_OF_STATUS_BAR:CGFloat = 16
    public static let HEIGHT_OF_NAVIGATION_BAR:CGFloat = 40
    public static let MARGIN_OF_VIEW:CGFloat = 16
    public static let HEIGHT_OF_AD:CGFloat = 50
    
    public static let SIZE_OF_DICE:CGFloat = 30
    public static let PADDING_BETWEEN_DICES:CGFloat = 5
    
    public static func addMainBackgroundImageViewTo(parentView:UIView) {
        let backgroundImageView = UIImageView(image: UIImage(named: DGBundle.MAIN_BACKGROUND))
        parentView.addSubview(backgroundImageView)
        
        backgroundImageView.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.top.equalTo(0)
            make.bottom.equalTo(0)
        }
    }
    
    public static func createHomeButton(name:String, target:AnyObject?, action:Selector) -> UIButton {
        let button = DGUIUtils.createBackgroundImageButton(imagePath:DGBundle.HOME_BUTTON_BACKGROUND, target: target, action: action)
        
        button.titleLabel?.font = DGFonts.HOME_BUTTON_FONT
        button.setTitleColor(DGColors.HOME_BUTTON_TEXT_COLOR, for: UIControl.State())
        button.setTitle(name, for: UIControl.State())
        
        return button
    }
    
    public static func createForegroundImageButton(imagePath:String, target:AnyObject?, action:Selector) -> UIButton {
        let button = UIButton()
        
        button.setImage(UIImage(named: imagePath), for: .normal)
        button.addTarget(target, action: action, for: UIControl.Event.touchUpInside)
        return button
    }
    
    static func createBackgroundImageButton(imagePath:String, target:AnyObject?, action:Selector) -> UIButton {
        let button = UIButton()
        
        button.setBackgroundImage(UIImage(named: imagePath), for: .normal)
        button.addTarget(target, action: action, for: UIControl.Event.touchUpInside)
        return button
    }
    
    public static func calculatePreferredWidth(_ titleOfButton:String, fontOfButton:UIFont) -> CGFloat {
        let attribute = [NSAttributedString.Key.font: fontOfButton]
        let preferredSize = NSString(string: titleOfButton).boundingRect(with: CGSize(width: CGFloat(MAXFLOAT), height: fontOfButton.pointSize), options: NSStringDrawingOptions.usesLineFragmentOrigin, attributes:attribute , context: nil).size
        
        return preferredSize.width
    }
    
    public static func calculatePreferredHeight(_ title:String, font:UIFont, fixedWidth:CGFloat) -> CGFloat {
        let attribute = [NSAttributedString.Key.font: font]
        let preferredSize = NSString(string: title).boundingRect(with: CGSize(width: fixedWidth, height: CGFloat(MAXFLOAT)), options: NSStringDrawingOptions.usesLineFragmentOrigin, attributes:attribute , context: nil).size
        
        return preferredSize.height
    }
    
    public static func createUIButton(titleOfButton:String, target:AnyObject?, action:Selector) -> UIButton {
        let button = UIButton()
        button.titleLabel?.font = DGFonts.NORMAL_BUTTON_FONT
        button.setTitle(titleOfButton, for: UIControl.State())
        button.addTarget(target, action: action, for: UIControl.Event.touchUpInside)
        
        return button
    }
    
    public static func createMiddleUIButton(titleOfButton:String, target:AnyObject?, action:Selector) -> UIButton {
        let button = UIButton()
        button.titleLabel?.font = DGFonts.MIDDLE_FONT
        button.setTitle(titleOfButton, for: UIControl.State())
        button.addTarget(target, action: action, for: UIControl.Event.touchUpInside)
        
        return button
    }
    
    public static func createImageView(imagePath:String) -> UIImageView {
        let image = UIImage(named: imagePath)
        let imageView = UIImageView(image: image)
        
        return imageView
    }
    
    public static func createRoundImageView(sizeOfImage:CGFloat, image:UIImage) -> UIImageView {
        let view = UIImageView(image: image)
        view.layer.cornerRadius = sizeOfImage/2
        view.clipsToBounds = true
        
        return view
    }
    
    public static func addTransparentBackgroundViewTo(parentView:UIView) -> UIView {
        let view = UIView()
        view.backgroundColor = UIColor.clear
        
        parentView.addSubview(view)
        view.snp.makeConstraints { (make) in
            make.edges.equalTo(parentView)
        }
        
        return view
    }
    
    public static func createUILabel(initString:String) -> UILabel {
        return DGUIUtils.createFontSizeFixedUILabel(initString: initString, size: DGFonts.NORMAL_FONT_SIZE)
    }
    
    public static func createTinyUILabel(initString:String) -> UILabel {
        return DGUIUtils.createFontSizeFixedUILabel(initString: initString, size: DGFonts.TINY_FONT_SIZE)
    }
    
    public static func createMiddleUILabel(initString:String) -> UILabel {
        return DGUIUtils.createFontSizeFixedUILabel(initString: initString, size: DGFonts.MIDDLE_FONT_SIZE)
    }
    
    public static func createLargeUILabel(initString:String) -> UILabel {
        return DGUIUtils.createFontSizeFixedUILabel(initString: initString, size: DGFonts.LARGE_FONT_SIZE)
    }
    
    fileprivate static let sandbox = DGSandbox()
    
    static public func log2Sandbox(_ message:String) {
        if let data = "\(message)\n".data(using: String.Encoding.utf8, allowLossyConversion: true) {
            sandbox.log(data)
        }
    }
    
    static public func myDevicePlayerName() -> String {
        let gkPlayer = GKLocalPlayer.local
        
        if gkPlayer.isAuthenticated {
            return gkPlayer.alias
        } else {
            return UIDevice.current.name
        }
    }
    
    fileprivate static func createFontSizeFixedUILabel(initString:String, size:CGFloat) -> UILabel {
        let label = UILabel()
        label.font = UIFont.boldSystemFont(ofSize: size)
        label.textAlignment = NSTextAlignment.center
        label.textColor = DGColors.LABEL_COLOR
        label.backgroundColor = UIColor.clear
        label.text = initString
        label.adjustsFontSizeToFitWidth = true
        
        return label
    }
    
    public static func getDiceImageOfQuestion() -> UIImage {
        return DICE_IMAGES[0]
    }
    
    public static func getFixedDiceImage(number:Int) -> UIImage {
        return DICE_IMAGES[number]
    }
    
    public static func getFlexiableDiceImage() -> UIImage {
        return DICE_IMAGES[7]
    }
}

private let DICE_IMAGES = [
    UIImage(named: DGBundle.getDiceImage(0))!,
    UIImage(named: DGBundle.getDiceImage(1))!,
    UIImage(named: DGBundle.getDiceImage(2))!,
    UIImage(named: DGBundle.getDiceImage(3))!,
    UIImage(named: DGBundle.getDiceImage(4))!,
    UIImage(named: DGBundle.getDiceImage(5))!,
    UIImage(named: DGBundle.getDiceImage(6))!,
    UIImage(named: DGBundle.FLEXIBLE_ONE_IMAGE)!
]

extension UIView {
    
    // MARK: - UIView Class Methods
    //    static func moveViews(subViews:[UIView], parentView:UIView) {
    //        for view in subViews {
    //            parentView.addSubview(view)
    //        }
    //    }
    
    /*
    * 当xPoint属于[0, 1]时,表示百分比
    */
    static public func arrangeViewsVertically(_ views:[UIView], bounds:CGRect, xPoint:CGFloat) {
        let heightOfBounds = bounds.size.height
        let widthOfBounds = bounds.size.width
        let countOfViews = views.count
        
        for i in 0 ..< countOfViews {
            let xPosition:CGFloat
            if xPoint <= 1.0 {
                xPosition = xPoint * widthOfBounds + bounds.origin.x
            } else {
                xPosition = xPoint + bounds.origin.x
            }
            
            views[i].center = CGPoint(x: xPosition, y: heightOfBounds/CGFloat(countOfViews + 1) * CGFloat(i + 1) + bounds.origin.y)
        }
    }
    
    /*
    * 当yPoint属于[0, 1]时,表示百分比
    */
    static public func arrangeViewHorizontally(_ views:[UIView], bounds:CGRect, yPoint:CGFloat) {
        let heightOfBounds = bounds.size.height
        let widthOfBounds = bounds.size.width
        let countOfViews = views.count
        
        for i in 0 ..< countOfViews {
            let yPosition:CGFloat
            if yPoint <= 1.0 {
                yPosition = yPoint * heightOfBounds + bounds.origin.y
            } else {
                yPosition = yPoint + bounds.origin.y
            }
            
            let point = CGPoint(x: widthOfBounds/CGFloat(countOfViews + 1) * CGFloat(i + 1) + bounds.origin.x, y: yPosition)
            
            views[i].center = point
        }
    }
    
    public static func iterateBigAndSmall(_ views:[UIView],
                                          callbackOnEach2Start:@escaping (_ view:UIView, _ indexOfView:Int) -> Void,
                                          callbackOnEachFinished:@escaping (_ view:UIView, _ indexOfView:Int) -> Void,
                                          callbackOnAllFinished:@escaping () -> Void) {
        UIView.iterateBigAndSmallByIndex(views, currentIndex: 0, callbackOnCurrentIndex2Start:callbackOnEach2Start, callbackOnCurrentIndexFinished: callbackOnEachFinished, callbackOnIndexOutOfRange: callbackOnAllFinished)
    }
    
    fileprivate static func iterateBigAndSmallByIndex(_ views:[UIView], currentIndex:Int,
                                                  callbackOnCurrentIndex2Start:@escaping (_ view:UIView, _ indexOfView:Int) -> Void,
                                                  callbackOnCurrentIndexFinished:@escaping (_ view:UIView, _ indexOfView:Int) -> Void,
                                                  callbackOnIndexOutOfRange:@escaping () -> Void) {
        if currentIndex < views.count && currentIndex >= 0 {
            callbackOnCurrentIndex2Start(views[currentIndex], currentIndex)
            
            views[currentIndex].bigAndSmall({ () -> Void in
                callbackOnCurrentIndexFinished(views[currentIndex], currentIndex)
                
                UIView.iterateBigAndSmallByIndex(views, currentIndex: currentIndex + 1, callbackOnCurrentIndex2Start:callbackOnCurrentIndex2Start, callbackOnCurrentIndexFinished: callbackOnCurrentIndexFinished, callbackOnIndexOutOfRange: callbackOnIndexOutOfRange)
            })
        } else {
            callbackOnIndexOutOfRange()
        }
    }
    
    // MARK: - UIView Instance Methods
    public func hideAndPopup() {
        let oldTransform = self.transform
        
        self.transform = oldTransform.scaledBy(x: 0.01, y: 0.01)
        UIView.animate(withDuration: 0.3, animations: { 
            self.transform = oldTransform.scaledBy(x: 1.1, y: 1.1)
            }, completion: { (finished) in
                UIView.animate(withDuration: 0.1, animations: { 
                    self.transform = oldTransform.scaledBy(x: 0.9, y: 0.9)
                    }, completion: { (finished) in
                        UIView.animate(withDuration: 0.1, animations: {
                            self.transform = oldTransform.scaledBy(x: 1.05, y: 1.05)
                            }, completion: { (finished) in
                                UIView.animate(withDuration: 0.1, animations: {
                                    self.transform = oldTransform.scaledBy(x: 0.95, y: 0.95)
                                    }, completion: { (finished) in
                                        UIView.animate(withDuration: 0.1, animations: { 
                                            self.transform = oldTransform.scaledBy(x: 1, y: 1)
                                    })
                                })
                        })
                })
        }) 
    }
    
    public func hideAndPopupLarge() {
        self.transform = CGAffineTransform(scaleX: 0.01, y: 0.01)
        UIView.animate(withDuration: 0.3, animations: {
            self.transform = CGAffineTransform(scaleX: 3, y: 3)
        }, completion: { (finished) in
            UIView.animate(withDuration: 0.1, animations: {
                self.transform = CGAffineTransform(scaleX: 0.8, y: 0.8)
                }, completion: { (finished) in
                    UIView.animate(withDuration: 0.1, animations: {
                        self.transform = CGAffineTransform(scaleX: 2, y: 2)
                        }, completion: { (finished) in
                            UIView.animate(withDuration: 0.1, animations: {
                                self.transform = CGAffineTransform(scaleX: 0.9, y: 0.9)
                                }, completion: { (finished) in
                                    UIView.animate(withDuration: 0.1, animations: {
                                        self.transform = CGAffineTransform(scaleX: 1.5, y: 1.5)
                                        }, completion: { (finished) in
                                            UIView.animate(withDuration: 0.1, animations: {
                                                self.transform = CGAffineTransform(scaleX: 0.95, y: 0.95)
                                                }, completion: { (finished) in
                                                    UIView.animate(withDuration: 0.1, animations: {
                                                        self.transform = CGAffineTransform(scaleX: 1, y: 1)
                                                    })
                                            })
                                    })
                            })
                    })
            })
        }) 
    }
    
    public func bigAndSmall(_ callback:@escaping () -> Void) {
        UIView.animate(withDuration: 0.3, animations: { () -> Void in
            self.transform = CGAffineTransform(scaleX: 1.5,y: 1.5)
            }, completion: { (_) -> Void in
                UIView.animate(withDuration: 0.1, animations: { () -> Void in
                    self.transform = CGAffineTransform(scaleX: 0.9,y: 0.9)
                    }, completion: { (_) -> Void in
                        UIView.animate(withDuration: 0.1, animations: { () -> Void in
                            self.transform = CGAffineTransform(scaleX: 1.05,y: 1.05)
                            }, completion: { (_) -> Void in
                                UIView.animate(withDuration: 0.1, animations: { () -> Void in
                                    self.transform = CGAffineTransform(scaleX: 0.95,y: 0.95)
                                    }, completion: { (_) -> Void in
                                        UIView.animate(withDuration: 0.1, animations: { () -> Void in
                                            self.transform = CGAffineTransform(scaleX: 1,y: 1)
                                            }, completion: { (_) -> Void in
                                                callback()
                                        })
                                })
                        })
                })
        }) 
    }
}

private class DGSandbox {
    fileprivate let logFile4Write:FileHandle
    fileprivate let logFile4Read:FileHandle
    
    init() {
        let home = NSHomeDirectory() as NSString
        let docPath = home.appendingPathComponent("Documents") as NSString
        let logPath = docPath.appendingPathComponent("performance.log")
        
        let fileManager = FileManager.default
        if !fileManager.fileExists(atPath: logPath) {
            fileManager.createFile(atPath: logPath, contents: nil, attributes: nil)
        }
        
        self.logFile4Write = FileHandle(forWritingAtPath: logPath)!
        self.logFile4Read = FileHandle(forReadingAtPath: logPath)!
    }
    
    fileprivate func log(_ data:Data) {
        self.logFile4Write.seekToEndOfFile()
        self.logFile4Write.write(data)
        self.logFile4Write.synchronizeFile()
    }
}

