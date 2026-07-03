//
//  WLUI.swift
//  WhaleLib
//
//  Created by alex on 2017/5/12.
//  Copyright © 2017年 WhaleStudio. All rights reserved.
//

import Foundation

public class WLUI {
    public static func resize(sourceImage:UIImage, sizeOfLongSide:CGFloat) -> UIImage {
        let sizeOfSourceImage = sourceImage.size
        let sizeOfLongSideOfSourceImage = max(sizeOfSourceImage.width, sizeOfSourceImage.height)
        let scale = sizeOfLongSideOfSourceImage / sizeOfLongSide
        
        let sizeRes = CGSize(width: sizeOfSourceImage.width / scale / UIScreen.main.scale, height: sizeOfSourceImage.height / scale / UIScreen.main.scale)
        
        UIGraphicsBeginImageContextWithOptions(sizeRes, false, 0)
        sourceImage.draw(in: CGRect(x: 0, y: 0, width: sizeRes.width, height: sizeRes.height))
        let imageRes = UIGraphicsGetImageFromCurrentImageContext()
        
        UIGraphicsEndImageContext()
        
        return imageRes!
    }
    
    static func maskImage(_ originalImage:UIImage, path:UIBezierPath) -> UIImage {
        UIGraphicsBeginImageContextWithOptions(originalImage.size, false, 0);
        path.addClip()
        originalImage.draw(at: CGPoint.zero)
        let maskedImage = UIGraphicsGetImageFromCurrentImageContext()
        UIGraphicsEndImageContext()
        return maskedImage!
    }
    
    public static func clipImage(_ image:UIImage, rect:CGRect) -> UIImage? {
        let cgImageCorpped = image.cgImage?.cropping(to: rect)
        return UIImage(cgImage: cgImageCorpped!, scale: image.scale, orientation: image.imageOrientation)
    }
    
    public static func drawTextAsImage(text:String, size:CGSize, fontSize:CGFloat) -> UIImage {
        UIGraphicsBeginImageContext(size)
        
        let attrs = [
            NSAttributedString.Key.font:UIFont.systemFont(ofSize: fontSize)
        ]
        NSString(string: text).draw(in: CGRect(origin: CGPoint.zero, size: size), withAttributes: attrs)
        let newImage = UIGraphicsGetImageFromCurrentImageContext()
        UIGraphicsEndImageContext()
        
        return newImage!
    }
    
    public static func drawColorAsImage(color:UIColor) -> UIImage {
        let imageRect = CGRect(x: 0, y: 0, width: 1, height: 1)
        UIGraphicsBeginImageContext(imageRect.size)
        let context = UIGraphicsGetCurrentContext()
        context?.setFillColor(color.cgColor)
        context?.fill(imageRect)
        let image = UIGraphicsGetImageFromCurrentImageContext()
        UIGraphicsEndImageContext()
        
        return image!
    }
    
    public static func alert(title:String?, message:String?) -> UIAlertController {
        let alertVC = UIAlertController(title: title, message: message, preferredStyle: .alert)
        alertVC.addAction(UIAlertAction(title: "确定", style: .default, handler: { (action) in
            // do nothing
        }))
        
        return alertVC
    }
    
    public static func alertAsk(title:String?, message:String?, handler:@escaping ()->Void) -> UIAlertController {
        let alertVC = UIAlertController(title: title, message: message, preferredStyle: .alert)
        alertVC.addAction(UIAlertAction(title: "确定", style: .default, handler: { (action) in
            handler()
        }))
        alertVC.addAction(UIAlertAction(title: "取消", style: .cancel, handler: { (action) in
            // do nothing
        }))
        
        return alertVC
    }
    
    public static func createUILabel(text:String) -> UILabel {
        return WLUI.createFontSizeFixedUILabel(text: text, size: NORMAL_FONT_SIZE)
    }
    
    public static func createUIButton(titleOfButton:String, target:AnyObject?, action:Selector) -> UIButton {
        let button = UIButton()
        button.titleLabel?.font = NORMAL_BUTTON_FONT
        button.setTitle(titleOfButton, for: .normal)
        button.addTarget(target, action: action, for: UIControl.Event.touchUpInside)
        
        return button
    }
    
    public static func createUIButton(image:UIImage, margin:CGFloat, target:AnyObject?, action:Selector) -> UIButton {
        let button = UIButton()
        button.setImage(image, for: .normal)
        button.imageEdgeInsets = UIEdgeInsets(top: margin, left: margin, bottom: margin, right: margin)
        button.addTarget(target, action: action, for: UIControl.Event.touchUpInside)
        
        return button
    }
    
    fileprivate static func createFontSizeFixedUILabel(text:String, size:CGFloat) -> UILabel {
        let label = UILabel()
        label.font = UIFont.boldSystemFont(ofSize: size)
        label.textAlignment = NSTextAlignment.center
        label.textColor = LABEL_COLOR
        label.backgroundColor = UIColor.clear
        label.text = text
        label.adjustsFontSizeToFitWidth = true
        
        return label
    }
}

private let LABEL_COLOR = UIColor.white

private let NORMAL_FONT_SIZE:CGFloat = 18
private let NORMAL_BUTTON_FONT = UIFont.systemFont(ofSize: NORMAL_FONT_SIZE)


private weak var currentFirstResponder: AnyObject?

extension UIResponder {
    
    public static func firstResponder() -> AnyObject? {
        currentFirstResponder = nil
        // 通过将target设置为nil，让系统自动遍历响应链
        // 从而响应链当前第一响应者响应我们自定义的方法
        UIApplication.shared.sendAction(#selector(findFirstResponder(_:)), to: nil, from: nil, for: nil)
        return currentFirstResponder
    }
    
    @objc public static func resignFirstResponder() {
        UIApplication.shared.sendAction(#selector(resignFirstResponder), to: nil, from: nil, for: nil)
    }
    
    @objc func findFirstResponder(_ sender: AnyObject) {
        // 第一响应者会响应这个方法，并且将静态变量currentFirstResponder设置为自己
        currentFirstResponder = self
    }
}

extension UIApplication {
    static func topViewController() -> UIViewController? {
        guard var top = shared.keyWindow?.rootViewController else {
            return nil
        }
        while let next = top.presentedViewController {
            top = next
        }
        return top
    }
}
