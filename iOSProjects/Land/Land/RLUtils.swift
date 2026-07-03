//
//  RLUtils.swift
//  Land
//
//  Created by apple on 15/12/31.
//  Copyright © 2015年 G & B. All rights reserved.
//

import Foundation
import WhaleLib

func drawDiamondPrice(_ price:Int, size:CGSize) -> UIImage {
    UIGraphicsBeginImageContextWithOptions(size, true, 0)
    let ctx = UIGraphicsGetCurrentContext()
    ctx?.setFillColor(red: 1, green: 1, blue: 1, alpha: 1)
    ctx?.fill(CGRect(origin: CGPoint.zero, size: size))
    
    ctx?.setStrokeColor(red: 0,green: 0,blue: 0,alpha: 1)
    let font = UIFont.systemFont(ofSize: 20)
    let text = NSString(string: "\(price)")
    let textAttributes = [convertFromNSAttributedStringKey(NSAttributedString.Key.font):font]
    let sizeOfText = text.size(withAttributes: convertToOptionalNSAttributedStringKeyDictionary(textAttributes))
    let yPoint = (size.height - sizeOfText.height)/2
    let paddingBetweenTextAndImage:CGFloat = 2
    text.draw(at: CGPoint(x: size.width / 2 - sizeOfText.width - paddingBetweenTextAndImage/2, y: yPoint), withAttributes: convertToOptionalNSAttributedStringKeyDictionary(textAttributes))
    
    UIImage(named: "diamond.png")?.draw(in: CGRect(x: size.width/2 + paddingBetweenTextAndImage/2, y: yPoint, width: sizeOfText.height, height: sizeOfText.height))
    
    let image = UIGraphicsGetImageFromCurrentImageContext()
    UIGraphicsEndImageContext()
    return image!
}

let FOOTPRINT_OF_SIZE_9_IMAGE = drawFootprint(9.0)

private func drawFootprint(_ fontSize:CGFloat) -> UIImage {
    let font = UIFont.boldSystemFont(ofSize: fontSize)
    let text = NSString(string: "👣")
    let textAttributes = [
        convertFromNSAttributedStringKey(NSAttributedString.Key.font):font,
        convertFromNSAttributedStringKey(NSAttributedString.Key.foregroundColor):UIColor(red: 219.0/255, green: 0, blue: 25.0/255, alpha: 1)
    ]
    let sizeOfText = text.size(withAttributes: convertToOptionalNSAttributedStringKeyDictionary(textAttributes))
    
    UIGraphicsBeginImageContextWithOptions(sizeOfText, false, 0)
    
    let ctx = UIGraphicsGetCurrentContext()
    ctx?.setFillColor(red: 1, green: 1, blue: 1, alpha: 0)
    ctx?.fill(CGRect(origin: CGPoint.zero, size: sizeOfText))
    
    text.draw(at: CGPoint.zero, withAttributes: convertToOptionalNSAttributedStringKeyDictionary(textAttributes))

    let image = UIGraphicsGetImageFromCurrentImageContext()
    UIGraphicsEndImageContext()
    return image!
}

func drawUserLocationImage() -> UIImage {
    UIGraphicsBeginImageContextWithOptions(CGSize(width: 10,height: 20), false, 0)
    
    let ctx = UIGraphicsGetCurrentContext()
    
    ctx?.setFillColor(red: 1, green: 0, blue: 1, alpha: 0)
    ctx?.fill(CGRect(origin: CGPoint.zero, size: CGSize(width: 10,height: 20)))
    
    ctx?.setFillColor(red: 0, green: 0, blue: 1, alpha: 0)
    ctx?.fill(CGRect(origin: CGPoint(x: 0,y: 10), size: CGSize(width: 10,height: 10)))
    
    let image = UIGraphicsGetImageFromCurrentImageContext()
    UIGraphicsEndImageContext()
    
    return image!
}

func drawMark(_ number:Int, sizeOfFont:CGFloat, sizeOfImage:CGSize) -> UIImage {
    UIGraphicsBeginImageContextWithOptions(sizeOfImage, true, 0)
    let ctx = UIGraphicsGetCurrentContext()
    ctx?.setFillColor(red: 1, green: 0, blue: 0, alpha: 1)
    ctx?.fill(CGRect(origin: CGPoint.zero, size: sizeOfImage))
    
    let font = UIFont.boldSystemFont(ofSize: sizeOfFont)
    let text = NSString(string: "\(number)")
    let textAttributes = [
        convertFromNSAttributedStringKey(NSAttributedString.Key.font):font,
        convertFromNSAttributedStringKey(NSAttributedString.Key.foregroundColor):UIColor.white
    ]
    let sizeOfText = text.size(withAttributes: convertToOptionalNSAttributedStringKeyDictionary(textAttributes))
    let yPoint = (sizeOfImage.height - sizeOfText.height)/2
    let xPoint = (sizeOfImage.width - sizeOfText.width)/2
    text.draw(at: CGPoint(x: xPoint, y: yPoint), withAttributes: convertToOptionalNSAttributedStringKeyDictionary(textAttributes))
    
    let image = UIGraphicsGetImageFromCurrentImageContext()
    UIGraphicsEndImageContext()
    return image!
}

func asTimeDescription(_ interval:TimeInterval) -> String {
    printLog("timeLeft:\(interval)")
    var description = ""
    var seconds = Int(interval)
    var minutes = 0
    var hours = 0
    var days = 0
    if seconds >= 60 {
        minutes = seconds / 60
        seconds = seconds % 60
    }
    if minutes >= 60 {
        hours = minutes / 60
        minutes = minutes % 60
    }
    if hours >= 24 {
        days = hours / 24
        hours = hours % 24
    }
    
    if seconds > 0 {
        description = "\(seconds)秒"
    }
    if minutes > 0 {
        description = "\(minutes)分\(description)"
    }
    if hours > 0 {
        description = "\(hours)时\(description)"
    }
    if days > 0 {
        description = "\(days)天\(description)"
    }
    printLog("result:\(description)")
    
    return description
}

// Helper function inserted by Swift 4.2 migrator.
fileprivate func convertFromNSAttributedStringKey(_ input: NSAttributedString.Key) -> String {
	return input.rawValue
}

// Helper function inserted by Swift 4.2 migrator.
fileprivate func convertToOptionalNSAttributedStringKeyDictionary(_ input: [String: Any]?) -> [NSAttributedString.Key: Any]? {
	guard let input = input else { return nil }
	return Dictionary(uniqueKeysWithValues: input.map { key, value in (NSAttributedString.Key(rawValue: key), value)})
}
