//
//  RLDraw4TestView.swift
//  Land
//
//  Created by apple on 16/1/7.
//  Copyright © 2016年 G & B. All rights reserved.
//

import UIKit

class RLDraw4TestView : UIView {
    override func draw(_ rect: CGRect) {
        let font = UIFont.boldSystemFont(ofSize: 12)
        let str:NSString = "HelloWorld"
        var attr = [String:AnyObject]()
        attr[convertFromNSAttributedStringKey(NSAttributedString.Key.font)] = font
        str.draw(at: CGPoint(x: 0,y: 0), withAttributes:convertToOptionalNSAttributedStringKeyDictionary(attr))
    }
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
