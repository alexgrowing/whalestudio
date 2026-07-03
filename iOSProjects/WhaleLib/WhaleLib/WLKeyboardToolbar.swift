//
//  KeyboardToolbar.swift
//  Gym
//
//  Created by alex on 2017/11/14.
//  Copyright © 2017年 WhaleStudio. All rights reserved.
//

import UIKit

public class WLKeyboardToolbar : UIToolbar {
    public static let HEIGHT_OF_KEYBOARD_TOOLBAR:CGFloat = 40
    
    private var yesButton:UIBarButtonItem!
    private let delegate4KeyboardToolbar:WLKeyboardToolbarDelegate
    
    public init(delegate:WLKeyboardToolbarDelegate) {
        self.delegate4KeyboardToolbar = delegate
        
        super.init(frame: CGRect(x: 0, y: UIScreen.main.bounds.height, width: UIScreen.main.bounds.width, height: WLKeyboardToolbar.HEIGHT_OF_KEYBOARD_TOOLBAR))
        
        self.autoresizingMask = UIView.AutoresizingMask(rawValue: UIView.AutoresizingMask.RawValue(UInt8(UIView.AutoresizingMask.flexibleWidth.rawValue) | UInt8(UIView.AutoresizingMask.flexibleTopMargin.rawValue)))
        let spaceItem = UIBarButtonItem(barButtonSystemItem: UIBarButtonItem.SystemItem.flexibleSpace, target: nil, action: nil)
        self.yesButton = UIBarButtonItem(title: "确定", style: UIBarButtonItem.Style.plain, target: self, action: #selector(yesPressed))
        self.setItems([spaceItem, self.yesButton], animated: false)
    }
    
    public required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    public func moveTo(yPoint:CGFloat) {
        self.frame.origin.y = yPoint
    }
    
    public func hide() {
        self.frame.origin.y = UIScreen.main.bounds.height
    }
    
    func setYesButtonEnabled(enabled:Bool) {
        self.yesButton.isEnabled = enabled
    }
    
    @objc func yesPressed() {
        self.delegate4KeyboardToolbar.keyboardToolbarYesPressed(toolbar: self)
    }
}

public protocol WLKeyboardToolbarDelegate {
    func keyboardToolbarYesPressed(toolbar:WLKeyboardToolbar)
}
