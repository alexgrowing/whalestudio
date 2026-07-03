//
//  DGBundle.swift
//  DiceGameLib
//
//  Created by apple on 15/7/8.
//  Copyright (c) 2015年 WhaleStudio. All rights reserved.
//

import Foundation

open class DGBundle {
    fileprivate static let bundle = Bundle(path: Bundle.main.path(forResource: "DGLib", ofType: "bundle")!)!
    
    fileprivate static let BUNDLE_PREFIX = "DGLib.bundle"
    
    public static let LOGO = "\(DGBundle.BUNDLE_PREFIX)/logo.png"
    
    public static let MAIN_BACKGROUND = "\(DGBundle.BUNDLE_PREFIX)/background_1920_1080.jpg"


    
    static let TRANSFORMABLE_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/transform.png"
    static let MINUS_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/minus.png"
    static let PLUS_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/plus.png"
    static let HOME_BUTTON_BACKGROUND = "\(DGBundle.BUNDLE_PREFIX)/button.jpg"
    static let DICE_CUP_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/box.png"
    static let POINTER_IAMGE = "\(DGBundle.BUNDLE_PREFIX)/pointer_280_280.png"
    static func getDiceImage(_ number:Int) -> String {
        return "\(DGBundle.BUNDLE_PREFIX)/\(number)_85_85.png"
    }
    static let FLEXIBLE_ONE_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/1_flexible_85_85.png"
    static let FIXED_ONE_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/1_fixed_85_85.png"
    
    static let BACKGROUND_IMAGE_OF_SELECTED_DICE = "\(DGBundle.BUNDLE_PREFIX)/concave_85_85.png"
    
    static let INCREASE_COUNT_OF_GUESS_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/up.png"
    static let DECREASE_COUNT_OF_GUESS_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/down.png"
    
    static let GREEN_BUTTON_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/green_button_512.png"
    static let RED_BUTTON_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/red_button_512.png"
    
    static let SCORE_CARD_NUMBERS_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/numbers.png"
    
    static let DEFAULT_FIGURE_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/defaultfigure.png"
    
    static let GOLD_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/gold.png"
    static let CROWN_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/crown.png"
    
    static let READY_GO_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/go_32_32.png"
//    static let LAUGH_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/laugh_128_128.png"
//    static let CRY_IMAGE = "\(DGBundle.BUNDLE_PREFIX)/cry_128_128.png"
    
    static func i18n(key:String) -> String {
        return NSLocalizedString(key, bundle: DGBundle.bundle, value: key, comment: key)
    }

}
