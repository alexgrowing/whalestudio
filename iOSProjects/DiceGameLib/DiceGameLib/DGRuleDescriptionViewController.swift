//
//  DGRuleDescriptionViewController.swift
//  DiceGame
//
//  Created by Alex Chen on 15/4/23.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import UIKit

open class DGRuleDescriptionViewController : UIViewController, UITextViewDelegate {
    private var descriptionTextView:UITextView!

    open override func viewDidLoad() {
        super.viewDidLoad()
                
        DGUIUtils.addMainBackgroundImageViewTo(parentView: self.view)
    }
    
    open override func viewDidAppear(_ animated: Bool) {
        let safeView = UIView()
        self.view.addSubview(safeView)
        safeView.snp.makeConstraints { (make) in
            make.edges.equalTo(self.view.safeAreaInsets)
        }
        
        let titleOfButton = DGBundle.i18n(key:"Return")
        let backButton = DGUIUtils.createUIButton(titleOfButton: titleOfButton, target: self, action: #selector(DGRuleDescriptionViewController.back))
        safeView.addSubview(backButton)
        backButton.snp.makeConstraints { (make) in
            make.centerX.equalTo(safeView)
            make.bottom.equalTo(-DGUIUtils.MARGIN_OF_VIEW)
        }
        
        self.descriptionTextView = UITextView()
        safeView.addSubview(self.descriptionTextView)
        self.descriptionTextView.snp.makeConstraints { (make) in
            make.left.equalTo(DGUIUtils.MARGIN_OF_VIEW)
            make.right.equalTo(-DGUIUtils.MARGIN_OF_VIEW)
            make.top.equalTo(DGUIUtils.MARGIN_OF_VIEW)
            make.bottom.equalTo(backButton.snp.top).offset(-DGUIUtils.MARGIN_OF_VIEW)
        }
        self.descriptionTextView.isEditable = false
        self.descriptionTextView.backgroundColor = UIColor.clear
        self.descriptionTextView.font = DGFonts.NORMAL_BUTTON_FONT
        self.descriptionTextView.textColor = DGColors.LABEL_COLOR
        self.descriptionTextView.text = "1.两个人先摇盅掷好骰子\n"
            + "\n"
            + "2.双方轮流吹牛,猜两个人共同拥有的点数（比如4个6）\n"
            + "\n"
            + "3.第一个猜的个数必须大于1，也就是不能猜1个Y，至少猜2个Y\n"
            + "\n"
            + "4.后猜的必须大于前一个，从小到大为，2个1 < 2个2 < ... < 2个6 < 3个1 < 3个2 < ... < 10个6\n"
            + "\n"
            + "5.当你不相信对方猜的点数的时候就可以一起开盅, 如果大家实际手上的牌点数大于等于叫出的个数, 那么不信的人就输了;反之,不信的人就赢了（比如当对方猜4个6时我不信，那么如果两个人盅里的6的个数大于等于4，那么我就输了）\n"
            + "\n"
            + "6.点数1在上述过程中都没有人猜过,那么在结算时就可以代表任何数，但是1如果被猜过了,那么就只代表1,不可以代表任何别的数字了（比如开盅后有3个6，2个1，如果猜点过程没有人猜过X个1，那么就结算为5个6，否则就结算为3个6）"
        
        super.viewDidAppear(animated)
    }
    
    open override func viewDidLayoutSubviews() {
        super.viewDidLayoutSubviews()
        
        if descriptionTextView != nil {
            self.descriptionTextView.contentSize = self.descriptionTextView.sizeThatFits(self.descriptionTextView.bounds.size)
        }
    }
    
    @objc func back() {
        self.dismiss(animated: true, completion: nil)
    }
}
