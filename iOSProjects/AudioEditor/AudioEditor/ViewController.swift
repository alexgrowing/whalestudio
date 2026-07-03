//
//  ViewController.swift
//  AudioEditor
//
//  Created by alex on 2020/8/6.
//  Copyright © 2020 WhaleStudio. All rights reserved.
//

import UIKit

class ViewController: UIViewController {
    private enum Metrics {
        static let padding:CGFloat = 15
        static let iconImageViewWidth: CGFloat = 30
    }
    
    override func viewSafeAreaInsetsDidChange() {
        super.viewSafeAreaInsetsDidChange()
        
        testLayout3()
    }
    
    
    private func testLayout1() {
        let view1 = UIView()
        view1.backgroundColor = .red
        self.view.addSubview(view1)
        view1.translatesAutoresizingMaskIntoConstraints = false
        
        let view2 = UIView()
        view2.backgroundColor = .blue
        self.view.addSubview(view2)
        view2.translatesAutoresizingMaskIntoConstraints = false
        
        let view3 = UIView()
        view3.backgroundColor = .gray
        self.view.addSubview(view3)
        view3.translatesAutoresizingMaskIntoConstraints = false
        
        let margin = 30
        let spacing = 30
        
        let vfl1 = "H:|-margin-[redView]-spacing-[greenView(==redView)]-margin-|"
        self.view.addConstraints(NSLayoutConstraint.constraints(withVisualFormat: vfl1, options: .directionMask, metrics: ["margin":margin, "spacing":spacing], views:["redView":view1, "greenView":view2]))
        
        let vfl2 = "H:|-margin-[grayView]-margin-|"
        self.view.addConstraints(NSLayoutConstraint.constraints(withVisualFormat: vfl2, options: .directionMask, metrics: ["margin":margin, "spacing":spacing], views:["grayView":view3]))
        
        let vfl3 = "V:|-margin-[redView]-spacing-[grayView(==redView)]-margin-|"
        self.view.addConstraints(NSLayoutConstraint.constraints(withVisualFormat: vfl3, options: .directionMask, metrics: ["margin":margin, "spacing":spacing], views:["redView":view1, "grayView":view3]))
        
        let vfl4 = "V:|-margin-[greenView]-margin-|"
        self.view.addConstraints(NSLayoutConstraint.constraints(withVisualFormat: vfl4, options: .directionMask, metrics: ["margin":30], views: ["greenView":view2]))
        
    }

    private func testLayout2() {
        let centerView = UIView()
        self.view.addSubview(centerView)
        
        let v1 = createView(color: .black, parent: centerView)
        let v2 = createView(color: .blue, parent:centerView)
        let v3 = createView(color: .brown, parent: centerView)
        let v4 = createView(color: .red, parent: centerView)
        let v5 = createView(color: .yellow, parent: centerView)
        let v6 = createView(color: .cyan, parent: centerView)
        
        let metrics = ["m":10,"s":20]
        
        let vflH = "H:|-m-[vL(100)]-s[vR(100)]-m|"
        centerView.addConstraints(NSLayoutConstraint.constraints(withVisualFormat: vflH, options: .directionMask, metrics: metrics, views: ["vL":v1, "vR":v2]))
        centerView.addConstraints(NSLayoutConstraint.constraints(withVisualFormat: vflH, options: .directionMask, metrics: metrics, views: ["vL":v3, "vR":v4]))
        centerView.addConstraints(NSLayoutConstraint.constraints(withVisualFormat: vflH, options: .directionMask, metrics: metrics, views: ["vL":v5, "vR":v6]))
        
        let vflV = "V:|-m-[vU(30)]-s-[vM(30)]-s-[vD(30)]-m|"
        centerView.addConstraints(NSLayoutConstraint.constraints(withVisualFormat: vflV, options: .directionMask, metrics: metrics, views: ["vU":v1, "vM":v3, "vD":v5]))
        centerView.addConstraints(NSLayoutConstraint.constraints(withVisualFormat: vflV, options: .directionMask, metrics: metrics, views: ["vU":v2, "vM":v4, "vD":v6]))
    }
    
    private func testLayout3() {
        // SafeArea start
        let safeArea = UIView()
        safeArea.translatesAutoresizingMaskIntoConstraints = false
        self.view.addSubview(safeArea)
        safeArea.backgroundColor = .blue
        
        let newInsets = self.view.safeAreaInsets
        let leftMargin = newInsets.left > 0 ? newInsets.left : Metrics.padding
        let rightMargin = newInsets.right > 0 ? newInsets.right : Metrics.padding
        let topMargin = newInsets.top > 0 ? newInsets.top : Metrics.padding
        let bottomMargin = newInsets.bottom > 0 ? newInsets.bottom : Metrics.padding
        
        let metrics = [
        "topMargin": topMargin,
        "bottomMargin": bottomMargin,
        "leftMargin": leftMargin,
        "rightMargin": rightMargin
        ]
        
        self.view.addConstraints(NSLayoutConstraint.constraints(
            withVisualFormat: "V:|-topMargin-[safeView]-bottomMargin-|",
            options: .directionMask,
            metrics: metrics,
            views: [
                "safeView":safeArea
            ])
        )
        
        self.view.addConstraints(NSLayoutConstraint.constraints(
            withVisualFormat: "H:|-leftMargin-[safeView]-rightMargin-|",
            options: .directionMask,
            metrics: metrics,
            views: [
                "safeView":safeArea
            ])
        )
        
        // CenterArea start
        let centerArea = UIView()
        centerArea.translatesAutoresizingMaskIntoConstraints = false
        centerArea.backgroundColor = .yellow
        safeArea.addSubview(centerArea)
        safeArea.addConstraints(NSLayoutConstraint.constraints(
            withVisualFormat: "H:[center(100)]",
            options: [],
            metrics: nil,
            views: [
                "center":centerArea
            ])
        )
        safeArea.addConstraints(NSLayoutConstraint.constraints(
            withVisualFormat: "V:[center(200)]",
            options: [],
            metrics: nil,
            views: [
                "center":centerArea
            ])
        )
        safeArea.addConstraints([NSLayoutConstraint.init(
            item: centerArea,
            attribute: .centerY,
            relatedBy: .equal,
            toItem: safeArea,
            attribute: .centerY,
            multiplier: 1,
            constant: 0
        )])
        safeArea.addConstraints([NSLayoutConstraint.init(
            item: centerArea,
            attribute: .centerX,
            relatedBy: .equal,
            toItem: safeArea,
            attribute: .centerX,
            multiplier: 1,
            constant: 0
        )])
        
        
        // Buttons start
//        let v1 = createView(color: .black, parent: safeArea)
//        let v2 = createView(color: .yellow, parent: safeArea)
//        let v3 = createView(color: .red, parent: safeArea)
//
//        let views = ["v1":v1, "v2":v2, "v3":v3]
//
//        var cons = NSLayoutConstraint.constraints(
//            withVisualFormat: "H:|-[v1(30)]-20-[v2]-20-[v3(30)]-|",
//            options: .alignAllCenterY,
//            metrics: nil,
//            views: views
//        )
//
//        cons += NSLayoutConstraint.constraints(
//            withVisualFormat: "V:|-[v1(30)]",
//            options: [],
//            metrics: nil,
//            views: views
//        )
//
//        cons += NSLayoutConstraint.constraints(
//            withVisualFormat: "V:[v2(20)]",
//            options: [],
//            metrics: nil,
//            views: views
//        )
//
//        cons += NSLayoutConstraint.constraints(
//            withVisualFormat: "V:[v3(30)]",
//            options: [],
//            metrics: nil,
//            views: views
//        )
//
//        safeArea.addConstraints(cons)
    }
    
    private func createView(color:UIColor, parent:UIView) -> UIView {
        let view = UIView()
        view.backgroundColor = color
        view.translatesAutoresizingMaskIntoConstraints = false
        
        parent.addSubview(view)
        
        return view
    }
}

