//
//  CountOfFactPickerView.swift
//  DiceGameLib
//
//  Created by apple on 15/7/14.
//  Copyright (c) 2015年 WhaleStudio. All rights reserved.
//

import UIKit

class DGGuessPickerView:UIPickerView, UIPickerViewDataSource, UIPickerViewDelegate {
    var countOfFullPlayers = 4 {
        didSet {
            self.reloadAllComponents()
        }
    }
    
    init() {
        super.init(frame:CGRect.zero)

        self.dataSource = self
        self.delegate = self
    }
    
    var selectedGuess:DGGuess {
        get {
            let selectedCount = self.selectedRow(inComponent: 0) + 1
            let selectedFact = self.selectedRow(inComponent: 1) + 1
            
            return DGGuess(count: selectedCount, factor: selectedFact)
        }
        
        set {
            self.selectRow(newValue.count - 1, inComponent: 0, animated: true)
            self.selectRow(newValue.factor - 1, inComponent: 1, animated: true)
        }
    }

    required init(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    // returns the number of 'columns' to display.
    func numberOfComponents(in pickerView: UIPickerView) -> Int {
        return 2
    }
    
    // returns the # of rows in each component..
    func pickerView(_ pickerView: UIPickerView, numberOfRowsInComponent component: Int) -> Int {
        if component == 0 {
            return self.countOfFullPlayers * DGGameRules.COUNT_OF_DICE
        } else {
            return DGGameRules.FACTOR_OF_DICE
        }
    }
        
    // returns width of column and height of row for each component.
    func pickerView(_ pickerView: UIPickerView, widthForComponent component: Int) -> CGFloat {
        return pickerView.frame.size.width/2
    }
    
    func pickerView(_ pickerView: UIPickerView, rowHeightForComponent component: Int) -> CGFloat {
        return pickerView.frame.size.height/3
    }

    
    // these methods return either a plain NSString, a NSAttributedString, or a view (e.g UILabel) to display the row for the component.
    // for the view versions, we cache any hidden and thus unused views and pass them back for reuse.
    // If you return back a different object, the old one will be released. the view will be centered in the row rect
//    func pickerView(pickerView: UIPickerView, titleForRow row: Int, forComponent component: Int) -> String! {
//        if component == 0 {
//            return "\(row + 1)个"
//        } else {
//            return "\(row + 1)"
//        }
//    }
    
    func pickerView(_ pickerView: UIPickerView, viewForRow row: Int, forComponent component: Int, reusing view: UIView?) -> UIView {
        if view != nil {
            return view!
        }
        
        let size = CGSize(width: self.pickerView(self, widthForComponent: component), height: self.pickerView(self, rowHeightForComponent: component))
        if component == 0 {
            return self.createCountLabel(row + 1, size)
        } else {
            return self.createDiceFactImageView(row + 1, size)
        }
    }
    
    fileprivate func createCountLabel(_ count:Int, _ size:CGSize) -> UILabel {
        let label = DGUIUtils.createMiddleUILabel(initString: "\(count)")
        label.frame = CGRect(x: 0,y: 0,width: size.width,height: size.height)
        label.textAlignment = NSTextAlignment.right
        
        return label
    }
    
    fileprivate func createDiceFactImageView(_ fact:Int, _ size:CGSize) -> UIView {
        let returnView = UIView(frame:CGRect(x: 0, y: 0, width: size.width, height: size.height))
        let diceImage = UIImageView(image: DGUIUtils.getFixedDiceImage(number: fact))
        returnView.addSubview(diceImage)
        diceImage.snp.makeConstraints { (make) in
            make.center.equalTo(returnView)
            make.width.height.equalTo(min(size.width, size.height))
        }
        
        return returnView
    }
}
