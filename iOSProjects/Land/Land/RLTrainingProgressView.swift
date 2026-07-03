//
//  RLTrainingProgressView.swift
//  Land
//
//  Created by apple on 16/1/20.
//  Copyright © 2016年 G & B. All rights reserved.
//

import UIKit

class RLTrainingProgressView : UIView {
    var delegate:RLTrainingProgressViewDelegate!
    
    @IBOutlet weak var progressView: UIProgressView!
    @IBOutlet weak var countProgressDescriptionLabel: UILabel!
    @IBOutlet weak var progressDescriptionLabel: UILabel!
    @IBOutlet weak var quickFinishButton: UIButton!
    
    fileprivate var diamondCost4QuickFinish = 0 {
        didSet {
            if self.diamondCost4QuickFinish == 0 {
                self.quickFinishButton.setTitle("已完成", for: UIControl.State())
                self.quickFinishButton.setBackgroundImage(nil, for: UIControl.State())
            } else if oldValue != self.diamondCost4QuickFinish {
                self.quickFinishButton.setTitle(nil, for: UIControl.State())
                self.quickFinishButton.setBackgroundImage(drawDiamondPrice(self.diamondCost4QuickFinish, size: self.quickFinishButton.bounds.size), for: UIControl.State())
            }
        }
    }
    
    func setTraining(_ training:RLTraining) {
        self.progressView.progress = Float(training.passedTime / training.allTime)
        
        let timeLeft = training.leftTime
        self.countProgressDescriptionLabel.text = "\(training.countOfSoldierFinished)/\(training.countOfSoldier)"
        self.progressDescriptionLabel.text = "\(asTimeDescription(timeLeft))"
        
        self.diamondCost4QuickFinish = Int(ceil(timeLeft / Double(COUNT_OF_SECONDS_PER_DIAMOND)))
        
        DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) {
            if timeLeft > 0 && !self.isHidden {
                self.setTraining(training)
            }
        }
    }
    
    @IBAction func quickFinish() {
        self.delegate.quickFinishOnTrainingProgressView()
    }
    @IBAction func iknow() {
        self.delegate.iknowOnTrainingProgressView()
    }
}

protocol RLTrainingProgressViewDelegate {
    func quickFinishOnTrainingProgressView()
    func iknowOnTrainingProgressView()
}
