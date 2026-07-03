//
//  DGStartupViewController.swift
//  DiceGame
//
//  Created by Alex Chen on 15/4/23.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import UIKit
import DiceGameLib

class DGLocalStartupViewController : UIViewController {
    
    override func viewDidLoad() {        
        DGUIUtils.addMainBackgroundImageViewTo(parentView: self.view)
                
        let widthOfHomeButton:CGFloat = 120
        let heightOfHomeButton:CGFloat = 80
        let verticalPaddingOfHomeButton:CGFloat = 20

        let fightAIButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Fight_AI", comment:""), target:self, action:#selector(DGLocalStartupViewController.playWithComputer))
        self.view.addSubview(fightAIButton)
        fightAIButton.snp.makeConstraints { (make) in
            make.width.equalTo(widthOfHomeButton)
            make.height.equalTo(heightOfHomeButton)
            make.centerX.equalTo(self.view)
            make.centerY.equalTo(self.view).offset(-(heightOfHomeButton + verticalPaddingOfHomeButton))
        }
        
        let ruleButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Rule", comment:""), target:self, action:#selector(DGLocalStartupViewController.showRules))
        self.view.addSubview(ruleButton)
        ruleButton.snp.makeConstraints { (make) in
            make.width.equalTo(widthOfHomeButton)
            make.height.equalTo(heightOfHomeButton)
            make.centerX.equalTo(self.view)
            make.centerY.equalTo(self.view)
        }
        
        let downloadButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Download_Network_Version", comment:""), target:self, action:#selector(DGLocalStartupViewController.downloadNetworkVersion))
        self.view.addSubview(downloadButton)
        downloadButton.snp.makeConstraints { (make) in
            make.width.equalTo(widthOfHomeButton)
            make.height.equalTo(heightOfHomeButton)
            make.centerX.equalTo(self.view)
            make.centerY.equalTo(self.view).offset(heightOfHomeButton + verticalPaddingOfHomeButton)
        }
        
        super.viewDidLoad()
    }
    
    // MARK: - IBAction
    @objc func playWithComputer() {
        let gamevc = DGGameViewController()
        let client = DGComputerServer().createHumanClient()
        gamevc.client = client

        self.present(gamevc, animated: false, completion: {
            DispatchQueue.main.async {
                client.notifyServerOfQuickStart()
            }
        })
    }
    
    @objc func showRules() {
        let ruleViewController = DiceGameLib.DGRuleDescriptionViewController()
        self.present(ruleViewController, animated: true, completion: nil)
    }
    
    @objc func downloadNetworkVersion() {
        // https://itunes.apple.com/us/app/jiu-ba-tou-zi/id493902223
        UIApplication.shared.open(URL(string: "https://itunes.apple.com/us/app/jiu-ba-tou-zi/id493902223")!, options: convertToUIApplicationOpenExternalURLOptionsKeyDictionary([String : Any]()), completionHandler: nil)
    }
}

// Helper function inserted by Swift 4.2 migrator.
fileprivate func convertToUIApplicationOpenExternalURLOptionsKeyDictionary(_ input: [String: Any]) -> [UIApplication.OpenExternalURLOptionsKey: Any] {
	return Dictionary(uniqueKeysWithValues: input.map { key, value in (UIApplication.OpenExternalURLOptionsKey(rawValue: key), value)})
}
