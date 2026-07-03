//
//  DGSettingsViewController.swift
//  DiceGame
//
//  Created by Alex Chen on 15/5/28.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import UIKit
import DiceGameLib
import WhaleLib

class DGFeedbackViewController : UIViewController, UITableViewDataSource, UITableViewDelegate {
    fileprivate var feedbackTextField: UITextField!
    fileprivate var sendFeedbackButton: UIButton!
    
    fileprivate var tableView4HistorySuggestion:UITableView!
    fileprivate var historySuggestions = [String]() {
        didSet {
            self.tableView4HistorySuggestion.reloadData()
        }
    }
    
    override func viewDidLoad() {
        DGUIUtils.addMainBackgroundImageViewTo(parentView: self.view)
        
        let contentView = UIView()
        self.view.addSubview(contentView)
        contentView.snp.makeConstraints { (make) in
            make.edges.equalTo(self.view.safeAreaLayoutGuide.snp.edges)
        }
        
        let centerTitleLabel = WLUI.createUILabel(text: NSLocalizedString("Suggestion_Wall", comment:""))
        contentView.addSubview(centerTitleLabel)
        centerTitleLabel.snp.makeConstraints { (make) in
            make.top.equalTo(0)
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.height.equalTo(DGUIUtils.HEIGHT_OF_NAVIGATION_BAR)
        }
        
        let backButton = WLUI.createUIButton(image:UIImage(named: "return_1024.png")!, margin:10, target: self, action: #selector(DGFeedbackViewController.back))
        contentView.addSubview(backButton)
        backButton.snp.makeConstraints { (make) in
            make.height.equalTo(DGUIUtils.HEIGHT_OF_NAVIGATION_BAR)
            make.width.equalTo(DGUIUtils.HEIGHT_OF_NAVIGATION_BAR)
            make.left.equalTo(DGUIUtils.MARGIN_OF_VIEW)
            make.top.equalTo(0)
        }
        
        self.sendFeedbackButton = WLUI.createUIButton(image:UIImage(named: "send_1024.png")!, margin:10, target: self, action: #selector(DGFeedbackViewController.sendFeedback))
        contentView.addSubview(self.sendFeedbackButton)
        self.sendFeedbackButton.snp.makeConstraints { (make) in
            make.right.equalTo(-DGUIUtils.MARGIN_OF_VIEW)
            make.top.equalTo(0)
            make.height.equalTo(DGUIUtils.HEIGHT_OF_NAVIGATION_BAR)
            make.width.equalTo(DGUIUtils.HEIGHT_OF_NAVIGATION_BAR)
        }
        
        self.feedbackTextField = UITextField()
        contentView.addSubview(self.feedbackTextField)
        self.feedbackTextField.snp.makeConstraints { (make) in
            make.left.equalTo(DGUIUtils.MARGIN_OF_VIEW)
            make.right.equalTo(-DGUIUtils.MARGIN_OF_VIEW)
            make.top.equalTo(centerTitleLabel.snp.bottom)
            make.height.equalTo(DGUIUtils.HEIGHT_OF_NAVIGATION_BAR)
        }
        self.feedbackTextField.backgroundColor = UIColor.white
        self.feedbackTextField.placeholder = NSLocalizedString("My_Suggestion", comment:"")
        
        self.tableView4HistorySuggestion = UITableView()
        contentView.addSubview(self.tableView4HistorySuggestion)
        self.tableView4HistorySuggestion.snp.makeConstraints { (make) in
            make.left.equalTo(DGUIUtils.MARGIN_OF_VIEW)
            make.right.equalTo(-DGUIUtils.MARGIN_OF_VIEW)
            make.top.equalTo(self.feedbackTextField.snp.bottom)
            make.bottom.equalTo(0)
        }
        self.tableView4HistorySuggestion.backgroundColor = UIColor.clear
        self.tableView4HistorySuggestion.separatorStyle = UITableViewCell.SeparatorStyle.none
        self.tableView4HistorySuggestion.dataSource = self
        self.tableView4HistorySuggestion.delegate = self

        super.viewDidLoad()
        
        self.reloadData()
    }
    
    // MARK: - Instance Method
    @objc func back() {
        self.dismiss(animated: true, completion: nil)
    }
    
    fileprivate func reloadData() {
        DGClientActions.fetchFeedbacks { (history) -> Void in
            DispatchQueue.main.async(execute: {
                self.historySuggestions = history
            })
        }
    }
    
    @objc func sendFeedback() {
        if let feedbackContent = self.feedbackTextField.text , feedbackContent.count > 0 {
            self.sendFeedbackButton.isEnabled = false
            
            DGClientActions.sendFeedback(feedbackContent, callback: { () -> Void in
                DispatchQueue.main.async(execute: {
                    self.sendFeedbackButton.isEnabled = true
                    self.feedbackTextField.resignFirstResponder()
                    self.feedbackTextField.text = nil
                    self.reloadData()
                    
                    let alertController = UIAlertController(title: NSLocalizedString("Thank_You_For_Your_Support", comment:""), message: nil, preferredStyle: UIAlertController.Style.alert)
                    alertController.addAction(UIAlertAction(title:NSLocalizedString("Yes", comment:""), style:UIAlertAction.Style.default, handler: nil))
                    
                    self.present(alertController, animated: true, completion: nil)
                })
            })
            
        }
    }
    
    // MARK: - UITableViewDataSource
    func numberOfSections(in tableView: UITableView) -> Int {
        return 1
    }
    
    func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        return self.historySuggestions.count
    }
    
    func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        let cellIdentifier = "Cell"
        var cell = tableView.dequeueReusableCell(withIdentifier: cellIdentifier)
        if cell == nil {
            cell = UITableViewCell(style: UITableViewCell.CellStyle.default, reuseIdentifier: cellIdentifier)
            cell?.selectionStyle = UITableViewCell.SelectionStyle.none
            cell?.backgroundColor = UIColor.clear
            
            let backgroundLabel = UILabel(frame: CGRect(x: 0,y: 0,width: cell!.bounds.width, height: cell!.bounds.height))
            backgroundLabel.textColor = UIColor.white
            backgroundLabel.numberOfLines = 0
            cell?.backgroundView = backgroundLabel
        }
        
        (cell?.backgroundView as! UILabel).text = "🎲" + self.historySuggestions[(indexPath as NSIndexPath).row]
        
        return cell!
    }
    
    // MARK: - UITableViewDelegate
    func tableView(_ tableView: UITableView, heightForRowAt indexPath: IndexPath) -> CGFloat {
        let suggest = self.historySuggestions[(indexPath as NSIndexPath).row]
        return DGUIUtils.calculatePreferredHeight(suggest, font: DGFonts.NORMAL_BUTTON_FONT, fixedWidth: tableView.bounds.width) + 10
    }
}
