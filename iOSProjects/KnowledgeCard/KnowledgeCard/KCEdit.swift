//
//  KCEdit.swift
//  KnowledgeCard
//
//  Created by alex on 2018/5/3.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import UIKit

class KCEditViewController : UIViewController {
    
    @IBOutlet weak var contentTextView: UITextView!
    @IBOutlet weak var gapBetweenToolbarAndBottom: NSLayoutConstraint!
    
    private var uuidEditing:String!
    private var delegate:KCEditViewControllerDelegate!
    
    override func viewDidLoad() {
        NotificationCenter.default.addObserver(self, selector: #selector(keyboardWillShow(_:)), name: UIResponder.keyboardWillShowNotification, object: nil)
        
        self.contentTextView.contentInset = UIEdgeInsets(top: 20, left: 20, bottom: 20, right: 20)
        
        super.viewDidLoad()
    }
    
    @IBAction func cancel(_ sender: UIBarButtonItem) {
        self.dismiss(animated: true) {
            // do nothing
        }
    }
    
    @IBAction func done(_ sender: UIBarButtonItem) {
        KCMain.instance.edit(uuid: self.uuidEditing, newText: self.contentTextView.text)

        self.dismiss(animated: true) {
            self.delegate.kcEditViewControllerAfterEdit(uuid: self.uuidEditing)
        }
    }
    
    @objc func keyboardWillShow(_ notification: Notification) {
//        guard let fr = UIResponder.firstResponder() else {
//            return
//        }
        
        let dict = NSDictionary(dictionary: notification.userInfo!)
        let keyboardFrame = dict[UIResponder.keyboardFrameEndUserInfoKey] as! CGRect
        
        self.gapBetweenToolbarAndBottom.constant = keyboardFrame.height
    }
    
    // MARK: - Instance Methods
    func set(textKL:KCTextKnowledge, delegate:KCEditViewControllerDelegate) {
        let style = NSMutableParagraphStyle()
        style.lineSpacing = 5
        let attributes = [
            NSAttributedString.Key.font :UIFont.systemFont(ofSize: 18),
            NSAttributedString.Key.paragraphStyle : style
        ]
        
        self.contentTextView.attributedText = NSAttributedString(string: textKL.getText(), attributes: attributes)
        
        self.uuidEditing = textKL.uuid
        self.delegate = delegate
        
        self.contentTextView.becomeFirstResponder()
    }
}

protocol KCEditViewControllerDelegate {
    func kcEditViewControllerAfterEdit(uuid:String)
}
