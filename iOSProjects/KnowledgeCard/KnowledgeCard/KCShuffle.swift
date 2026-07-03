//
//  KCShuffle.swift
//  KnowledgeCard
//
//  Created by alex on 2018/7/12.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import UIKit
import WhaleLib

class KCShuffleViewController : UIViewController, KCEditViewControllerDelegate, KCKnowledgeViewDelegate {
    @IBOutlet weak var messageLabel: UILabel!
    @IBOutlet weak var cardsContainer: UIView!
    @IBOutlet weak var cardsContainerAbove: UIView!
    @IBOutlet weak var bottomToolbar: UIView!
    @IBOutlet weak var aboveToolbar: UIView!
    @IBOutlet weak var editCardButton: UIButton!
    @IBOutlet weak var panTipLabel: UILabel!
    
    @IBOutlet weak var constraintOfBottomToolbar: NSLayoutConstraint!
    @IBOutlet weak var constraintOfAboveToolbar: NSLayoutConstraint!
    private var hideToolbar = true
    
    var shuffleDataSource:KCDataSource!
    var shuffleDelegate:KCShuffleViewControllerDelegate!
    
    fileprivate var loadedCardViewsAbove = [KCKnowledgeView]()
    fileprivate var loadedCardViewsBelow = [KCKnowledgeView]()
    
    fileprivate var orders = [Int]()
    fileprivate var indexInOrdersOfCardShowing: Int!
    
    override func viewDidLoad() {
        super.viewDidLoad()
        
        self.aboveToolbar.backgroundColor = BORDER_COLOR
        self.bottomToolbar.backgroundColor = BORDER_COLOR
        
        self.aboveToolbar.isHidden = true
        self.bottomToolbar.isHidden = true
        self.panTipLabel.isHidden = true
    }
    
    override func updateViewConstraints() {
        super.updateViewConstraints()
        
        if self.hideToolbar {
            self.constraintOfBottomToolbar.constant = -self.bottomToolbar.frame.height
            self.constraintOfAboveToolbar.constant = -self.aboveToolbar.frame.height
        } else {
            self.constraintOfBottomToolbar.constant = 0
            self.constraintOfAboveToolbar.constant = 0
        }
    }
    
    // MARK: - IBActions
    @IBAction func btnBack(_ sender: Any) {
        self.dismiss(animated: true) {
            self.shuffleDelegate.kcShuffleDidExit()
        }
    }
    
    @IBAction func btnShuffleCards() {
        if self.indexInOrdersOfCardShowing >= 0 {
            let vc = WLUI.alertAsk(title: "洗牌", message: "还没完成所有卡片学习，确定洗牌?") {
                self.resetOrdersBy(startIndex: 0, order: false)
            }
            self.present(vc, animated: true) {
                // do nothing
            }
        } else {
            self.resetOrdersBy(startIndex: 0, order: false)
        }
    }
    @IBAction func btnEditCard() {
        if self.orders.count > self.indexInOrdersOfCardShowing {
            if let kl = self.getKnowledgeShowing() as? KCTextKnowledge {
                self.edit(textKnowledge: kl)
            }
        }
    }
    @IBAction func btnDeleteCard() {
        if let firstView = self.loadedCardViewsBelow.first {
            let vc = WLUI.alertAsk(title: "删除当前卡片", message: "") {
                let indexInKCMain = self.orders[self.indexInOrdersOfCardShowing]
                self.shuffleDataSource.datasourceDeleteKnowledgeBy(index: indexInKCMain)
                
                firstView.removeFromSuperview()
                self.loadedCardViewsBelow.removeFirst()
                
                var oi = self.orders.count - 1
                while oi >= 0 {
                    if self.orders[oi] > indexInKCMain {
                        self.orders[oi] = self.orders[oi] - 1
                    } else if self.orders[oi] == indexInKCMain {
                        self.orders.remove(at: oi)
                        break
                    }
                    
                    oi = oi - 1
                }
                
                self.loadKnowledgeViewAroundShowing()
                self.loadedCardViewsDidChanged()
            }
            
            self.present(vc, animated: true) {
                // do nothing
            }
        }
    }
    
    // MARK: - KCEditViewControllerDelegate
    func kcEditViewControllerAfterEdit(uuid: String) {        
        if let kl = KCMain.instance.knowledgeBy(uuid: uuid) {
            let klView = self.createUIViewFromKnowledge(knowledge: kl) { (v) in
                self.cardsContainer.addSubview(v)
                
                v.snp.makeConstraints { (make) in
                    make.edges.equalTo(self.cardsContainer)
                }
            }
            
            self.loadedCardViewsBelow.first!.removeFromSuperview()
            self.loadedCardViewsBelow.removeFirst()
            self.loadedCardViewsBelow.insert(klView, at: 0)
            
            self.loadedCardViewsDidChanged()
        }
    }
    
    // MARK: - KCKnowledgeViewDelegate
    func kcKnowledgeViewTap() {
        self.hideToolbar = !self.hideToolbar
        self.view.setNeedsUpdateConstraints()
        
        if !self.hideToolbar {
            self.aboveToolbar.isHidden = self.hideToolbar
            self.bottomToolbar.isHidden = self.hideToolbar
        }
        
        UIView.animate(withDuration: 0.5, animations: {
            self.view.layoutIfNeeded()
        }) { (success) in
            if self.hideToolbar {
                self.aboveToolbar.isHidden = self.hideToolbar
                self.bottomToolbar.isHidden = self.hideToolbar
            }
        }
    }
    
    func kcKnowledgeViewPan(translation: CGPoint, isLeft:Bool, isEnded:Bool) {
        let mode = isLeft ? PanMode.left : PanMode.right
        mode.pan(vc: self, translation: translation, isEnded: isEnded)
    }
    
    // MARK: - Instance Methods
    func resetOrdersBy(startIndex:Int, order:Bool) {
        for view in self.loadedCardViewsBelow {
            view.removeFromSuperview()
        }
        self.loadedCardViewsBelow.removeAll()
        for view in self.loadedCardViewsAbove {
            view.removeFromSuperview()
        }
        self.loadedCardViewsAbove.removeAll()
        
        let range = 0 ..< self.shuffleDataSource.datasourceCountOfThumbs()
        let ints = range.map { (index) -> Int in
            index
        }
        
        if order {
            self.orders = OrderMode.ordered.outputOrders(sourceOrders: ints)
        } else {
            self.orders = OrderMode.shuffle.outputOrders(sourceOrders: ints)
        }
        
        self.indexInOrdersOfCardShowing = startIndex
        self.loadCardShowing()
        self.loadKnowledgeViewAroundShowing()
        self.loadedCardViewsDidChanged()
    }
    
    private func loadCardShowing() {
        let indexOfKnow = self.orders[self.indexInOrdersOfCardShowing]
        
        let know = self.shuffleDataSource.datasourceKnowledgeBy(index: indexOfKnow)
        let knowView = self.createUIViewFromKnowledge(knowledge: know) { (v) in
            self.cardsContainer.addSubview(v)
            
            v.snp.makeConstraints { (make) in
                make.edges.equalTo(self.cardsContainer)
            }
        }
        self.loadedCardViewsBelow.append(knowView)
    }
    
    private func loadKnowledgeViewAroundShowing() {
        while self.loadedCardViewsBelow.count < 4 {
            let indexInOrders2Load = self.indexInOrdersOfCardShowing + self.loadedCardViewsBelow.count
            if indexInOrders2Load < 0 || indexInOrders2Load >= self.orders.count {
                break
            }
            let indexOfKnow = self.orders[indexInOrders2Load]
            
            let know = self.shuffleDataSource.datasourceKnowledgeBy(index: indexOfKnow)
            let knowView = self.createUIViewFromKnowledge(knowledge: know) { (v) in
                self.cardsContainer.insertSubview(v, belowSubview: self.loadedCardViewsBelow.last!)
                
                v.snp.makeConstraints { (make) in
                    make.edges.equalTo(self.cardsContainer)
                }
            }
            self.loadedCardViewsBelow.append(knowView)
        }
        
        while self.loadedCardViewsAbove.count < 3 {
            let indexInOrders2Load = self.indexInOrdersOfCardShowing - self.loadedCardViewsAbove.count - 1
            if indexInOrders2Load < 0 || indexInOrders2Load >= self.orders.count {
                break
            }
            let indexOfKnow = self.orders[indexInOrders2Load]
            
            let know = self.shuffleDataSource.datasourceKnowledgeBy(index: indexOfKnow)
            let knowView = self.createUIViewFromKnowledge(knowledge: know) { (v) in
                self.cardsContainerAbove.addSubview(v)
                
                v.snp.makeConstraints { (make) in
                    make.edges.equalTo(self.cardsContainerAbove)
                }
            }
            self.loadedCardViewsAbove.append(knowView)
        }
    }
    
    private func loadedCardViewsDidChanged() {
        if self.indexInOrdersOfCardShowing + 1 > self.orders.count {
            self.messageLabel.text = "到底了"
        } else {
            self.messageLabel.text = "\(self.indexInOrdersOfCardShowing + 1)/\(self.orders.count)"
        }
        
        if let _ = self.getKnowledgeShowing() as? KCTextKnowledge {
            self.editCardButton.isEnabled = true
        } else {
            self.editCardButton.isEnabled = false
        }
    }
    
    private func createUIViewFromKnowledge(knowledge:KCKnowledge, add2ParentViewFunc:(_ v:UIView) -> Void) -> KCKnowledgeView {
        let klView = knowledge.asUIView(delegate: self)
        add2ParentViewFunc(klView)
        
        return klView
    }
    
    fileprivate func showNextCard() {
        if let fv = self.loadedCardViewsBelow.first {
            fv.removeFromSuperview()
            self.loadedCardViewsBelow.removeFirst()
            
            self.cardsContainerAbove.insertSubview(fv, at: 0)
            fv.snp.makeConstraints { (make) in
                make.edges.equalTo(self.cardsContainerAbove)
            }
            self.loadedCardViewsAbove.insert(fv, at: 0)
            
            self.indexInOrdersOfCardShowing = self.indexInOrdersOfCardShowing + 1
            self.loadKnowledgeViewAroundShowing()
            self.loadedCardViewsDidChanged()
        }
    }
    
    fileprivate func showPrevCard() {
        if let fv = self.loadedCardViewsAbove.first {
            fv.removeFromSuperview()
            self.loadedCardViewsAbove.removeFirst()
            
            self.cardsContainer.addSubview(fv)
            fv.snp.makeConstraints { (make) in
                make.edges.equalTo(self.cardsContainer)
            }
            self.loadedCardViewsBelow.insert(fv, at: 0)
            
            self.indexInOrdersOfCardShowing = self.indexInOrdersOfCardShowing - 1
            self.loadKnowledgeViewAroundShowing()
            self.loadedCardViewsDidChanged()
        }
    }
    
    private func getKnowledgeShowing() -> KCKnowledge? {
        let io = self.indexInOrdersOfCardShowing!
        if self.orders.count > io && io >= 0 {
            return self.shuffleDataSource.datasourceKnowledgeBy(index: self.orders[io])
        }
        
        return nil
    }
    
    private func edit(textKnowledge:KCTextKnowledge) {
        if let vc = self.storyboard?.instantiateViewController(withIdentifier: "editvc") as? KCEditViewController {
            
            self.present(vc, animated: true) {
                vc.set(textKL: textKnowledge, delegate: self)
            }
        }
    }
}

private enum PanMode {
    case left
    case right
    
    fileprivate func pan(vc:KCShuffleViewController, translation:CGPoint, isEnded:Bool) {
        if let targetView = self.getTargetView(vc: vc) {
            let xPoint = self.getXPoint(translation: translation)
            let currentPageNumber = vc.indexInOrdersOfCardShowing + 1
            if self.shouldRebound(xPoint: xPoint, targetView: targetView) {
                vc.panTipLabel.text = String(currentPageNumber)
            } else {
                vc.panTipLabel.text = self.nextPageNumber(currentPageNumber: currentPageNumber, totalPageNumbers: vc.orders.count)
            }
            vc.panTipLabel.isHidden = false
            
            targetView.transform = CGAffineTransform(translationX: xPoint, y: 0)
            
            if isEnded {
                vc.panTipLabel.isHidden = true
                
                if self.shouldRebound(xPoint: xPoint, targetView: targetView) {
                    UIView.animate(withDuration: 0.2) {
                        targetView.transform = CGAffineTransform(translationX: 0, y: 0)
                    }
                } else {
                    UIView.animate(withDuration: 0.2, animations: {
                        self.disappear(targetView: targetView)
                    }) { (success) in
                        if success {
                            self.targetViewDidDisappear(vc: vc)
                            targetView.reset()
                        }
                    }
                }
            }
        }
    }
    
    private func getTargetView(vc:KCShuffleViewController) -> KCKnowledgeView? {
        switch self {
        case .left:
            return vc.loadedCardViewsBelow.first
        case .right:
            return vc.loadedCardViewsAbove.first
        }
    }
    
    private func getXPoint(translation:CGPoint) -> CGFloat {
        switch self {
        case .left:
            return translation.x > 0 ? 0 : translation.x
        case .right:
            return translation.x < 0 ? 0 : translation.x
        }
    }
    
    private func shouldRebound(xPoint:CGFloat, targetView:KCKnowledgeView) -> Bool {
        return abs(xPoint) < targetView.bounds.width / 3
    }
    
    private func nextPageNumber(currentPageNumber:Int, totalPageNumbers:Int) -> String {
        let pn:Int
        switch self {
        case .left:
            pn = currentPageNumber + 1
        case .right:
            pn = currentPageNumber - 1
        }
        
        if pn <= 0 {
            return "没有上一页了"
        } else if pn > totalPageNumbers {
            return "没有下一页了"
        } else {
            return String(pn)
        }
    }
    
    private func disappear(targetView:KCKnowledgeView) {
        switch self {
        case .left:
            targetView.transform = CGAffineTransform(translationX: -targetView.bounds.width, y: 0)
        case .right:
            targetView.transform = CGAffineTransform(translationX: targetView.bounds.width, y: 0)
        }
    }
    
    private func targetViewDidDisappear(vc:KCShuffleViewController) {
        switch self {
        case .left:
            vc.showNextCard()
        case .right:
            vc.showPrevCard()
        }
    }
}

private enum OrderMode {
    case ordered
    case shuffle
    
    fileprivate func outputOrders(sourceOrders:[Int]) -> [Int] {
        switch self {
        case .ordered:
            return sourceOrders
        case .shuffle:
            return sourceOrders.shuffle()
        }
    }
}


protocol KCShuffleViewControllerDelegate {
    func kcShuffleDidExit()
}

let BORDER_COLOR = UIColor(displayP3Red: 200/255.0, green: 200/255.0, blue: 200/255.0, alpha: 1.0)
