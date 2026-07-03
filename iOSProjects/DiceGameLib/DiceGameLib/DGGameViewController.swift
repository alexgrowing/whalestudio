//
//  DGGameViewController.swift
//  DiceGameLib
//
//  Created by Alex Chen on 15/4/23.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import UIKit
import AVFoundation
import SnapKit

private let VERTICAL_PADDING:CGFloat = 10

private let FIVE_UNKNOW_DICES = [0,0,0,0,0]

open class DGGameViewController : UIViewController, DGRoomViewDelegate, DGActionsOnMessageReceivedFromServer {
    open var client:DGGameClient! {
        willSet {
            if self.client != nil {
                self.client.actionsOnMessageReceivedFromServer = nil
            }
        }
        
        didSet {
            if self.client != nil {
                self.client.actionsOnMessageReceivedFromServer = self
            }
        }
    }
    
    fileprivate var allPlayers:[DGPlayer]! {
        didSet {
            self.roomView.resetRoomWithPlayers(self.allPlayers)
        }
    }
    
    private var topConstraintOfSafeArea:Constraint?
    private var bottomConstraintOfSafeArea:Constraint?
    
    // MARK: - Fields.MatchingPlayerView
    fileprivate var matchingPlayerView:UIView!
    fileprivate var exitGameButton:UIButton!
    fileprivate var matchingPlayerInforLabel:UILabel!
    
    // MARK: - Fields.DGRoomView
    fileprivate var roomView:DGRoomView!
    
    // MARK: - Fields.maniCountOfFactorView
    fileprivate var maniCountOfFactorView:UIView!
    
    fileprivate var count2Guess:Int = 0 {
        didSet {
            self.count2GuessLabel.text = "\(self.count2Guess)"
        }
    }
    fileprivate var count2GuessLabel:UILabel!
    fileprivate var decreaseCountButton:UIButton!
    fileprivate var increaseCountButton:UIButton!
    
    fileprivate var factor1Button:UIButton!
    fileprivate var factor2Button:UIButton!
    fileprivate var factor3Button:UIButton!
    fileprivate var factor4Button:UIButton!
    fileprivate var factor5Button:UIButton!
    fileprivate var factor6Button:UIButton!
    fileprivate var all6FactorButtons:[UIButton]!

    // MARK: - Fields.guessDiceView
    fileprivate var guessDiceView: UIView!

    fileprivate var sendMyGuessButton: UIButton!
    fileprivate var pointOutLiarButton: UIButton!
    fileprivate var useCardButton:UIButton!
    
    // MARK: - Fields.someoneLeftView
    fileprivate var someoneLeftView:UIView!
    fileprivate var nameOfSomeOneLabel:UILabel!
    fileprivate var reasonOfLeftLabel:UILabel!
    
    fileprivate var __loadingIndicator__ : UIActivityIndicatorView!
    fileprivate var loadingIndicator : UIActivityIndicatorView! {
        get {
            if self.__loadingIndicator__ == nil {
                self.__loadingIndicator__ = UIActivityIndicatorView(style: UIActivityIndicatorView.Style.white)
                self.__loadingIndicator__.frame = CGRect(x: 0, y: 0, width: 38, height: 38)
                self.__loadingIndicator__.center = CGPoint(x: self.view.bounds.width / 2, y: self.view.bounds.height / 2)
                
                self.view.addSubview(self.__loadingIndicator__)
            }
            
            return self.__loadingIndicator__
        }
    }
    
    fileprivate var screenTouchInforLabel: DGFlickLabel!
    fileprivate var oneHasBeenGuessed = false {
        didSet {
            if self.oneHasBeenGuessed {
                self.factor1Button.setImage(DGUIUtils.getFixedDiceImage(number: 1), for: .normal)
            } else {
                self.factor1Button.setImage(DGUIUtils.getFlexiableDiceImage(), for: .normal)
            }
        }
    }
    
    // MARK: - StartRoundView
    fileprivate var startNewRoundButton:UIButton!
    fileprivate var toMainMenuButton:UIButton!
    
    fileprivate var action4StartNewRound:DGStartNewButtonAction = .nothing {
        didSet {
            switch self.action4StartNewRound {
            case .onIWinRound:
                self.startNewRoundButton.setTitle(self.textOfNewRoundButtonOnIWinRound(), for: UIControl.State())
                self.startNewRoundButton.isHidden = false
                self.toMainMenuButton.isHidden = false
            case .onINotWinRound:
                self.startNewRoundButton.setTitle(self.textOfNewRoundButtonOnINotWinRound(), for: UIControl.State())
                self.startNewRoundButton.isHidden = false
                self.toMainMenuButton.isHidden = false
            case .onSomeoneLeft:
                self.startNewRoundButton.setTitle(self.textOfNewRoundButtonOnSomeoneLeft(), for: UIControl.State())
                self.startNewRoundButton.isHidden = false
                self.toMainMenuButton.isHidden = false
            case .nothing:
                self.startNewRoundButton.isHidden = true
                self.toMainMenuButton.isHidden = true
            }
        }
    }
    
    open var currentCardOfView:DGViewCard = .matchingPlayer {
        didSet {
            // 先停止,不然在闪的时候,再设置闪就会有问题
            self.screenTouchInforLabel.stopFlick()
            
            self.matchingPlayerView.isHidden = true
            self.roomView.isHidden = true
            self.guessDiceView.isHidden = true
            self.maniCountOfFactorView.isHidden = true
            self.someoneLeftView.isHidden = true
            
            switch self.currentCardOfView {
            case .matchingPlayer:
                self.matchingPlayerView.isHidden = false
            case .waitingAllPlayersReady4NextRound:
                self.roomView.isHidden = false
                self.roomView.waitingAllPlayersReady4NextRound()
            case .waitingNewChallenger:
                self.roomView.isHidden = false
                self.loadingIndicator.startAnimating()
                self.roomView.waitingNewChallenger()
            case .ready2ShakeDice:
                self.roomView.isHidden = false
                self.screenTouchInforLabel.startFlick()
            case .guessDice:
                self.roomView.isHidden = false
                self.guessDiceView.isHidden = false
            case .displayResult:
                self.roomView.isHidden = false
            case let .someoneLeft(messageOfLine1, messageOfLine2):
                self.someoneLeftView.isHidden = false
                self.nameOfSomeOneLabel.text = messageOfLine1
                self.reasonOfLeftLabel.text = messageOfLine2
            }
        }
    }
    
    fileprivate var myCards = [String:Int]() {
        didSet {
            guard let theUseCardButton = self.useCardButton else {
                return
            }
            var countOfAllMyCards = 0
            for (_, countOfType) in self.myCards {
                countOfAllMyCards = countOfAllMyCards + countOfType
            }
            theUseCardButton.setTitle("\(DGBundle.i18n(key: "Lucky_Card"))(\(countOfAllMyCards))", for: .normal)
        }
    }
    
    fileprivate var toastView:UIView!
    
    // MARK: - Override
    override open var prefersStatusBarHidden : Bool {
        return true
    }
    
    override open func viewDidLoad() {
        DGUIUtils.addMainBackgroundImageViewTo(parentView: self.view)
        
        let safeAreaView = UIView()
        self.view.addSubview(safeAreaView)
        safeAreaView.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            self.topConstraintOfSafeArea = make.top.equalTo(0).constraint
            make.right.equalTo(0)
            self.bottomConstraintOfSafeArea = make.bottom.equalTo(0).constraint
        }
        
        // matchingPlayerView
        self.matchingPlayerView = DGUIUtils.addTransparentBackgroundViewTo(parentView: safeAreaView)
        self.addSubviews2MatchingPlayerView(self.matchingPlayerView)
        
        // someoneLeftView
        self.someoneLeftView = DGUIUtils.addTransparentBackgroundViewTo(parentView: safeAreaView)
        self.addSubviews2SomeoneLeftView(self.someoneLeftView)
        
        // roomView
        self.roomView = DGRoomView(delegate: self)
        safeAreaView.addSubview(self.roomView)
        self.roomView.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.top.equalTo(0)
            make.bottom.equalTo(0)
        }
        
        let paddingAcrossingPlayerView = DGPlayerView.PREFERRED_HEIGHT + PADDING_AROUND_PLAYER_VIEW_2_EDGE * 2
        
        // guessDiceView
        self.guessDiceView = UIView()
        safeAreaView.addSubview(self.guessDiceView)
        self.guessDiceView.snp.makeConstraints { (make) in
            make.left.equalTo(PADDING_AROUND_PLAYER_VIEW_2_EDGE)
            make.right.equalTo(-PADDING_AROUND_PLAYER_VIEW_2_EDGE)
            make.bottom.equalTo(-paddingAcrossingPlayerView)
            make.height.equalTo(HEIGHT_OF_GUESS_DICE_VIEW)
        }
        self.addSubviews2GuessDiceView(self.guessDiceView)
        
        // maniCountOfFactorView
        self.maniCountOfFactorView = UIView()
        self.maniCountOfFactorView.isHidden = true
        safeAreaView.addSubview(self.maniCountOfFactorView)
        self.maniCountOfFactorView.snp.makeConstraints { (make) in
            make.left.equalTo(paddingAcrossingPlayerView)
            make.right.equalTo(-paddingAcrossingPlayerView)
            make.bottom.equalTo(self.guessDiceView.snp.top).offset(-PADDING_AROUND_PLAYER_VIEW_2_EDGE)
            make.height.equalTo(DGUIUtils.SIZE_OF_DICE * 2 + DGUIUtils.PADDING_BETWEEN_DICES * 3)
        }
        
        let sixFactorChoiceView = self.createFactorChoiceView()
        self.maniCountOfFactorView.addSubview(sixFactorChoiceView)
        sixFactorChoiceView.snp.makeConstraints { (make) in
            make.left.equalTo(self.maniCountOfFactorView.snp.centerX)
            make.right.equalTo(0)
            make.top.equalTo(0)
            make.bottom.equalTo(0)
        }
        
        let countChoiceView = self.createCountChoiceView()
        self.maniCountOfFactorView.addSubview(countChoiceView)
        countChoiceView.snp.makeConstraints { (make) in
            make.right.equalTo(self.maniCountOfFactorView.snp.centerX)
            make.left.equalTo(0)
            make.top.equalTo(0)
            make.bottom.equalTo(0)
        }
        
        // widgetsAlwaysShow
        let heightOfScreentTouchTipLabel:CGFloat = 20
        
        // start round view
        let widthOfButtonInStartRoundView:CGFloat = 100
        let heightOfButtonInStartRoundView:CGFloat = 40
        let paddingBetweenButtonsInStartRoundView:CGFloat = 60
        self.toMainMenuButton = DGUIUtils.createHomeButton(name: DGBundle.i18n(key:"End_Game"), target: self, action: #selector(DGGameViewController.btnEndGame))
        self.startNewRoundButton = DGUIUtils.createHomeButton(name: DGBundle.i18n(key:"New_Round"), target: self, action: #selector(DGGameViewController.actionOnStartNewRoundButton))
        safeAreaView.addSubview(self.toMainMenuButton)
        self.toMainMenuButton.snp.makeConstraints { (make) in
            make.width.equalTo(widthOfButtonInStartRoundView)
            make.height.equalTo(heightOfButtonInStartRoundView)
            make.centerX.equalTo(safeAreaView).offset(-(widthOfButtonInStartRoundView + paddingBetweenButtonsInStartRoundView)/2)
            make.bottom.equalTo(safeAreaView).offset(-paddingAcrossingPlayerView)
        }
        safeAreaView.addSubview(self.startNewRoundButton)
        self.startNewRoundButton.snp.makeConstraints { (make) in
            make.width.equalTo(widthOfButtonInStartRoundView)
            make.height.equalTo(heightOfButtonInStartRoundView)
            make.centerX.equalTo(safeAreaView).offset((widthOfButtonInStartRoundView + paddingBetweenButtonsInStartRoundView)/2)
            make.bottom.equalTo(safeAreaView).offset(-paddingAcrossingPlayerView)
        }
        
        self.screenTouchInforLabel = DGFlickLabel()
        safeAreaView.addSubview(self.screenTouchInforLabel)
        self.screenTouchInforLabel.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.bottom.equalTo(safeAreaView).offset(-paddingAcrossingPlayerView)
            make.right.equalTo(0)
            make.height.equalTo(heightOfScreentTouchTipLabel)
        }
        self.screenTouchInforLabel.text = DGBundle.i18n(key:"Touch_Screen_2_Shake_Dice")
        
        self.currentCardOfView = .matchingPlayer
        self.action4StartNewRound = .nothing
        
        super.viewDidLoad()
    }
    
    open override func viewDidAppear(_ animated: Bool) {
        super.viewDidAppear(animated)
        
        self.topConstraintOfSafeArea?.update(offset: self.topOfSafeArea())
        self.bottomConstraintOfSafeArea?.update(offset: -self.view.safeAreaInsets.bottom)
    }
    
    open func topOfSafeArea() -> CGFloat {
        return self.view.safeAreaInsets.top
    }
    
    open func addSubviews2MatchingPlayerView(_ matchingPlayerView:UIView) {        
        self.matchingPlayerInforLabel = DGUIUtils.createMiddleUILabel(initString: DGBundle.i18n(key:"Matching_Player"))
        matchingPlayerView.addSubview(self.matchingPlayerInforLabel)
        self.matchingPlayerInforLabel.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.height.equalTo(DGFonts.MIDDLE_FONT_SIZE)
            make.centerY.equalTo(matchingPlayerView.snp.centerY).offset(-100)
        }
        
        self.exitGameButton = DGUIUtils.createHomeButton(name: DGBundle.i18n(key:"Cancel"), target: self, action: #selector(DGGameViewController.btnEndGame))
        matchingPlayerView.addSubview(self.exitGameButton)
        self.exitGameButton.snp.makeConstraints { (make) in
            make.centerX.equalTo(matchingPlayerView)
            make.bottom.equalTo(-100)
            make.width.equalTo(100)
            make.height.equalTo(40)
        }
    }
    
    fileprivate func createCountChoiceView() -> UIView {
        let view = UIView()
        
        self.count2GuessLabel = DGUIUtils.createMiddleUILabel(initString: "\(self.count2Guess)")
        view.addSubview(self.count2GuessLabel)
        self.count2GuessLabel.snp.makeConstraints { (make) in
            make.center.equalTo(view)
            make.width.equalTo(self.count2GuessLabel.snp.height)
        }
        
        self.decreaseCountButton = DGUIUtils.createForegroundImageButton(imagePath: DGBundle.MINUS_IMAGE, target: self, action: #selector(DGGameViewController.decreaseCount2Guess))
        view.addSubview(self.decreaseCountButton)
        decreaseCountButton.snp.makeConstraints { (make) in
            make.width.height.equalTo(20)
            make.centerY.equalTo(view)
            make.right.equalTo(self.count2GuessLabel.snp.left).offset(-5)
        }
        
        self.increaseCountButton = DGUIUtils.createForegroundImageButton(imagePath: DGBundle.PLUS_IMAGE, target: self, action: #selector(DGGameViewController.increaseCount2Guess))
        view.addSubview(self.increaseCountButton)
        increaseCountButton.snp.makeConstraints { (make) in
            make.width.height.equalTo(20)
            make.centerY.equalTo(view)
            make.left.equalTo(self.count2GuessLabel.snp.right).offset(5)
        }
        
        return view
    }
    
    fileprivate func createFactorChoiceView() -> UIView {
        let view = UIView()
        
        self.factor1Button = UIButton()
        view.addSubview(self.factor1Button)
        self.factor1Button.setImage(DGUIUtils.getFlexiableDiceImage(), for: .normal)
        self.factor1Button.setBackgroundImage(UIImage(named: DGBundle.BACKGROUND_IMAGE_OF_SELECTED_DICE), for: .selected)
        self.factor1Button.snp.makeConstraints { (make) in
            make.width.height.equalTo(DGUIUtils.SIZE_OF_DICE)
            make.top.equalTo(DGUIUtils.PADDING_BETWEEN_DICES)
            make.left.equalTo(DGUIUtils.PADDING_BETWEEN_DICES)
        }
        self.factor1Button.addTarget(self, action: #selector(DGGameViewController.btnFactorButtonPressed), for: .touchUpInside)
        
        self.factor2Button = UIButton()
        view.addSubview(self.factor2Button)
        self.factor2Button.setImage(DGUIUtils.getFixedDiceImage(number: 2), for: .normal)
        self.factor2Button.setBackgroundImage(UIImage(named: DGBundle.BACKGROUND_IMAGE_OF_SELECTED_DICE), for: .selected)
        self.factor2Button.snp.makeConstraints { (make) in
            make.width.height.equalTo(DGUIUtils.SIZE_OF_DICE)
            make.top.equalTo(DGUIUtils.PADDING_BETWEEN_DICES)
            make.centerX.equalTo(view)
        }
        self.factor2Button.addTarget(self, action: #selector(DGGameViewController.btnFactorButtonPressed), for: .touchUpInside)
        
        self.factor3Button = UIButton()
        view.addSubview(self.factor3Button)
        self.factor3Button.setImage(DGUIUtils.getFixedDiceImage(number: 3), for: .normal)
        self.factor3Button.setBackgroundImage(UIImage(named: DGBundle.BACKGROUND_IMAGE_OF_SELECTED_DICE), for: .selected)
        self.factor3Button.snp.makeConstraints { (make) in
            make.width.height.equalTo(DGUIUtils.SIZE_OF_DICE)
            make.top.equalTo(DGUIUtils.PADDING_BETWEEN_DICES)
            make.right.equalTo(-DGUIUtils.PADDING_BETWEEN_DICES)
        }
        self.factor3Button.addTarget(self, action: #selector(DGGameViewController.btnFactorButtonPressed), for: .touchUpInside)
        
        self.factor4Button = UIButton()
        view.addSubview(self.factor4Button)
        self.factor4Button.setImage(DGUIUtils.getFixedDiceImage(number: 4), for: .normal)
        self.factor4Button.setBackgroundImage(UIImage(named: DGBundle.BACKGROUND_IMAGE_OF_SELECTED_DICE), for: .selected)
        self.factor4Button.snp.makeConstraints { (make) in
            make.width.height.equalTo(DGUIUtils.SIZE_OF_DICE)
            make.bottom.equalTo(-DGUIUtils.PADDING_BETWEEN_DICES)
            make.left.equalTo(DGUIUtils.PADDING_BETWEEN_DICES)
        }
        self.factor4Button.addTarget(self, action: #selector(DGGameViewController.btnFactorButtonPressed), for: .touchUpInside)

        self.factor5Button = UIButton()
        view.addSubview(self.factor5Button)
        self.factor5Button.setImage(DGUIUtils.getFixedDiceImage(number: 5), for: .normal)
        self.factor5Button.setBackgroundImage(UIImage(named: DGBundle.BACKGROUND_IMAGE_OF_SELECTED_DICE), for: .selected)
        self.factor5Button.snp.makeConstraints { (make) in
            make.width.height.equalTo(DGUIUtils.SIZE_OF_DICE)
            make.bottom.equalTo(-DGUIUtils.PADDING_BETWEEN_DICES)
            make.centerX.equalTo(view)
        }
        self.factor5Button.addTarget(self, action: #selector(DGGameViewController.btnFactorButtonPressed), for: .touchUpInside)

        self.factor6Button = UIButton()
        view.addSubview(self.factor6Button)
        self.factor6Button.setImage(DGUIUtils.getFixedDiceImage(number: 6), for: .normal)
        self.factor6Button.setBackgroundImage(UIImage(named: DGBundle.BACKGROUND_IMAGE_OF_SELECTED_DICE), for: .selected)
        self.factor6Button.snp.makeConstraints { (make) in
            make.width.height.equalTo(DGUIUtils.SIZE_OF_DICE)
            make.bottom.equalTo(-DGUIUtils.PADDING_BETWEEN_DICES)
            make.right.equalTo(-DGUIUtils.PADDING_BETWEEN_DICES)
        }
        self.factor6Button.addTarget(self, action: #selector(DGGameViewController.btnFactorButtonPressed), for: .touchUpInside)
        
        self.all6FactorButtons = [
            self.factor1Button,
            self.factor2Button,
            self.factor3Button,
            self.factor4Button,
            self.factor5Button,
            self.factor6Button
        ]

        return view
    }
    
    fileprivate func addSubviews2GuessDiceView(_ guessDiceView:UIView) {
        self.sendMyGuessButton = DGUIUtils.createBackgroundImageButton(imagePath: DGBundle.GREEN_BUTTON_IMAGE, target: self, action: #selector(DGGameViewController.btnSendMyGuess))
        self.sendMyGuessButton.setTitle(DGBundle.i18n(key:"Guess"), for:UIControl.State.normal)
        guessDiceView.addSubview(self.sendMyGuessButton)
        self.sendMyGuessButton.snp.makeConstraints { (make) in
            make.width.equalTo(guessDiceView.snp.width).multipliedBy(0.33).offset(-7)
            make.height.equalTo(self.sendMyGuessButton.snp.width).multipliedBy(45.0/122)
            make.centerX.equalTo(guessDiceView.snp.centerX)
            make.centerY.equalTo(guessDiceView.snp.centerY)
        }
        self.sendMyGuessButton.isEnabled = false
        
        self.pointOutLiarButton = DGUIUtils.createBackgroundImageButton(imagePath: DGBundle.RED_BUTTON_IMAGE, target: self, action: #selector(DGGameViewController.btnPointOutLiar))
        self.pointOutLiarButton.setTitle(DGBundle.i18n(key:"Doubt"), for:UIControl.State.normal)
        guessDiceView.addSubview(self.pointOutLiarButton)
        self.pointOutLiarButton.snp.makeConstraints { (make) in
            make.width.equalTo(self.sendMyGuessButton.snp.width)
            make.height.equalTo(self.sendMyGuessButton.snp.height)
            make.centerX.equalTo(guessDiceView.snp.centerX)
            make.left.equalTo(0)
            make.centerY.equalTo(guessDiceView.snp.centerY)
        }
        self.pointOutLiarButton.isEnabled = false
        
        self.useCardButton = DGUIUtils.createUIButton(titleOfButton: DGBundle.i18n(key:"Use_Lucky_Card"), target: self, action: #selector(DGGameViewController.useCard))
        guessDiceView.addSubview(self.useCardButton)
        self.useCardButton.snp.makeConstraints { (make) in
            make.width.equalTo(self.sendMyGuessButton.snp.width)
            make.height.equalTo(self.sendMyGuessButton.snp.height)
            make.right.equalTo(0)
            make.centerY.equalTo(guessDiceView.snp.centerY)
        }
    }
    
    fileprivate func addSubviews2SomeoneLeftView(_ someoneLeftView:UIView) {
        self.nameOfSomeOneLabel = DGUIUtils.createMiddleUILabel(initString: "")
        self.reasonOfLeftLabel = DGUIUtils.createUILabel(initString: "")
        
        someoneLeftView.addSubview(self.nameOfSomeOneLabel)
        self.nameOfSomeOneLabel.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.bottom.equalTo(someoneLeftView.snp.centerY).offset(-20)
            make.height.equalTo(DGFonts.MIDDLE_FONT_SIZE)
        }
        someoneLeftView.addSubview(self.reasonOfLeftLabel)
        self.reasonOfLeftLabel.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.top.equalTo(someoneLeftView.snp.centerY).offset(20)
            make.height.equalTo(DGFonts.NORMAL_FONT_SIZE)
        }
    }
    
    open func setTextOfMatchingPlayerInforLabel(_ text:String) {
        self.matchingPlayerInforLabel.text = text
    }
    
    open func textOfNewRoundButtonOnIWinRound() -> String {
        return DGBundle.i18n(key:"One_More")
    }
    
    open func textOfNewRoundButtonOnINotWinRound() -> String {
        return DGBundle.i18n(key:"One_More")
    }
    
    open func textOfNewRoundButtonOnSomeoneLeft() -> String {
        return DGBundle.i18n(key:"Match_New_Player")
    }
    
    open func action4StartNewRoundOnIWinRound() {
        self.actionOfScreenTouch2StartNewRound()
    }
    
    open func action4StartNewRoundOnINotWinRound() {
        self.actionOfScreenTouch2StartNewRound()
    }
    
    open func action4StartNewRoundOnSomeoneLeft() {
// todo
        if self.allPlayers.count == 2 {
            self.client.notifyServerOfQuickStart()
        } else {
            self.client.notifyServerOfQuickStartOf4()
        }
    }
    
    fileprivate func actionOfScreenTouch2StartNewRound() {
        self.currentCardOfView = .waitingAllPlayersReady4NextRound
        self.loadingIndicator.startAnimating()
        
        self.client.notifyServerIAmReady4NewRound()
    }
    
    // MARK: - UI Actions
    @objc func actionOnStartNewRoundButton() {
        switch self.action4StartNewRound {
        case .onIWinRound:
            self.action4StartNewRound = .nothing
            
            self.action4StartNewRoundOnIWinRound()
        case .onINotWinRound:
            self.action4StartNewRound = .nothing
            
            self.action4StartNewRoundOnINotWinRound()
        case .onSomeoneLeft:
            self.action4StartNewRound = .nothing
            
            self.action4StartNewRoundOnSomeoneLeft()
        case .nothing:
            break
        }
    }
    
    @objc func btnFactorButtonPressed(sender:UIButton) {
        self.setFactorButtonSelectedBy(factorButton: sender)
    }
    
    private func setFactorButtonSelectedBy(index:Int) {
        self.all6FactorButtons.forEach { (button) in
            button.isSelected = false
        }
        
        self.all6FactorButtons[index].isSelected = true
    }
    
    private func setFactorButtonSelectedBy(factorButton:UIButton) {
        self.all6FactorButtons.forEach { (button) in
            button.isSelected = false
        }
        
        factorButton.isSelected = true
    }
    
    @objc func decreaseCount2Guess() {
        self.count2Guess = self.count2Guess - 1
    }
    
    @objc func increaseCount2Guess() {
        self.count2Guess = self.count2Guess + 1
    }
    
    @objc func btnEndGame() {
        let alertController = UIAlertController(title: DGBundle.i18n(key:"End_Game"), message: DGBundle.i18n(key:"Are_You_Sure_2_Quit"), preferredStyle: UIAlertController.Style.alert)
        alertController.addAction(UIAlertAction(title:DGBundle.i18n(key:"Yes"), style:UIAlertAction.Style.default, handler: {
            (action) -> Void in
            self.client.notifyServerIWant2EndGame()
            self.dismiss(animated: true, completion: nil)
        }))
        alertController.addAction(UIAlertAction(title:DGBundle.i18n(key:"Cancel"), style:UIAlertAction.Style.cancel, handler:nil))
        
        self.present(alertController, animated: true, completion: nil)
    }
    
    @objc func toastTipOfOneState() {
        if !self.oneHasBeenGuessed {
            self.toastMessage(DGBundle.i18n(key:"1_Can_Be_Any_Point"), message: DGBundle.i18n(key:"1_Has_Not_Been_Guessed"))
        } else {
            self.toastMessage(DGBundle.i18n(key:"1_Can_Only_Be_1"), message: DGBundle.i18n(key:"1_Can_Only_Be_1_After_Been_Guessed_Once"))
        }
    }
    
    fileprivate func getPlayerInRoomByUUID(_ uuid:String) -> DGPlayer? {
        for player in self.allPlayers {
            if player.uuid == uuid {
                return player
            }
        }
        
        return nil
    }
    
    fileprivate func getPlayerNameInRoomByUUID(_ uuid:String) -> String {
        if self.myUUID() == uuid {
            return DGBundle.i18n(key:"Me")
        } else if let playerInRoom = self.getPlayerInRoomByUUID(uuid) {
            return playerInRoom.playerName
        }
        
        return uuid
    }
    
    func toastMessage(_ title:String, message:String) {
        if self.toastView != nil {
            return
        }
        
        let widthOfTitle = DGUIUtils.calculatePreferredWidth(title, fontOfButton: DGFonts.NORMAL_BUTTON_FONT)
        let widthOfMessage = DGUIUtils.calculatePreferredWidth(message, fontOfButton: DGFonts.NORMAL_BUTTON_FONT)
        let paddingOfToast:CGFloat = 5
        let verticalSpacingBetweenTitleAndMessage:CGFloat = 10
        let widthOfToast = max(widthOfTitle, widthOfMessage) + paddingOfToast*2
        let heightOfToast = paddingOfToast*2 + verticalSpacingBetweenTitleAndMessage + DGFonts.NORMAL_FONT_SIZE+DGFonts.NORMAL_FONT_SIZE
        
        self.toastView = UIView()
        self.view.addSubview(self.toastView)
        self.toastView.snp.makeConstraints { (make) in
            make.width.equalTo(widthOfToast)
            make.height.equalTo(heightOfToast)
            make.top.equalTo(self.view.safeAreaInsets.top)
            make.centerX.equalTo(self.view)
        }
        self.toastView.backgroundColor = UIColor(red: 0.2, green: 0.2, blue: 0.2, alpha: 0.75)
        self.toastView.layer.cornerRadius = 5.0
        self.toastView.layer.borderWidth = 1.0
        self.toastView.layer.borderColor = UIColor.gray.withAlphaComponent(0.5).cgColor
        
        let titleLabel = DGUIUtils.createUILabel(initString:title)
        self.toastView.addSubview(titleLabel)
        titleLabel.snp.makeConstraints { (make) in
            make.left.equalTo(paddingOfToast)
            make.top.equalTo(paddingOfToast)
            make.right.equalTo(paddingOfToast)
            make.height.equalTo(DGFonts.NORMAL_FONT_SIZE)
        }
        
        let messageLabel = DGUIUtils.createUILabel(initString:message)
        self.toastView.addSubview(messageLabel)
        messageLabel.snp.makeConstraints { (make) in
            make.left.equalTo(paddingOfToast)
            make.right.equalTo(paddingOfToast)
            make.top.equalTo(titleLabel.snp.bottom)
            make.height.equalTo(DGFonts.NORMAL_FONT_SIZE)
        }
        
        Timer.scheduledTimer(timeInterval: 4.0, target: self, selector: #selector(DGGameViewController.removeToastView), userInfo: nil, repeats: false)
    }
    
    @objc func removeToastView() {
        self.toastView.removeFromSuperview()
        self.toastView = nil
    }
    
    func goldModification(_ gold:Int) {
        if gold == 0 {
            return
        }
        let centerXOfMainView = self.view.bounds.width/2
        let centerYOfMainView = self.view.bounds.height/2
        
        let sizeOfImage:CGFloat = 30
        let widthOfGoldView:CGFloat = 60
        let heightOfGoldView:CGFloat = 50
        
        let goldView = UIView(frame:CGRect(x: centerXOfMainView-widthOfGoldView/2, y: centerYOfMainView-heightOfGoldView/2, width: widthOfGoldView, height: heightOfGoldView))
        self.view.addSubview(goldView)
        
        let goldImage = UIImageView(image: UIImage(named: DGBundle.GOLD_IMAGE))
        goldImage.frame = CGRect(x: 0, y: (heightOfGoldView-sizeOfImage)/2, width: sizeOfImage, height: sizeOfImage)
        goldView.addSubview(goldImage)
        
        let scoreLabel = UILabel(frame:CGRect(x: sizeOfImage,y: 0,width: widthOfGoldView-sizeOfImage,height: heightOfGoldView))
        goldView.addSubview(scoreLabel)
        scoreLabel.text = "\(gold)"
        if gold > 0 {
            scoreLabel.textColor = UIColor.white
        } else {
            scoreLabel.textColor = UIColor.black
        }
        scoreLabel.textAlignment = NSTextAlignment.center
        
        goldView.alpha = 0.5
        UIView.animate(withDuration: 2, animations: { () -> Void in
            goldView.alpha = 1
            goldView.center = CGPoint(x: centerXOfMainView, y: centerYOfMainView-50)
            }, completion: { (finished) -> Void in
                if finished {
                    UIView.animate(withDuration: 2, animations: { () -> Void in
                        goldView.alpha = 0
                        }, completion: { (finished) -> Void in
                            goldView.removeFromSuperview()
                    })
                }
        }) 
    }
    
    // MARK: - DGRoomViewDelegate
    open func myUUID() -> String {
        return self.client.playerUUID
    }
    
    open func positionOfUUID(_ uuid: String) -> DGRoomViewPosition {
        if self.myUUID() == uuid {
            return .me
        }
        
        if self.allPlayers.count == 2 {
            return .up
        }
        
        guard let indexOfMe = self.orderOfPlayer(self.client.playerUUID) else {
            fatalError("i am not a player")
        }
        guard let indexOfTarget = self.orderOfPlayer(uuid) else {
            fatalError("target:\(uuid) not a player")
        }
        
        if indexOfMe == indexOfTarget {
            return .me
        } else if (indexOfMe + 1) % 4 == indexOfTarget {
            return .right
        } else if (indexOfMe + 2) % 4 == indexOfTarget {
            return .up
        } else {
            return .left
        }
    }
    
    fileprivate func orderOfPlayer(_ uuid:String) -> Int? {
        var currentIndex = 0
        for p in self.allPlayers {
            if p.uuid == uuid {
                return currentIndex
            }
            
            currentIndex += 1
        }
        
        return nil
    }
    
    open func ready2Shake() {
        self.currentCardOfView = .ready2ShakeDice
        
        self.roomView.resetReady2ShakeDiceView()
    }

    open func ready2Guess() {
        self.resetReady2GuessDice()
        self.currentCardOfView = .guessDice
        
        self.client.notifyServerIHaveShakedDice()
    }
    
    open func afterResultDisplayAnimation(_ amIWinner:Bool) {
        if amIWinner {
            self.modifyAction4StartNewRoundOnIWin()
        } else {
            self.modifyAction4StartNewRoundOnINotWin()
        }
    }
    
    // MARK: - DGActionsOnMessageReceivedFromServer
    open func beNotifiedOfIGotNewCards(_ cardsGot:[String:Int], gold:Int, forReason:String) {
        var messages = [String]()
        if gold > 0 {
            messages.append("\(gold)\(DGBundle.i18n(key:"Gold"))")
        }
        for (nameOfCard, countOfCard) in cardsGot {
            if let countOfCardIAlreadyGot = self.myCards[nameOfCard] {
                self.myCards[nameOfCard] = countOfCardIAlreadyGot + countOfCard
            } else {
                self.myCards[nameOfCard] = countOfCard
            }
            
            messages.append("\(CARD_NAME_DESCRIPTION(nameOfCard))\(countOfCard)")
        }
        
        let message = messages.joined(separator: ";")
        
        self.toastMessage(forReason, message: message)
        
        if gold != 0 {
            self.goldModification(gold)
        }
    }
    
    open func beNotifiedOfRoomIDNotAvailable(_ roomID:String) {
        self.simpleAlert(DGBundle.i18n(key:"Unavailable"), message: "\(DGBundle.i18n(key:"Specified_Room")) \(roomID) \(DGBundle.i18n(key:"Not_Accessable"))") { (action) -> Void in
            self.dismiss(animated: true, completion: nil)
        }
    }

    open func beNotifiedOfMyRoomID(_ roomID: String) {
        // do nothing
    }
    
    open func beNotified2StartRound(_ roundIndex: Int, myCards: [String : Int], playersInRoom: [DGPlayer]) {
        self.currentCardOfView = .waitingAllPlayersReady4NextRound
        
        self.allPlayers = playersInRoom
        self.myCards = myCards
        self.oneHasBeenGuessed = false
        
        self.count2Guess = self.allPlayers.count
        self.setFactorButtonSelectedBy(index: 0)

        self.loadingIndicator.stopAnimating()

        self.roomView.playRoundAnimation(roundIndex)
    }
    
    open func beNotifiedOfCardUsed(_ typeOfCard:String, sourceUUID:String, targetUUID:[String]) {
        if targetUUID.contains(self.client.playerUUID) {
            switch typeOfCard {
            case CARD_NAME_RESHAKE:
                self.roomView.dicesITossed = DGGameRules.randomDicesTossed()
            default:
                break
            }
        } else {
            print("\(sourceUUID) \(DGBundle.i18n(key:"Used_Card_But_I_Am_Not_The_Target"))")
        }
        
        if sourceUUID == self.client.playerUUID {
            self.myCards[typeOfCard] = self.myCards[typeOfCard]! - 1
        }
    }
    
    open func beNotifiedOfMyCard2UseNotAvailable(_ message: String) {
    }
    
    open func beNotifiedOfOneClientHasShakedDice(_ playerUUID:String) {
        if playerUUID != self.myUUID() {
            self.roomView.setDiceByUUID(playerUUID, dices: FIVE_UNKNOW_DICES, byAnimation: false)
        }
    }
    
    open func beNotifiedOfOneClient2Guess(_ playerUUID:String) {
        if self.myUUID() == playerUUID {
            self.sendMyGuessButton.isEnabled = true
            self.maniCountOfFactorView.isHidden = false
        } else {
            self.sendMyGuessButton.isEnabled = false
            self.maniCountOfFactorView.isHidden = true
        }
        
        self.roomView.startTimerOfUUID(playerUUID)
    }
    
    open func beNotifiedOfNotMyTurn2Guess() {
        self.simpleAlert(DGBundle.i18n(key:"Wrong_Order"), message: DGBundle.i18n(key:"Not_My_Ture_2_Guess"), handler:nil)
    }
    
    open func beNotifiedOfNotTime2PointOutLiar() {
        self.simpleAlert(DGBundle.i18n(key:"Wrong_Order"), message: DGBundle.i18n(key:"You_Can_Not_Point_Out_Liar_Now"), handler:nil)
    }
    
    open func beNotifiedOfMyLastGuessIsInvalid(_ invalidMessage:String) {
        // 注意Send Guess可能是不合法的,所以在被告知自己的Guess不合法时,这两个Button要重新enable
        self.pointOutLiarButton.isEnabled = true
        self.sendMyGuessButton.isEnabled = true
        
        self.simpleAlert(DGBundle.i18n(key:"Illegal_Guess"), message: invalidMessage, handler:nil)
    }
    open
    func beNotifiedOfGuessByPlayer(_ guess:DGGuess, playerUUID:String, nextPlayerUUID:String) {
        if guess.factor == 1 {
            self.oneHasBeenGuessed = true
        }
        
        let isMyGuess = (self.myUUID() == playerUUID)
        self.pointOutLiarButton.isEnabled = (!isMyGuess)
        
        self.count2Guess = guess.count
        self.setFactorButtonSelectedBy(index: guess.factor - 1)
        
        self.roomView.showGuessActionByUUID(playerUUID, guess: guess)
        self.roomView.addGuessHistoryElement(DGGuessHistoryElement(guess: guess, uuidOfGuesser: playerUUID, isMyself: isMyGuess))
        self.roomView.stopTimerOfUUID(playerUUID)
        self.beNotifiedOfOneClient2Guess(nextPlayerUUID)
    }
    
    open func beNotified2OpenCup(_ uuidOfNotBelieveGuy: String) {
        self.roomView.showNotBelieveActionByUUID(uuidOfNotBelieveGuy)
        self.roomView.stopTimerOfUUID(uuidOfNotBelieveGuy)
        
        self.roundOver()
        
        self.client.notifyServerMyDicesShaked(self.roomView.dicesITossed)
    }
    
    open func beNotifiedOfRoundResult(_ result:[DGPlayerDicesTossedAndRoundResult]) {
        self.currentCardOfView = .displayResult
        self.roomView.displayRoundResult(result)
    }
    
    open func beNotifiedOfOneClientIsReady4NewRound(_ playerUUID: String) {
        self.roomView.setTagAsReadyByUUID(playerUUID)
    }
    
    open func beNotified2EndGameOfServerCrashed() {
        self.simpleAlert("GameOver", message: DGBundle.i18n(key:"Server_Crashed"), handler: {
            (action) -> Void in
            self.dismiss(animated: true, completion: nil)
        })
    }
    
    open func beNotified2EndGameOfSomeoneAsk2ExitGame(_ playerUUID:String) {
        if self.myUUID() == playerUUID {
            self.dismiss(animated: true, completion: nil)
        } else {
            self.currentCardOfView = .someoneLeft(messageOfLine1: self.getPlayerNameInRoomByUUID(playerUUID), messageOfLine2: DGBundle.i18n(key:"Ask_2_Quit"))
            self.roundInterruptedBecauseOfUUID(playerUUID)
        }
    }
    
    open func beNotified2EndGameOfSomeoneLostConnectionFromServer(_ playerUUID:String) {
        if self.myUUID() == playerUUID {
            self.dismiss(animated: true, completion: nil)
        } else {
            self.currentCardOfView = .someoneLeft(messageOfLine1: self.getPlayerNameInRoomByUUID(playerUUID), messageOfLine2: DGBundle.i18n(key:"Lost_Connection"))
            self.roundInterruptedBecauseOfUUID(playerUUID)
        }
    }
    
    fileprivate func roundInterruptedBecauseOfUUID(_ uuid:String) {
        self.roundOver()
        Timer.scheduledTimer(timeInterval: 1, target: self, selector: #selector(DGGameViewController.modifyAction4StartNewRoundOnSomeoneLeft), userInfo: nil, repeats: false)
    }
    
    fileprivate func roundOver() {
        self.roomView.stopAllTimer()
    }
    
    func simpleAlert(_ title:String, message:String, handler:((UIAlertAction?) -> Void)!) {
        let alertController = UIAlertController(title: title, message: message, preferredStyle: UIAlertController.Style.alert)
        alertController.addAction(UIAlertAction(title:DGBundle.i18n(key:"Yes"), style:UIAlertAction.Style.cancel, handler:handler))
        self.present(alertController, animated: true, completion: nil)
    }
}

// MARK: - Ready2GuessDice
extension DGGameViewController {
    
    @objc func btnSendMyGuess() {
        // 注意Send Guess可能是不合法的,所以在被告知自己的Guess不合法时,这两个Button要重新enable
        self.pointOutLiarButton.isEnabled = false
        self.sendMyGuessButton.isEnabled = false
        
        self.client.notifyServerMyGuess(self.countOfFactorSelected2Guess())
    }
    
    @objc func btnPointOutLiar() {
        self.pointOutLiarButton.isEnabled = false
        self.sendMyGuessButton.isEnabled = false
 
        self.client.notifyServerIDoNotBelieve()
    }
    
    @objc func useCard() {
        self.client.notifyServerOfTry2UseCard(CARD_NAME_RESHAKE)
    }
    
    fileprivate func countOfFactorSelected2Guess() -> DGGuess {
        var factor:Int = 1
        
        for i in 0 ..< self.all6FactorButtons.count {
            if self.all6FactorButtons[i].isSelected {
                factor = i + 1
                break
            }
        }
        
        return DGGuess(count: self.count2Guess, factor: factor)
    }
    
    fileprivate func resetReady2GuessDice() {
        self.sendMyGuessButton.isEnabled = false
        self.pointOutLiarButton.isEnabled = false
    }
}

// MARK: - Display Round Result
extension DGGameViewController {
    open override func touchesBegan(_ touches: Set<UITouch>, with event: UIEvent?) {
        switch self.currentCardOfView {
        case .ready2ShakeDice:
            if !self.roomView.isShaking {
                self.screenTouchInforLabel.stopFlick()
                self.roomView.startShake()
            }
        default:
            break
        }
    }
    
    @objc func modifyAction4StartNewRoundOnSomeoneLeft() {
        self.action4StartNewRound = .onSomeoneLeft
    }
    
    func modifyAction4StartNewRoundOnIWin() {
        self.action4StartNewRound = .onIWinRound
    }
    
    func modifyAction4StartNewRoundOnINotWin() {
        self.action4StartNewRound = .onINotWinRound
    }
}

public enum DGRoomViewPosition {
    case me, up, left, right
}

public protocol DGRoomViewDelegate {
    func myUUID() -> String
    func positionOfUUID(_ uuid:String) -> DGRoomViewPosition
    
    func ready2Shake()
    func ready2Guess()
    func afterResultDisplayAnimation(_ amIWinner:Bool)
}

private let PADDING_AROUND_PLAYER_VIEW_2_EDGE:CGFloat = 10
private let HEIGHT_OF_GUESS_DICE_VIEW:CGFloat = 40

private class DGRoomView:UIView {
    fileprivate var delegate:DGRoomViewDelegate
    
    fileprivate var layerView4PlayersAndDices:UIView
    fileprivate var mapOfAllPlayerViews = [String:DGPlayerView]()
    
    fileprivate let countingLabel:UILabel
    
    fileprivate var isShaking:Bool = false
    fileprivate var shakeDiceCup:UIImageView
    
    fileprivate var roundInforLabel: UILabel
    
    fileprivate let pointerImageView:UIImageView
    fileprivate let historyGuessView:DGGuessView
    fileprivate let tellLiarLabel:UILabel
    
    fileprivate var dicesITossed = [Int]() {
        didSet {
            self.setDiceByUUID(self.delegate.myUUID(), dices: self.dicesITossed, byAnimation: false)
        }
    }
    
    init(delegate:DGRoomViewDelegate) {
        self.delegate = delegate
        
        self.layerView4PlayersAndDices = UIView()
        
        self.countingLabel = DGUIUtils.createMiddleUILabel(initString: "0")
        self.countingLabel.isHidden = true
        
        let sizeOfDiceCup:CGFloat = 150
        self.shakeDiceCup = DGUIUtils.createImageView(imagePath: DGBundle.DICE_CUP_IMAGE)
        self.roundInforLabel = DGUIUtils.createMiddleUILabel(initString: "")
        self.roundInforLabel.isHidden = true
        
        self.pointerImageView = DGUIUtils.createImageView(imagePath: DGBundle.POINTER_IAMGE)
        self.pointerImageView.isHidden = true
        self.historyGuessView = DGGuessView()
        self.historyGuessView.isHidden = true
        self.tellLiarLabel = DGUIUtils.createUILabel(initString: DGBundle.i18n(key:"I_Do_Not_Believe"))
        self.tellLiarLabel.isHidden = true
        
        super.init(frame:CGRect.zero)
        
        self.addSubview(self.layerView4PlayersAndDices)
        self.layerView4PlayersAndDices.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.top.equalTo(0)
            make.bottom.equalTo(0)
        }
        
        self.addSubview(self.countingLabel)
        self.countingLabel.snp.makeConstraints { (make) in
            make.center.equalTo(self)
            make.width.height.equalTo(DGFonts.MIDDLE_FONT_SIZE)
        }
        
        self.addSubview(self.shakeDiceCup)
        self.shakeDiceCup.snp.makeConstraints { (make) in
            make.width.equalTo(sizeOfDiceCup)
            make.height.equalTo(sizeOfDiceCup)
            make.center.equalTo(self)
        }
        
        self.addSubview(self.pointerImageView)
        self.pointerImageView.snp.makeConstraints { (make) in
            make.center.equalTo(self)
            make.height.equalTo(70)
            make.width.equalTo(70)
        }
        
        self.addSubview(self.historyGuessView)
        self.historyGuessView.snp.makeConstraints { (make) in
            make.width.equalTo(DGGuessView.PREFERRED_WIDTH)
            make.height.equalTo(DGGuessView.PREFERRED_HEIGHT)
            make.center.equalTo(self)
        }
        self.addSubview(self.tellLiarLabel)
        self.tellLiarLabel.snp.makeConstraints { (make) in
            make.width.equalTo(DGGuessView.PREFERRED_WIDTH)
            make.height.equalTo(DGGuessView.PREFERRED_HEIGHT)
            make.center.equalTo(self)
        }
        
        self.addSubview(self.roundInforLabel)
        self.roundInforLabel.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.bottom.equalTo(0)
            make.height.equalTo(DGFonts.MIDDLE_FONT_SIZE)
        }
    }

    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    fileprivate func waitingAllPlayersReady4NextRound() {
        self.historyOfGuessMessage.removeAll()
        self.countingLabel.isHidden = true
        self.historyGuessView.isHidden = true
        self.tellLiarLabel.isHidden = true
    }
    
    fileprivate func waitingNewChallenger() {
        self.mapOfAllPlayerViews.forEach { (uuid, pview) in
            if uuid != self.delegate.myUUID() {
                pview.removeFromSuperview()
                self.mapOfAllPlayerViews.removeValue(forKey: uuid)
            }
        }
        
        self.historyOfGuessMessage.removeAll()
        self.countingLabel.isHidden = true
    }
    
    // MARK: - RoomView.History Of Guess
    fileprivate var historyOfGuessMessage = [DGGuessHistoryElement]()
    
    fileprivate func isHistoryOfGuessEmpty() -> Bool {
        return self.historyOfGuessMessage.count == 0
    }

    fileprivate func addGuessHistoryElement(_ historyEl:DGGuessHistoryElement) {
        self.historyOfGuessMessage.append(historyEl)
    }
    
    fileprivate func lastGuessHistoryElement() -> DGGuessHistoryElement? {
        return self.historyOfGuessMessage.last
    }
    
    // MARK: - RoomView.Action By UUID
    fileprivate func getMyPlayerView() -> DGPlayerView? {
        return self.mapOfAllPlayerViews[self.delegate.myUUID()]
    }
    
    fileprivate func getDiceViewOfUUIDByIndices(_ targetUUID:String, indices:[Int]) -> [UIImageView] {
        guard let thePlayerView = self.mapOfAllPlayerViews[targetUUID] else {
            fatalError("uuid not exist")
        }
        
        return thePlayerView.getDiceViewsByIndices(indices)
    }
    
    fileprivate func setDiceByUUID(_ targetUUID:String, dices:[Int], byAnimation:Bool) {
        if let thePlayerView = self.mapOfAllPlayerViews[targetUUID] {
            thePlayerView.setDices(dices, animation: byAnimation)
        }
    }
    
    fileprivate func moveCrownFrom(loser:DGPlayerDicesTossedAndRoundResult, toWinner winner:DGPlayerDicesTossedAndRoundResult) {
        if let theLoserView = self.mapOfAllPlayerViews[loser.playerUUID] {
            if let theWinnerView = self.mapOfAllPlayerViews[winner.playerUUID] {
                theLoserView.modifyCountOfCrown(loser.crownModification)
                
                let startRectOfCrown = theLoserView.getFrameOfCrownTo(parentView: self)
                let endRectOfCrown = theWinnerView.getFrameOfCrownTo(parentView: self)
                
                let tempCrownImageView = UIImageView(image: UIImage(named: DGBundle.CROWN_IMAGE)!)
                tempCrownImageView.frame = startRectOfCrown
                
                self.addSubview(tempCrownImageView)
                
                UIView.animate(withDuration: 2, animations: {
                    tempCrownImageView.center = CGPoint(x: self.frame.width / 2, y: self.frame.height / 2)
                    tempCrownImageView.transform = CGAffineTransform(scaleX: 5, y: 5)
                }) { (success) in
                    UIView.animate(withDuration: 1, animations: {
                        tempCrownImageView.frame = endRectOfCrown
                        tempCrownImageView.transform = CGAffineTransform(scaleX: 1, y: 1)
                    }, completion: { (success) in
                        tempCrownImageView.removeFromSuperview()
                    })
                    
                    theWinnerView.modifyCountOfCrown(winner.crownModification)
                }
            }
        }
    }
    
    fileprivate func showNotBelieveActionByUUID(_ uuidOfPlayer:String) {
        self.placeActionView(uuidOfPlayer: uuidOfPlayer, actionView: self.tellLiarLabel)
    }
    
    fileprivate func showGuessActionByUUID(_ uuidOfPlayer:String, guess:DGGuess) {
        self.historyGuessView.setGuess(guess)
        self.placeActionView(uuidOfPlayer: uuidOfPlayer, actionView: self.historyGuessView)
    }
    
    private func placeActionView(uuidOfPlayer:String, actionView:UIView) {
        let attachFrame = self.pointerImageView.frame
        let attachTop = attachFrame.origin.y
        let attachBottom = attachFrame.size.height + attachTop
        let attachLeft = attachFrame.origin.x
        let attachRight = attachFrame.size.width + attachLeft
        let attachCenterX = attachLeft + attachFrame.size.width / 2
        let attachCenterY = attachTop + attachFrame.size.height / 2
        
        let shortAsHeight = min(actionView.frame.size.height, actionView.frame.size.width)
        
        switch self.delegate.positionOfUUID(uuidOfPlayer) {
        case .left:
            actionView.snp.remakeConstraints{ (make) in
                make.center.equalTo(CGPoint(x: attachLeft - shortAsHeight, y: attachCenterY))
                make.width.equalTo(DGGuessView.PREFERRED_WIDTH)
                make.height.equalTo(DGGuessView.PREFERRED_HEIGHT)
            }
            actionView.transform = CGAffineTransform(rotationAngle: CGFloat(Double.pi / 2))
            break
        case .right:
            actionView.snp.remakeConstraints { (make) in
                make.center.equalTo(CGPoint(x: attachRight + shortAsHeight, y: attachCenterY))
                make.width.equalTo(DGGuessView.PREFERRED_WIDTH)
                make.height.equalTo(DGGuessView.PREFERRED_HEIGHT)
            }
            actionView.transform = CGAffineTransform(rotationAngle: -CGFloat(Double.pi / 2))
            break
        case .up:
            actionView.snp.remakeConstraints { (make) in
                make.center.equalTo(CGPoint(x: attachCenterX, y: attachTop - shortAsHeight))
                make.width.equalTo(DGGuessView.PREFERRED_WIDTH)
                make.height.equalTo(DGGuessView.PREFERRED_HEIGHT)
            }
            actionView.transform = CGAffineTransform(rotationAngle: 0)
            break
        case .me:
            actionView.snp.remakeConstraints { (make) in
                make.center.equalTo(CGPoint(x: attachCenterX, y: attachBottom + shortAsHeight))
                make.width.equalTo(DGGuessView.PREFERRED_WIDTH)
                make.height.equalTo(DGGuessView.PREFERRED_HEIGHT)
            }
            actionView.transform = CGAffineTransform(rotationAngle: 0)
            break
        }
        
        actionView.isHidden = false
        actionView.hideAndPopup()
    }
    
    fileprivate func setTagAsReadyByUUID(_ uuidOfPlayer:String) {
        guard let actionPlayerView = self.mapOfAllPlayerViews[uuidOfPlayer] else {return}
        
        actionPlayerView.showReady()
    }
    
    fileprivate func resetRoomWithPlayers(_ players:[DGPlayer]) {
        self.layerView4PlayersAndDices.subviews.forEach { (subview) in
            subview.removeFromSuperview()
        }
        self.mapOfAllPlayerViews.removeAll()
        
        let sizeOfAllPlayerView = self.bounds.size
        
        let heightOfPlayerView:CGFloat = DGPlayerView.PREFERRED_HEIGHT
        let widthOfPlayerView = sizeOfAllPlayerView.width - PADDING_AROUND_PLAYER_VIEW_2_EDGE * 2
        
        players.forEach { (p) in
            let centerXOfPlayerView:CGFloat
            let centerYOfPlayerView:CGFloat
            var rotate:CGFloat = 0
            var below4ActionUIView = true
            
            switch self.delegate.positionOfUUID(p.uuid) {
            case .left:
                centerXOfPlayerView = PADDING_AROUND_PLAYER_VIEW_2_EDGE + heightOfPlayerView/2
                centerYOfPlayerView = sizeOfAllPlayerView.height/2
                rotate = CGFloat(-Double.pi / 2)
            case .right:
                centerXOfPlayerView = sizeOfAllPlayerView.width - heightOfPlayerView/2 - PADDING_AROUND_PLAYER_VIEW_2_EDGE
                centerYOfPlayerView = sizeOfAllPlayerView.height/2
                rotate = CGFloat(Double.pi / 2)
            case .up:
                centerXOfPlayerView = sizeOfAllPlayerView.width/2
                centerYOfPlayerView = PADDING_AROUND_PLAYER_VIEW_2_EDGE + heightOfPlayerView/2
            case .me:
                centerXOfPlayerView = sizeOfAllPlayerView.width/2
                centerYOfPlayerView = sizeOfAllPlayerView.height - PADDING_AROUND_PLAYER_VIEW_2_EDGE - heightOfPlayerView/2
                below4ActionUIView = false
            }
            
            let newView = DGPlayerView(nickname: p.playerName, figure: p.figure, countOfCrown: p.countOfAllCrowns, below4ActionUIView: below4ActionUIView)
            self.layerView4PlayersAndDices.addSubview(newView)
            newView.snp.makeConstraints({ (make) in
                make.centerX.equalTo(centerXOfPlayerView)
                make.centerY.equalTo(centerYOfPlayerView)
                make.width.equalTo(widthOfPlayerView)
                make.height.equalTo(heightOfPlayerView)
            })
            
            newView.transform = newView.transform.rotated(by: rotate)

            self.mapOfAllPlayerViews[p.uuid] = newView
        }
    }
    
    /*
    private func setScoreOfPlayerUUID(uuid:String, score:Int) {
        if let view = self.mapOfAllScoreViews[uuid] {
            view.score = score
        }
    }
 */
 
    // MARK: - RoomView.Play Round Information
    fileprivate func playRoundAnimation(_ roundIndex:Int) {
        let boundsOfView = self.bounds
        let heightOfView = boundsOfView.height
        let widthOfView = boundsOfView.width
        
        self.roundInforLabel.center = CGPoint(x: widthOfView / 2, y: -heightOfView / 2)
        self.roundInforLabel.isHidden = false
        self.roundInforLabel.text = "Round \(roundIndex)"
        
        self.playSound(DGSound.readyGo)
        
        UIView.animate(withDuration: 0.5, animations: {
            self.roundInforLabel.center = CGPoint(x: widthOfView / 2, y: heightOfView / 2)
            }, completion: { (finished:Bool) -> Void in
                UIView.animate(withDuration: 1, delay: 1.5, options: UIView.AnimationOptions(), animations: { () -> Void in
                    self.roundInforLabel.alpha = 0
                    self.roundInforLabel.transform = CGAffineTransform(scaleX: 10, y: 10)
                    }, completion: { (finished:Bool) -> Void in
                        self.delegate.ready2Shake()
                        
                        self.roundInforLabel.alpha = 1
                        self.roundInforLabel.isHidden = true
                        self.roundInforLabel.transform = CGAffineTransform(scaleX: 1, y: 1)
                })
        })
    }
    
    // MARK: - RoomView.Ready 2 Shake Dice
    fileprivate func highlightDiceViewAsTargetDice(_ diceView:UIImageView) {
        diceView.layer.borderColor = UIColor.red.cgColor
    }
    
    fileprivate func startCenterOfCup() -> CGPoint {
        return self.center
    }
    
    fileprivate func resetReady2ShakeDiceView() {
        self.shakeDiceCup.transform = CGAffineTransform(translationX: 0, y: 0).scaledBy(x: 1, y: 1).rotated(by: 0)
        self.shakeDiceCup.center = self.startCenterOfCup()
    }
    
    // MARK: - RoomView.Shake Animation
    fileprivate func startShake() {
        self.isShaking = true
        self.shakeUpCup(true, timesLeft: 15)
        self.playSound(DGSound.dice)
    }
    
    fileprivate func shakeUpCup(_ isLeftDirection:Bool, timesLeft:Int) {
        if timesLeft <= 0 {
            UIView.animate(withDuration: 0.05, animations: { () -> Void in
                self.shakeDiceCup.transform = CGAffineTransform(rotationAngle: 0)
                }, completion: { (finished) -> Void in
                    self.stopSoundPlayer()
                    UIView.animate(withDuration: 0.2, animations: { () -> Void in
                        self.shakeDiceCup.center = self.startCenterOfCup()
                        }, completion: { (finished) -> Void in
                            self.playSound(.knock)
                            self.endShake()
                    })
            })
        } else {
            UIView.animate(withDuration: 0.1, animations: { () -> Void in
                let centerOfDiceCup = self.shakeDiceCup.center
                self.shakeDiceCup.center = CGPoint(x: centerOfDiceCup.x, y: centerOfDiceCup.y - 2)
                self.shakeDiceCup.transform = CGAffineTransform(rotationAngle: CGFloat(isLeftDirection ? Double.pi/8 : -Double.pi/8))
                }, completion: { (finished) -> Void in
                    self.shakeUpCup(!isLeftDirection, timesLeft: timesLeft - 1)
            })
        }
    }
    
    fileprivate func endShake() {
        let myDicesTossed = DGGameRules.randomDicesTossed()
        var tempDiceImageViews = [UIImageView]()
        myDicesTossed.forEach { (numberOfDice) in
            let diceView = UIImageView(image: DGUIUtils.getFixedDiceImage(number: numberOfDice))
            tempDiceImageViews.append(diceView)
            self.addSubview(diceView)
            diceView.frame = CGRect(
                x: self.frame.size.width / 2 - DGUIUtils.SIZE_OF_DICE / 2,
                y: self.frame.size.height / 2 - DGUIUtils.SIZE_OF_DICE / 2,
                width: DGUIUtils.SIZE_OF_DICE,
                height: DGUIUtils.SIZE_OF_DICE)
        }
        
        self.bringSubviewToFront(self.shakeDiceCup)
        
        UIView.animate(withDuration: 2, delay: 0.5, options: UIView.AnimationOptions(), animations: { () -> Void in
            let widthOfMainView = self.frame.width
            self.shakeDiceCup.transform = CGAffineTransform(translationX: widthOfMainView, y: -widthOfMainView).scaledBy(x: 0.5, y: 0.5).rotated(by: CGFloat(Double.pi / 2))
            
            
            let myPlayerView = self.getMyPlayerView()!
            let centerOfFiveDices = myPlayerView.getCenterOfFiveDices()
            for vi in 1 ... tempDiceImageViews.count {
                tempDiceImageViews[vi - 1].center = myPlayerView.convert(centerOfFiveDices[vi - 1], to: self)
            }
        }) { (finished) -> Void in
            self.dicesITossed = myDicesTossed
            
            tempDiceImageViews.forEach({ (v) in
                v.removeFromSuperview()
            })

            self.delegate.ready2Guess()
            
            self.isShaking = false
        }
    }
    
    // MARK: - RoomView.Count Down
    fileprivate func startTimerOfUUID(_ uuid:String) {
        let rotation:CGFloat
        switch self.delegate.positionOfUUID(uuid) {
        case .left:
            rotation = -CGFloat(Double.pi / 2)
        case .right:
            rotation = CGFloat(Double.pi / 2)
        case .up:
            rotation = 0
        case .me:
            rotation = -CGFloat(Double.pi)
        }
        
        self.pointerImageView.transform = CGAffineTransform(rotationAngle: rotation)
        self.pointerImageView.isHidden = false
        
        if let view = self.mapOfAllPlayerViews[uuid] {
            view.startCountDown()
        }
    }
    
    fileprivate func stopTimerOfUUID(_ uuid:String) {
        self.pointerImageView.isHidden = true
        
        if let view = self.mapOfAllPlayerViews[uuid] {
            view.stopCountDown()
        }
    }
    
    fileprivate func stopAllTimer() {
        for (_, view) in self.mapOfAllPlayerViews {
            view.stopCountDown()
        }
    }
    
    // MARK: - Audio Player
    fileprivate var currentAudioPlayer:AVAudioPlayer!
    
    fileprivate func playSound(_ sound:DGSound) {
        //        let soundFilePath = NSBundle.mainBundle().pathForResource(sound.soundName(), ofType: "m4r")
        //
        //        try! self.currentAudioPlayer = AVAudioPlayer(contentsOfURL: NSURL(fileURLWithPath: soundFilePath!), fileTypeHint:nil)
        //
        //        self.currentAudioPlayer.currentTime = 0
        //        self.currentAudioPlayer.play()
    }
    
    fileprivate func stopSoundPlayer() {
        if self.currentAudioPlayer != nil {
            self.currentAudioPlayer.stop()
        }
    }
    
    fileprivate enum DGSound {
        case dice
        case knock
        case readyGo
        
        func soundName() -> String {
            switch self {
            case .dice:
                return "dice"
            case .knock:
                return "knock"
            case .readyGo:
                return "readygo"
            }
        }
    }
    
    // MARK: - RoomView.Display Round Result
    fileprivate func displayRoundResult(_ results:[DGPlayerDicesTossedAndRoundResult]) {
        var allMatchedDiceViews = [UIImageView]()
        var amIWinner = false
        
        var resultOfLoser:DGPlayerDicesTossedAndRoundResult?
        var resultOfWinner:DGPlayerDicesTossedAndRoundResult?

        results.forEach { (res) in
            let playerUUID = res.playerUUID
            let dicesTossed = res.matchedInforOfDicesTossed.map({ (el) -> Int in
                return el.diceNumber
            })
            
            if playerUUID != self.delegate.myUUID() {
                self.setDiceByUUID(playerUUID, dices: dicesTossed, byAnimation: true)
            }
            
            var matchedIndices = [Int]()
            for index2Check in 0 ..< res.matchedInforOfDicesTossed.count {
                if res.matchedInforOfDicesTossed[index2Check].matched {
                    matchedIndices.append(index2Check)
                }
            }
            
            allMatchedDiceViews.append(contentsOf: self.getDiceViewOfUUIDByIndices(playerUUID, indices: matchedIndices))
            
            if res.playerUUID == self.delegate.myUUID() {
                amIWinner = res.crownModification > 0
            }
            
            if res.crownModification > 0 {
                resultOfWinner = res
            }
            if res.crownModification < 0 {
                resultOfLoser = res
            }
        }
        
        DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(3 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) { () -> Void in
            self.countingLabel.isHidden = false
            self.countingLabel.text = "0"
            
            UIView.iterateBigAndSmall(allMatchedDiceViews, callbackOnEach2Start: {(view, indexOfView) in
                self.countingLabel.text = "\(indexOfView + 1)"
                self.highlightDiceViewAsTargetDice(view as! UIImageView)
                },callbackOnEachFinished: { (view, indexOfView) in
                // do nothing
                }, callbackOnAllFinished: {
                    
                    if resultOfLoser != nil && resultOfWinner != nil {
                        self.moveCrownFrom(loser: resultOfLoser!, toWinner: resultOfWinner!)
                    }
                    
                    self.delegate.afterResultDisplayAnimation(amIWinner)
            })
        }
    }
}

// MARK: - enum
public enum DGViewCard {
    case matchingPlayer
    case waitingNewChallenger
    case waitingAllPlayersReady4NextRound
    case ready2ShakeDice
    case guessDice
    case displayResult
    case someoneLeft(messageOfLine1:String, messageOfLine2:String)
}

private enum DGScreenTouchAction {
    case nothing
    case shakeDice
    /*
    case OnIWinRound
    case OnINotWinRound
    case OnSomeoneLeft
*/
}

private enum DGStartNewButtonAction {
    case nothing
    case onIWinRound
    case onINotWinRound
    case onSomeoneLeft
}

private class DGGuessView:UIView {
    fileprivate let countLabel:UILabel
    fileprivate let diceImageView:UIImageView
    
    fileprivate static let PREFERRED_HEIGHT:CGFloat = DGUIUtils.SIZE_OF_DICE
    fileprivate static let PREFERRED_WIDTH:CGFloat = DGUIUtils.SIZE_OF_DICE * 2
    
    init() {
        self.countLabel = DGUIUtils.createUILabel(initString:"1个")
        self.countLabel.textAlignment = .center
        self.diceImageView = UIImageView(image: DGUIUtils.getFixedDiceImage(number: 1))
        
        super.init(frame: CGRect.zero)
        
        self.addSubview(self.countLabel)
        self.countLabel.snp.makeConstraints { (make) in
            make.top.equalTo(0)
            make.left.equalTo(0)
            make.bottom.equalTo(0)
            make.right.equalTo(self.snp.centerX)
        }
        
        self.addSubview(self.diceImageView)
        self.diceImageView.snp.makeConstraints { (make) in
            make.centerY.equalTo(self.snp.centerY)
            make.height.equalTo(DGUIUtils.SIZE_OF_DICE)
            make.left.equalTo(self.snp.centerX)
            make.width.equalTo(DGUIUtils.SIZE_OF_DICE)
        }
    }
    
    /*
     override init(frame: CGRect) {
     
     }
     */
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    fileprivate func setCountOfGuess(_ count:Int) {
        self.countLabel.text = "\(count)个"
    }
    
    fileprivate func setGuess(_ guess:DGGuess) {
        self.setCountOfGuess(guess.count)
        self.diceImageView.image = DGUIUtils.getFixedDiceImage(number: guess.factor)
    }
}
