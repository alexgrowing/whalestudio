////
////  MyViewController.swift
////  Gym
////
////  Created by alex on 2018/2/28.
////  Copyright © 2018年 WhaleStudio. All rights reserved.
////
//
//import UIKit
//import SnapKit
//
//public enum View {
//    case ContentView
//    case LoginView
//    case RegisterView
//}
//
//open class WLMyView : UIView, WLKeyboardToolbarDelegate {
//    private var registerView: UIView!
//    private var loginView: UIView!
//    private var contentView: UIView!
//    
//    private var registerEmailTF: UITextField!
//    private var registerVerifyCodeTF: UITextField!
//    private var registerPasswordTF: UITextField!
//    private var registerSendVerifyCodeButton: UIButton!
//    
//    private var loginEmailTF: UITextField!
//    private var loginPasswordTF: UITextField!
//    
//    private var toolbar4Keyboard:WLKeyboardToolbar!
//    
//    public override init(frame: CGRect) {
//        super.init(frame: frame)
//        
//        self.backgroundColor = UIColor.white
//        
//        self.registerView = UIView()
//        self.addSubview(self.registerView)
//        self.registerView.snp.makeConstraints { (make) in
//            make.edges.equalTo(self).inset(UIEdgeInsets(top: 0, left: 0, bottom: 0, right: 0))
//        }
//        
//        self.loginView = UIView()
//        self.addSubview(self.loginView)
//        self.loginView.snp.makeConstraints { (make) in
//            make.edges.equalTo(self).inset(UIEdgeInsets(top: 0, left: 0, bottom: 0, right: 0))
//        }
//        
//        self.contentView = UIView()
//        self.addSubview(self.contentView)
//        self.contentView.snp.makeConstraints { (make) in
//            make.edges.equalTo(self).inset(UIEdgeInsets(top: 0, left: 0, bottom: 0, right: 0))
//        }
//        
//        self.toolbar4Keyboard = WLKeyboardToolbar(delegate: self)
//        self.addSubview(self.toolbar4Keyboard)
//        NotificationCenter.default.addObserver(self, selector: #selector(keyboardWillShow(_:)), name: UIResponder.keyboardWillShowNotification, object: nil)
//        NotificationCenter.default.addObserver(self, selector: #selector(keyboardWillHide(_:)), name: UIResponder.keyboardWillHideNotification, object: nil)
//        
//        // controls in login view
//        let magicN:CGFloat = 44
//        
//        self.loginEmailTF = createTextField(placeHolder: "邮箱")
//        self.loginView.addSubview(self.loginEmailTF)
//        self.loginEmailTF.snp.makeConstraints { (make) in
//            make.left.equalTo(magicN)
//            make.right.equalTo(-magicN)
//            make.top.equalTo(magicN * 2)
//        }
//        createHorizontalLineOf(textField: self.loginEmailTF)
//        
//        self.loginPasswordTF = createTextField(placeHolder: "密码")
//        self.loginView.addSubview(self.loginPasswordTF)
//        self.loginPasswordTF.snp.makeConstraints { (make) in
//            make.left.equalTo(magicN)
//            make.right.equalTo(-magicN)
//            make.top.equalTo(self.loginEmailTF.snp.bottom).offset(magicN)
//        }
//        self.loginPasswordTF.isSecureTextEntry = true
//        createHorizontalLineOf(textField: self.loginPasswordTF)
//        
//        let loginButton = createLargeButton(title: "登录")
//        self.loginView.addSubview(loginButton)
//        loginButton.snp.makeConstraints { (make) in
//            make.left.equalTo(magicN)
//            make.right.equalTo(-magicN)
//            make.top.equalTo(self.loginPasswordTF.snp.bottom).offset(magicN)
//        }
//        loginButton.addTarget(self, action: #selector(login), for: .touchUpInside)
//        
//        let loginRegisterNowButton = createSmallButton(title: "现在注册", bright: false)
//        self.loginView.addSubview(loginRegisterNowButton)
//        loginRegisterNowButton.snp.makeConstraints { (make) in
//            make.right.equalTo(-magicN)
//            make.top.equalTo(loginButton.snp.bottom).offset(magicN)
//        }
//        loginRegisterNowButton.addTarget(self, action: #selector(showRegisterView(_:)), for: .touchUpInside)
//        
//        // controls in register view
//        self.registerEmailTF = createTextField(placeHolder: "邮箱")
//        self.registerView.addSubview(self.registerEmailTF)
//        self.registerEmailTF.snp.makeConstraints { (make) in
//            make.left.equalTo(magicN)
//            make.right.equalTo(-magicN)
//            make.top.equalTo(magicN * 2)
//        }
//        createHorizontalLineOf(textField: self.registerEmailTF)
//        self.registerVerifyCodeTF = createTextField(placeHolder: "验证码")
//        self.registerView.addSubview(self.registerVerifyCodeTF)
//        self.registerVerifyCodeTF.snp.makeConstraints { (make) in
//            make.left.equalTo(magicN)
//            make.right.equalTo(-magicN)
//            make.top.equalTo(self.registerEmailTF.snp.bottom).offset(magicN)
//        }
//        createHorizontalLineOf(textField: self.registerVerifyCodeTF)
//        self.registerSendVerifyCodeButton = createSmallButton(title: "发送验证码", bright: true)
//        self.registerView.addSubview(self.registerSendVerifyCodeButton)
//        self.registerSendVerifyCodeButton.snp.makeConstraints { (make) in
//            make.right.equalTo(-magicN)
//            make.bottom.equalTo(self.registerVerifyCodeTF.snp.bottom)
//        }
//        self.registerSendVerifyCodeButton.addTarget(self, action: #selector(self.registerSendVerifyCode), for: .touchUpInside)
//        self.registerPasswordTF = createTextField(placeHolder: "密码")
//        self.registerView.addSubview(self.registerPasswordTF)
//        self.registerPasswordTF.snp.makeConstraints { (make) in
//            make.left.equalTo(magicN)
//            make.right.equalTo(-magicN)
//            make.top.equalTo(self.registerVerifyCodeTF.snp.bottom).offset(magicN)
//        }
//        createHorizontalLineOf(textField: self.registerPasswordTF)
//        self.registerPasswordTF.isSecureTextEntry = true
//        let registerCreateAccountButton = createLargeButton(title: "注册")
//        self.registerView.addSubview(registerCreateAccountButton)
//        registerCreateAccountButton.snp.makeConstraints { (make) in
//            make.left.equalTo(magicN)
//            make.right.equalTo(-magicN)
//            make.top.equalTo(self.registerPasswordTF.snp.bottom).offset(magicN)
//        }
//        registerCreateAccountButton.addTarget(self, action: #selector(registerCreateAccount), for: .touchUpInside)
//        
//        let registerLoginNowButton = createSmallButton(title: "已有帐号", bright: false)
//        self.registerView.addSubview(registerLoginNowButton)
//        registerLoginNowButton.snp.makeConstraints { (make) in
//            make.right.equalTo(-magicN)
//            make.top.equalTo(registerCreateAccountButton.snp.bottom).offset(magicN)
//        }
//        registerLoginNowButton.addTarget(self, action: #selector(showLoginView(_:)), for: .touchUpInside)
//        
//        // controls in content view
//        let logoutButton = createLargeButton(title: "退出登录")
//        self.contentView.addSubview(logoutButton)
//        logoutButton.snp.makeConstraints { (make) in
//            make.bottom.equalTo(self.contentView.snp.bottom).offset(-magicN)
//            make.left.equalTo(0)
//            make.right.equalTo(0)
//        }
//        logoutButton.addTarget(self, action: #selector(self.logout), for: .touchUpInside)
//        
//        self.abstractDecorateContentView(contentView: self.contentView)
//    }
//    
//    required public init?(coder aDecoder: NSCoder) {
//        fatalError("init(coder:) has not been implemented")
//    }
//    
//    open override func safeAreaInsetsDidChange() {
//        super.safeAreaInsetsDidChange()
//        
//        self.registerView.snp.updateConstraints { (make) in
//            make.edges.equalTo(self).inset(self.safeAreaInsets)
//        }
//        self.loginView.snp.updateConstraints { (make) in            make.edges.equalTo(self).inset(self.safeAreaInsets)
//        }
//        self.contentView.snp.updateConstraints { (make) in
//            make.edges.equalTo(self).inset(self.safeAreaInsets)
//        }
//    }
//    
//    // MARK: - IBActions
//    @objc func showLoginView(_ sender: Any) {
//        self.switchCard(view: .LoginView)
//    }
//    @objc func showRegisterView(_ sender: Any) {
//        self.switchCard(view: .RegisterView)
//    }
//    
//    @objc func registerSendVerifyCode() {
//        guard let email = self.registerEmailTF.text else {
//            return
//        }
//        
//        WLAccount.ask4VerifyCode(email: email) { (success, error) in
//            DispatchQueue.main.async {
//                if success {
//                    self.registerSendVerifyCodeButton.isEnabled = false
//                    
//                    self.countdownOfVerifyCodeButton(secondsLeft: 60)
//                    
//                    let alert = UIAlertController(title: "", message: "验证码已发出，请注意查收来自鲸鱼工作室的邮件", preferredStyle: .actionSheet)
//                    alert.addAction(UIAlertAction(title: "确定", style: .default, handler: { (action) in
//                        // do nothing
//                    }))
//                    UIApplication.topViewController()?.present(alert, animated: true, completion: {
//                        // do nothing
//                    })
//                } else {
//                    UIApplication.topViewController()?.present(WLUI.alert(title: "验证码发送失败", message: error?.i18n()), animated: true, completion: {
//                        // do nothing
//                    })
//                }
//            }
//        }
//    }
//    
//    @objc func registerCreateAccount() {
//        guard let email = self.registerEmailTF.text else {
//            return
//        }
//        guard let password = self.registerPasswordTF.text else {
//            return
//        }
//        guard let verifyCode = self.registerVerifyCodeTF.text else {
//            return
//        }
//        
//        // 先退出编辑状态,让键盘消失,不然在Alert的时候会抛错
//        _ = UIResponder.firstResponder()?.resignFirstResponder()
//        
//        WLAccount.createAccount(email: email, password: password, verifyCode: verifyCode) { (passcode, newAccount, error) in
//            DispatchQueue.main.async {
//                if passcode != nil && newAccount != nil {
//                    if newAccount! {
//                        UIApplication.topViewController()?.present(WLUI.alert(title: "成功创建帐户", message: ""), animated: true, completion: {
//                            self.abstractDidLoginByEmailAndPasswordSuccessfully(passcode: passcode!)
//                        })
//                    } else {
//                        UIApplication.topViewController()?.present(WLUI.alert(title: "成功更新密码", message: ""), animated: true, completion: {
//                            self.abstractDidLoginByEmailAndPasswordSuccessfully(passcode: passcode!)
//                        })
//                    }
//                } else {
//                    UIApplication.topViewController()?.present(WLUI.alert(title: "创建帐户失败", message: error?.i18n()), animated: true, completion: {
//                        // do nothing
//                    })
//                }
//            }
//        }
//        
//    }
//    
//    @objc func login() {
//        guard let email = self.loginEmailTF.text else {
//            return
//        }
//        guard let password = self.loginPasswordTF.text else {
//            return
//        }
//        
//        // 先退出编辑状态,让键盘消失,不然在Alert的时候会抛错
//        _ = UIResponder.firstResponder()?.resignFirstResponder()
//        
//        WLAccount.login(email: email, password: password) { (passcode, error) in
//            DispatchQueue.main.async {
//                if passcode != nil {
//                    self.abstractDidLoginByEmailAndPasswordSuccessfully(passcode: passcode!)
//                } else {
//                    guard let em = error else {
//                        return
//                    }
//                    
//                    if em.raw == WLAccount.ERROR_LOGIN_ACCOUNT_NOT_FOUND {
//                        self.actionAfterAccountNotFound()
//                    } else if em.raw == WLAccount.ERROR_LOGIN_WRONG_PASSWORD {
//                        self.actionAfterWrongPassword()
//                    } else {
//                        print(em)
//                    }
//                }
//            }
//        }
//    }
//    
//    @objc func logout() {
//        let alert = UIAlertController(title: "", message: "退出后将清空本地数据，下次登录会重新下载数据", preferredStyle: .actionSheet)
//        alert.addAction(UIAlertAction(title: "退出登录", style: .default, handler: { (action) in
//            self.switchCard(view: .LoginView)
//            self.abstractDidLogout()
//        }))
//        alert.addAction(UIAlertAction(title: "取消", style: .cancel, handler: { (action) in
//            // do nothing
//        }))
//        
//        UIApplication.topViewController()?.present(alert, animated: true) {
//            // do nothing
//        }
//    }
//    
//    // MARK: - WLKeyboardToolbarDelegate
//    public func keyboardToolbarYesPressed(toolbar: WLKeyboardToolbar) {
//        UIResponder.resignFirstResponder()
//        self.toolbar4Keyboard.hide()
//    }
//    
//    // MARK: - Methods For Subclass Override
//    open func abstractDecorateContentView(contentView:UIView) {}
//    
//    open func abstractDidLogout() {
//        WLAccount.userPasscode = nil
//    }
//    
//    open func abstractDidLoginByEmailAndPasswordSuccessfully(passcode:String) {
//        WLAccount.userPasscode = passcode
//        
//        self.switchCard(view: .ContentView)
//    }
//    
//    // MARK: - Instance Methods
//    @objc func keyboardWillShow(_ notification: Notification) {
//        guard let _ = UIResponder.firstResponder() else {
//            return
//        }
//        
//        let dict = NSDictionary(dictionary: notification.userInfo!)
//        let keyboardFrame = dict[UIResponder.keyboardFrameEndUserInfoKey] as! CGRect
//        
//        let yPointOfToolbar = keyboardFrame.origin.y - WLKeyboardToolbar.HEIGHT_OF_KEYBOARD_TOOLBAR
//        
//        self.toolbar4Keyboard.moveTo(yPoint: yPointOfToolbar)
//    }
//    
//    @objc func keyboardWillHide(_ notification:Notification) {
//        self.toolbar4Keyboard.hide()
//    }
//    
//    public func checkState() {
//        if WLAccount.userPasscode != nil { // 说明用这个userPasscode是可以QuickLogin的
//            self.switchCard(view: .ContentView)
//        } else {
//            self.switchCard(view: .LoginView)
//        }
//    }
//    
//    public func switchCard(view:View) {
//        self.contentView.isHidden = true
//        self.registerView.isHidden = true
//        self.loginView.isHidden = true
//        
//        switch view {
//        case .ContentView:
//            self.contentView.isHidden = false
//            self.loginPasswordTF.text = ""
//            self.registerPasswordTF.text = ""
//        case .LoginView:
//            self.loginView.isHidden = false
//            self.loginEmailTF.becomeFirstResponder()
//        case .RegisterView:
//            self.registerView.isHidden = false
//            self.registerEmailTF.becomeFirstResponder()
//        }
//    }
//    
//    private func actionAfterAccountNotFound() {
//        let alertVC = UIAlertController(title: "帐号不存在", message:"", preferredStyle: .alert)
//        alertVC.addAction(UIAlertAction(title: "取消", style: .default, handler: { (action) in
//            // do nothing
//        }))
//        alertVC.addAction(UIAlertAction(title: "注册", style: .default, handler: { (action) in
//            self.switchCard(view: .RegisterView)
//            self.registerEmailTF.text = self.loginEmailTF.text
//            self.registerPasswordTF.text = self.loginPasswordTF.text
//        }))
//        UIApplication.topViewController()?.present(alertVC, animated: true) {
//            // do nothing
//        }
//    }
//    
//    private func actionAfterWrongPassword() {
//        let alertVC = UIAlertController(title: "密码错误", message:"", preferredStyle: .alert)
//        alertVC.addAction(UIAlertAction(title: "取消", style: .default, handler: { (action) in
//            // do nothing
//        }))
//        alertVC.addAction(UIAlertAction(title: "重置密码", style: .default, handler: { (action) in
//            self.switchCard(view: .RegisterView)
//            self.registerEmailTF.text = self.loginEmailTF.text
//            self.registerPasswordTF.text = self.loginPasswordTF.text
//        }))
//        UIApplication.topViewController()?.present(alertVC, animated: true) {
//            // do nothing
//        }
//    }
//    
//    private func countdownOfVerifyCodeButton(secondsLeft:Int) {
//        if secondsLeft <= 0 {
//            self.registerSendVerifyCodeButton.isEnabled = true
//            self.registerSendVerifyCodeButton.setTitle("发送验证码", for: .normal)
//            return
//        }
//        
//        self.registerSendVerifyCodeButton.setTitle("\(secondsLeft)", for: .normal)
//        DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(1 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) {
//            self.countdownOfVerifyCodeButton(secondsLeft: secondsLeft - 1)
//        }
//    }
//}
//
//private func createLargeButton(title:String) -> UIButton {
//    let btn = UIButton()
//    btn.setTitle(title, for: .normal)
//    btn.titleLabel?.font = UIFont.systemFont(ofSize: 20)
//    btn.setTitleColor(UIColor.white, for: .normal)
//    btn.backgroundColor = UIColor.lightGray
//
//    return btn
//}
//
//private func createSmallButton(title:String, bright:Bool) -> UIButton {
//    let btn = UIButton()
//    btn.setTitle(title, for: .normal)
//    btn.titleLabel?.font = UIFont.systemFont(ofSize: 15)
//    if bright {
//        btn.setTitleColor(UIColor.blue, for: .normal)
//    } else {
//        btn.setTitleColor(UIColor.lightGray, for: .normal)
//    }
//    btn.backgroundColor = UIColor.clear
//
//    return btn
//}
//
//private func createTextField(placeHolder:String) -> UITextField {
//    let tf = UITextField()
//    tf.placeholder = placeHolder
//    tf.font = UIFont.systemFont(ofSize: 20)
//    
//    return tf
//}
//
//private func createHorizontalLineOf(textField:UITextField) {
//    let horizontalLine =  UIView()
//    horizontalLine.backgroundColor = UIColor.lightGray
//    textField.superview?.addSubview(horizontalLine)
//    
//    horizontalLine.snp.makeConstraints { (make) -> Void in
//        make.height.equalTo(0.5)
//        make.left.equalTo(textField)
//        make.right.equalTo(textField)
//        make.top.equalTo(textField.snp.bottom).offset(5)
//    }
//}
