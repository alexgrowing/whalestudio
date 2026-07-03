//
//  Beans.swift
//  KnowledgeCard
//
//  Created by alex on 2018/4/20.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import Foundation
import UIKit
import WhaleLib
import SnapKit

fileprivate let KCMAIN_ROOT_KEY = "KCMAIN_ROOT_KEY"
fileprivate let KCMAIN_KNOWLEDGES = "KCMAIN_KNOWLEDGES"
fileprivate let KCMAIN_LAST_PASTE_BOARD = "KCMAIN_LAST_PASTE_BOARD"
fileprivate let KCMAIN_SIZE_OF_TEXT = "KCMAIN_SIZE_OF_TEXT"
fileprivate let KCMAIN_LAST_MODIFIED_ONLINE = "KCMAIN_LAST_MODIFIED_ONLINE"

fileprivate let KCKNOWLEDGE_UUID_KEY = "KCKNOWLEDGE_UUID_KEY"
fileprivate let KCKNOWLEDGE_CREATED_KEY = "KCKNOWLEDGE_CREATED_KEY"
fileprivate let KCKNOWLEDGE_COMMENTS_KEY = "KCKNOWLEDGE_COMMENTS_KEY"

fileprivate let KCTEXTKNOWLEDGE_TEXT_KEY = "KCTEXTKNOWLEDGE_TEXT_KEY"
fileprivate let KCIMAGEKNOWLEDGE_IMAGE_KEY = "KCIMAGEKNOWLEDGE_IMAGE_KEY"

public class KCMain : NSObject, NSCoding {
    public static let instance = KCMain.read()
    
    private var listeners = [KCMainListener]()
    
    var lastCheckedMessageFromPaste = "" {
        didSet {
            self.save()
        }
    }
    var sizeOfText:CGFloat = 25 {
        didSet {
            self.save()
        }
    }
    private var lastModifiedOnline = Date(timeIntervalSince1970: 0)
    fileprivate var knowledges = [KCKnowledge]()
    
    private var indicesOfKnowledges = [String:Int]() // <UUID Of Knowledge:Index Of Knowledge>
    
    override init() {
        super.init()
    }
    
    public func encode(with aCoder: NSCoder) {
        aCoder.encode(self.lastCheckedMessageFromPaste, forKey:KCMAIN_LAST_PASTE_BOARD)
        aCoder.encode(self.sizeOfText, forKey:KCMAIN_SIZE_OF_TEXT)
        aCoder.encode(self.knowledges, forKey: KCMAIN_KNOWLEDGES)
        aCoder.encode(self.lastModifiedOnline, forKey:KCMAIN_LAST_MODIFIED_ONLINE)
    }
    
    required public init?(coder aDecoder: NSCoder) {
        self.lastCheckedMessageFromPaste = aDecoder.decodeObject(forKey:KCMAIN_LAST_PASTE_BOARD) as! String
        self.sizeOfText = aDecoder.decodeObject(forKey: KCMAIN_SIZE_OF_TEXT) as! CGFloat
        self.knowledges = aDecoder.decodeObject(forKey: KCMAIN_KNOWLEDGES) as! [KCKnowledge]
        
        if let modified = aDecoder.decodeObject(forKey: KCMAIN_LAST_MODIFIED_ONLINE) as? Date {
            self.lastModifiedOnline = modified
        }
        
        super.init()
        
        self.rebuildIndices()
    }
    
    private static func read() -> KCMain {
        if let savedData = UserDefaults.standard.object(forKey:KCMAIN_ROOT_KEY) as? Data {
            if let savedMain = NSKeyedUnarchiver.unarchiveObject(with: savedData) as? KCMain {
                return savedMain
            }
        }
        
        return KCMain()
    }
    
    func append(listener:KCMainListener) {
        self.listeners.append(listener)
    }
    
    public func appendKnowledgeOf(text:String) -> KCTextKnowledge {
        let kl = KCTextKnowledge(text: text)
        
        self.append(know: kl)
        
        return kl
    }
    
    public func appendKnowledgeOf(image:UIImage) -> KCImageKnowledge {
        // alex:不晓得为什么用UIImagePNGRepresentation的话有的时候图片会转一定的角度
        let randomFileName = UUID().uuidString + ".jpg"
//        FileManager.default.createFile(atPath: KCMain.fullDirectoryOfImage(filename: randomFileName), contents: UIImagePNGRepresentation(image), attributes: nil)
        FileManager.default.createFile(atPath: KCImageTools.fullDirectoryOfImage(filename: randomFileName), contents: image.jpegData(compressionQuality: 1), attributes: nil)
        
        let kl = KCImageKnowledge(name: randomFileName)
        
        self.append(know: kl)
        
        return kl
    }
    
    private func append(know:KCKnowledge) {
        self.knowledges.append(know)
        self.indicesOfKnowledges[know.uuid] = self.knowledges.count - 1
        
        know.upload2Server { (success, lastModified) in
            if success {
                self.setLastModifiedOnline(time: TimeInterval(lastModified))
            }
        }
        
        self.save()
    }
    
    public func edit(uuid:String, newText:String) {
        if let indexOfKL = self.indicesOfKnowledges[uuid] {
            if let textKL = self.knowledges[indexOfKL] as? KCTextKnowledge {
                textKL.text = newText
                
                self.save()
                
                WebServices.edit(index: indexOfKL, newText: newText) { (success, lastModified) in
                    if success {
                        self.setLastModifiedOnline(time: TimeInterval(lastModified))
                    }
                }
            }
        }
    }
    
    func count() -> Int {
        return self.knowledges.count
    }
    
    func countOfImageCard() -> Int {
        var c = 0
        self.knowledges.forEach { (kc) in
            if let _ = kc as? KCImageKnowledge {
                c = c + 1
            }
        }
        
        return c
    }
    
    func countOfTextCard() -> Int {
        var c = 0
        self.knowledges.forEach { (kc) in
            if let _ = kc as? KCTextKnowledge {
                c = c + 1
            }
        }
        
        return c
    }
    
    fileprivate func deleteKnowledgeBy(index:Int) {
        let removedEl = self.knowledges.remove(at: index)
        
        if let removedImageEl = removedEl as? KCImageKnowledge {
            do {
                try FileManager.default.removeItem(atPath: KCImageTools.fullDirectoryOfImage(filename: removedImageEl.filename))
            } catch {
                print(error)
            }
        }
        
        self.rebuildIndices()
        self.save()
        
        WebServices.delete(index: index) { (success, lastModified) in
            if success {
                self.setLastModifiedOnline(time: TimeInterval(lastModified))
            }
        }
    }
    
    public func knowledgeBy(uuid:String) -> KCKnowledge? {
        if let index = self.indicesOfKnowledges[uuid] {
            return self.knowledges[index]
        }
        
        return nil
    }
    
    func knowledgesBy(keyword:String?) -> KCKnowledgeCollection {
            var indices = [Int]()
            let count = self.knowledges.count
            for i in 0 ..< count {
                let indexOfKnow = count - 1 - i
                
                if keyword == nil || keyword!.isEmpty {
                    indices.append(indexOfKnow)
                    continue
                }
                
                if let know = self.knowledges[indexOfKnow] as? KCTextKnowledge {
                    if know.text.positionOf(sub: keyword!) >= 0 {
                        indices.append(indexOfKnow)
                    }
                }
            }
            
            return KCKnowledgeCollection(indices: indices)
    }
    
    private func isMatch(lastModifiedOnline:TimeInterval) -> Bool {
        return self.lastModifiedOnline.timeIntervalSince1970 == lastModifiedOnline
    }
    
    private func setLastModifiedOnline(time:TimeInterval) {
        self.lastModifiedOnline = Date(timeIntervalSince1970: time)
        
        self.save()
    }
    
    func getLastModifiedOnline() -> Date {
        return self.lastModifiedOnline
    }
    
    private func uploadKnowledgesFrom(index:Int, callback:@escaping (Bool, Int)->Void) {
        if self.knowledges.count > index {
            
            self.knowledges[index].upload2Server { (success, lastModified) in
                if success {
                    if self.knowledges.count > index + 1 {
                        self.uploadKnowledgesFrom(index: index + 1, callback:callback)
                        return
                    }
                }
                
                self.listeners.forEach { (l) in
                    l.mainCardDidUpload2Server(success: success)
                }
                callback(success, lastModified)
            }
        }
    }
    
    private func downloadAllFromServer() {
        self.listeners.forEach { (l) in
            l.mainCardWillDownloadFromServer()
        }
        
        WebServices.downloadAll { (success, knowsJson, lastModified) in
            if success {
                self.knowledges.forEach { (know) in
                    know.cleanup()
                }
                
                self.knowledges.removeAll()
                
                knowsJson.forEach({ (json) in
                    if let know = parseJsonAsKnowledge(json: json) {
                        self.knowledges.append(know)
                        know.downloadResourceFromServer()
                    }
                })
                self.setLastModifiedOnline(time: TimeInterval(lastModified))
                
                self.rebuildIndices()
            }
            
            self.listeners.forEach { (l) in
                l.mainCardsDownloadedFromServer(success:success)
            }
        }
    }
    
    private func rebuildIndices() {
        self.indicesOfKnowledges.removeAll()
        
        for (index, kl) in self.knowledges.enumerated() {
            self.indicesOfKnowledges[kl.uuid] = index
        }
    }
    
    public func save() {
        let data = NSKeyedArchiver.archivedData(withRootObject: self)
        UserDefaults.standard.set(data, forKey: KCMAIN_ROOT_KEY)
        UserDefaults.standard.synchronize()
        
        self.listeners.forEach { (l) in
            l.mainCardModified()
        }
    }
    
    public func sync() {
        WebServices.fetchLastModified { (success, lastModifiedAsInt) in
            if !success {
                return
            }
            
            if lastModifiedAsInt == 0 {
                // 该帐号Online没有数据
                self.uploadKnowledgesFrom(index: 0, callback: { (success, lastModified) in
                    if success {
                        self.setLastModifiedOnline(time: TimeInterval(lastModified))
                    } else {
                        print("upload failed")
                    }
                })
            } else if !self.isMatch(lastModifiedOnline: TimeInterval(lastModifiedAsInt)) {
                self.downloadAllFromServer()
            } else {
                self.listeners.forEach({ (l) in
                    l.mainCardSynchronized()
                })
            }            
        }
    }
    
    // MARK: - Static Methods
    
    /*
    static func printSubFilesOfPicDirectory() {
        do {
            let subfiles = try FileManager.default.subpathsOfDirectory(atPath: directoryOfPic())
            print(subfiles)
        } catch {
            
        }
    }
 */
}

protocol KCMainListener {
    func mainCardWillDownloadFromServer()
    func mainCardsDownloadedFromServer(success:Bool)
    
    func mainCardWillUpload2Server()
    func mainCardDidUpload2Server(success:Bool)
    
    func mainCardSynchronized()
    
    func mainCardModified()
}

class KCKnowledgeCollection {
    private var indices:[Int]
    
    init(indices:[Int]) {
        self.indices = indices
    }
    
    func count() -> Int {
        return self.indices.count
    }
    
    func knowledgeBy(index:Int) -> KCKnowledge {
        let mainIndex = self.indices[index]
        
        return KCMain.instance.knowledges[mainIndex]
    }
    
    func deleteKnowledgeBy(index:Int) -> Void {
        let mainIndex2Delete = self.indices.remove(at: index)
        for index in 0 ..< self.indices.count {
            if self.indices[index] > mainIndex2Delete {
                self.indices[index] = self.indices[index] - 1
            }
        }
        
        KCMain.instance.deleteKnowledgeBy(index: mainIndex2Delete)
    }
}

public class KCKnowledge : NSObject, NSCoding, WLJsonable {
    let created:Date
    let uuid:String
    private var comments = [String]()
    
    override init() {
        self.created = Date()
        self.uuid = UUID().uuidString
        super.init()
    }
    
    public func append(comment:String) {
        self.comments.append(comment)
    }
    
    func asUIView(delegate:KCKnowledgeViewDelegate) -> KCKnowledgeView {
        fatalError("not supported")
    }
    
    func asThumb() -> UIView {
        fatalError("not supported")
    }
    
    public func encode(with aCoder: NSCoder) {
        aCoder.encode(self.uuid, forKey: KCKNOWLEDGE_UUID_KEY)
        aCoder.encode(self.created, forKey: KCKNOWLEDGE_CREATED_KEY)
        aCoder.encode(self.comments, forKey: KCKNOWLEDGE_COMMENTS_KEY)
    }
    
    required public init?(coder aDecoder: NSCoder) {
        self.uuid = aDecoder.decodeObject(forKey: KCKNOWLEDGE_UUID_KEY) as! String
        self.created = aDecoder.decodeObject(forKey: KCKNOWLEDGE_CREATED_KEY) as! Date
        self.comments = aDecoder.decodeObject(forKey:KCKNOWLEDGE_COMMENTS_KEY) as! [String]
    }
    
    // MARK: - WLJsonable
    public required init(dict: [String : AnyObject]) {
        self.uuid = dict["uuid"] as! String
        self.created = Date(timeIntervalSince1970: dict["created"] as! TimeInterval)
        self.comments = dict["comments"] as! [String]
        
        super.init()
    }
    
    public func encodeAsJson() -> [String : AnyObject] {
        return [
            "uuid":self.uuid as AnyObject,
            "created":self.created.timeIntervalSince1970 as AnyObject,
            "comments":self.comments as AnyObject
        ]
    }
    
    // MARK: - Instance Methods
    func upload2Server(callback:@escaping (_ success:Bool, _ lastModified:Int) -> Void) {
        WebServices.uploadTextConfigure(kc: self) { (success, lastModified) in
            callback(success, lastModified)
        }
    }
    
    func cleanup() {
        
    }
    
    func downloadResourceFromServer() {
        
    }
}

public class KCTextKnowledge : KCKnowledge {
    fileprivate var text:String
    
    fileprivate init(text:String) {
        self.text = text
        super.init()
    }
    
    required public init?(coder aDecoder: NSCoder) {
        self.text = aDecoder.decodeObject(forKey: KCTEXTKNOWLEDGE_TEXT_KEY) as! String
        super.init(coder: aDecoder)
    }
    
    override public func encode(with aCoder: NSCoder) {
        super.encode(with: aCoder)
        aCoder.encode(self.text, forKey: KCTEXTKNOWLEDGE_TEXT_KEY)
    }
    
    override func asUIView(delegate:KCKnowledgeViewDelegate) -> KCKnowledgeView {
//        return KCTextKnowledgeView(textKL: self)
        return KCTextKnowledgeView(textKnow: self, delegate: delegate)
    }
    
    override func asThumb() -> UIView {
        let theView = UITextView()
        theView.isScrollEnabled = false
        theView.isEditable = false
        theView.isSelectable = false
        theView.font = UIFont.systemFont(ofSize: 11)
        theView.text = self.text
        
        return theView
    }
    
    public func getText() -> String {
        return self.text
    }
    
    // MARK: - WLJsonable
    public required init(dict: [String : AnyObject]) {
        self.text = dict["text"] as! String
        
        super.init()
    }
    
    public override func encodeAsJson() -> [String : AnyObject] {
        var json = super.encodeAsJson()
        json["text"] = self.text as AnyObject
        
        return json
    }
}

public class KCImageKnowledge : KCKnowledge {
    fileprivate let filename:String
    
    fileprivate var image:UIImage? {
        get {
            return UIImage(named: KCImageTools.fullDirectoryOfImage(filename: self.filename))
        }
    }
    
    fileprivate init(name:String) {
        self.filename = name
        super.init()
    }
    
    required public init?(coder aDecoder: NSCoder) {
        self.filename = aDecoder.decodeObject(forKey: KCIMAGEKNOWLEDGE_IMAGE_KEY) as! String
        super.init(coder: aDecoder)
    }
    
    override func asUIView(delegate:KCKnowledgeViewDelegate) -> KCKnowledgeView {
        return KCImageKnowledgeView(imageKL: self, delegate:delegate)
    }
    
    override func asThumb() -> UIView {
        let initImage:UIImage
        if let theImage = self.image {
            initImage = theImage
        } else {
            initImage = LOADING_IMAGE
        }
        
        let theView = KCImageView(image: initImage)
        theView.set(imageKL: self)
        theView.contentMode = .scaleAspectFit
        theView.backgroundColor = UIColor.black
        KCImageTools.append(listener: theView)
        
        return theView
    }
    
    override public func encode(with aCoder: NSCoder) {
        super.encode(with: aCoder)
        aCoder.encode(self.filename, forKey: KCIMAGEKNOWLEDGE_IMAGE_KEY)
    }
    
    // MARK: - WLJsonable
    public required init(dict: [String : AnyObject]) {
        self.filename = dict["filename"] as! String
        
        super.init()
    }
    
    public override func encodeAsJson() -> [String : AnyObject] {
        var json = super.encodeAsJson()
        json["filename"] = self.filename as AnyObject
        
        return json
    }
    
    // MARK: - Instance Methods
    override func upload2Server(callback: @escaping (Bool, Int) -> Void) {
        if let im = self.image {
            WebServices.uploadImage(im, self.filename)
        }
        
        super.upload2Server(callback: callback)
    }
    
    override func cleanup() {
        super.cleanup()
    }
    
    override func downloadResourceFromServer() {
        super.downloadResourceFromServer()
        
        KCImageTools.appendImage2Queue(filename: self.filename)
    }
}

enum GestureMode {
    case left
    case right
    case pending
}

class KCKnowledgeView : UIView {
    private var mode = GestureMode.pending
    private let delegate:KCKnowledgeViewDelegate
    
    init(delegate:KCKnowledgeViewDelegate) {
        self.delegate = delegate
        
        super.init(frame: CGRect.zero)
        
        self.addGestureRecognizer(UIPanGestureRecognizer(target: self, action: #selector(self.handlePanGesture(recognizer:))))
        self.addGestureRecognizer(UITapGestureRecognizer(target:self, action:#selector(self.handleTapGesture)))
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    func reset() {
        self.transform = CGAffineTransform(translationX: 0, y: 0)
    }
    
    @objc private func handlePanGesture(recognizer:UIPanGestureRecognizer) {
        let translation = recognizer.translation(in: self)

        if recognizer.state == .began || self.mode == .pending {
            if translation.x == 0 {
                self.mode = .pending
            } else if translation.x < 0 {
                self.mode = .left
            } else {
                self.mode = .right
            }
            
            return
        }
        
        self.delegate.kcKnowledgeViewPan(translation: translation, isLeft: self.mode == .left, isEnded: recognizer.state == .ended)
    }
    
    @objc private func handleTapGesture(recognizer:UITapGestureRecognizer) {
        self.delegate.kcKnowledgeViewTap()
    }
}

protocol KCKnowledgeViewDelegate {
    func kcKnowledgeViewTap()
    func kcKnowledgeViewPan(translation:CGPoint, isLeft:Bool, isEnded:Bool)
}

class KCTextKnowledgeView : KCKnowledgeView, UIPageViewControllerDataSource, UIPageViewControllerDelegate {
    private let textKL:KCTextKnowledge

    private var pagevc:UIPageViewController!
    private var vcs = [UIViewController]()
    private var pagedStrings = [NSAttributedString]()
    
    init(textKnow:KCTextKnowledge, delegate:KCKnowledgeViewDelegate) {
        self.textKL = textKnow
        
        super.init(delegate: delegate)
        
        self.pagevc = UIPageViewController(transitionStyle: .pageCurl, navigationOrientation: .horizontal, options: nil)
        self.addSubview(self.pagevc.view)
        self.pagevc.view.backgroundColor = UIColor.black
        self.pagevc.view.snp.makeConstraints { (make) in
            make.edges.equalTo(self)
        }
        self.pagevc.dataSource = self
        self.pagevc.delegate = self
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    private func pagingWith(contentString:String, contentSize:CGSize) {
        self.pagedStrings.removeAll()
        
        let style = NSMutableParagraphStyle()
        style.lineSpacing = 10
        let attributes = [
            NSAttributedString.Key.font :UIFont.systemFont(ofSize: KCMain.instance.sizeOfText),
            NSAttributedString.Key.paragraphStyle : style
        ]
        
        let textStorage = NSTextStorage(attributedString: NSAttributedString(string: contentString, attributes: attributes))
        let layoutManager = NSLayoutManager()
        textStorage.addLayoutManager(layoutManager)
        
        while true {
            let textContainer = NSTextContainer(size: contentSize)
            layoutManager.addTextContainer(textContainer)
            let range = layoutManager.glyphRange(for: textContainer)
            if range.length <= 0 {
                break
            }
            
            let ps = contentString[Range(range, in: contentString)!]
            self.pagedStrings.append(NSAttributedString(string: String(ps), attributes: attributes))
        }
        
        if self.pagedStrings.count == 0 {
            self.pagedStrings.append(NSAttributedString(string: "", attributes: attributes))
        }
    }
    
    // MARK: - UIPageViewControllerDelegate
    // MARK: - UIPageViewControllerDataSource
    func pageViewController(_ pageViewController: UIPageViewController, viewControllerBefore viewController: UIViewController) -> UIViewController? {
        if let index = self.vcs.index(of: viewController), index > 0 {
            return self.vcs[index - 1]
        } else {
            return nil
        }
    }
    
    func pageViewController(_ pageViewController: UIPageViewController, viewControllerAfter viewController: UIViewController) -> UIViewController? {
        if let index = self.vcs.index(of: viewController), index < self.vcs.count - 1 {
            return self.vcs[index + 1]
        } else {
            return nil
        }
    }
    
    override func layoutSubviews() {
        super.layoutSubviews()
        
        let sizeOfTV = self.bounds.size
        let cs = CGSize(width: sizeOfTV.width, height: sizeOfTV.height / 6 * 5)
        self.pagingWith(contentString: self.textKL.text, contentSize: cs)
        
        self.vcs.removeAll()
        self.pagedStrings.forEach { (ps) in
            let vc = UIViewController()
            vc.view.backgroundColor = BORDER_COLOR
            
            let tv = UITextView(frame: CGRect(x: 5, y: 5, width: sizeOfTV.width - 10, height: sizeOfTV.height - 10))
            vc.view.addSubview(tv)
            tv.snp.makeConstraints({ (make) in
                make.edges.equalTo(vc.view).inset(UIEdgeInsets(top: 5, left: 5, bottom: 5, right: 5))
            })
            tv.attributedText = ps
            tv.isEditable = false
            tv.isSelectable = false
            tv.isScrollEnabled = false
            tv.backgroundColor = UIColor(red: 245/255.0, green: 242/255.0, blue: 227/255.0, alpha: 1.0)
            
            let sizeOfTV = tv.bounds.size
            let fitSize = tv.sizeThatFits(CGSize(width: sizeOfTV.width, height: CGFloat.infinity))
            let offsetY = (sizeOfTV.height - fitSize.height) / 2
            tv.contentInset = UIEdgeInsets(top: offsetY, left: 0, bottom: 0, right: 0)
            
            tv.contentSize = fitSize
            
            self.vcs.append(vc)
        }
        
        self.pagevc.setViewControllers([self.vcs[0]], direction: .forward, animated: false) { (success) in
            // do nothing
        }
    }
}

class KCImageView : UIImageView, KCImageToolsListener {
    private var imageKL:KCImageKnowledge!
    
    override init(image:UIImage?) {
        super.init(image: image)
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    func set(imageKL:KCImageKnowledge) {
        self.imageKL = imageKL
    }
    
    // MARK: - KCImageToolsListener
    func imageToolsImageDownloadedFromServer(filename: String) {
        if filename == self.imageKL.filename {
            DispatchQueue.main.async {
                self.image = self.imageKL.image
                
                KCImageTools.remove(listener: self)
            }
        }
    }
    
    func imageToolsImagePendingQueueChanged() {
        // do nothing
    }
}

class KCImageKnowledgeView : KCKnowledgeView, KCImageToolsListener {
    private let imageKL:KCImageKnowledge
    
    private var imageV:UIImageView!
    
    init(imageKL:KCImageKnowledge, delegate:KCKnowledgeViewDelegate) {
        self.imageKL = imageKL
        
        super.init(delegate: delegate)
        
        self.imageV = UIImageView()
        self.addSubview(self.imageV)
        self.imageV.snp.makeConstraints { (make) in
            make.edges.equalTo(self)
        }
        
        if let theImage = imageKL.image {
            self.imageV.image = theImage
        } else {
            self.imageV.image = LOADING_IMAGE
            KCImageTools.append(listener: self)
        }
        self.imageV.contentMode = .scaleAspectFit
        self.imageV.backgroundColor = UIColor.black
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    // MARK: - KCImageToolsListener
    func imageToolsImageDownloadedFromServer(filename: String) {
        if filename == self.imageKL.filename {
            DispatchQueue.main.async {
                self.imageV.image = self.imageKL.image
                
                KCImageTools.remove(listener: self)
            }
        }
    }
    
    override func removeFromSuperview() {
        super.removeFromSuperview()
        
        KCImageTools.remove(listener: self)
    }
}

private let LOADING_IMAGE = UIImage(named: "loading_1024.png")!

private func parseJsonAsKnowledge(json:[String:AnyObject]) -> KCKnowledge? {
    if let _ = json["text"] as? String {
        return KCTextKnowledge(dict: json)
    } else if let _ = json["filename"] as? String {
        return KCImageKnowledge(dict: json)
    } else {
        return nil
    }
}
