//
//  Beans.swift
//  Gym
//
//  Created by alex on 2017/10/30.
//  Copyright © 2017年 WhaleStudio. All rights reserved.
//

import Foundation
import WhaleLib

fileprivate let GCENTER_ROOT_KEY = "GCENTER_DEFAULTS_ROOT_KEY"

fileprivate let GCENTER_USER_NAME_KEY = "GCENTER_USERNAME_KEY"
fileprivate let GCENTER_TRAININGS_KEY = "GCENTER_TRAININGS_KEY"
fileprivate let GCENTER_CATEGORIED_MOVES_KEY = "GCENTER_CATEGORIED_MOVES_KEY"
fileprivate let GCENTER_LAST_MODIFIED_DATE_KEY = "GCENTER_LAST_MODIFIED_DATE_KEY"

fileprivate let DEFAULT_CATEGORIED_MOVES:[CategoryOfMoves] = [
    CategoryOfMoves(nameOfCategory: "背", nameOfMoves: ["山羊挺身", "坐姿划船", "高位下拉", "反手高位下拉"]),
    CategoryOfMoves(nameOfCategory: "胸", nameOfMoves: ["sms卧推", "绳索夹胸", "自由卧推"]),
    CategoryOfMoves(nameOfCategory: "腿", nameOfMoves: ["哈克深蹲", "sms深蹲", "自由深蹲"]),
    CategoryOfMoves(nameOfCategory: "臀", nameOfMoves: ["反向哈克", "自由深蹲（臀）", "山羊挺身（臀）"]),
    CategoryOfMoves(nameOfCategory: "腹", nameOfMoves: ["仰卧起坐", "抬腿"])
]

public class GCenter : NSObject, NSCoding {
    private var delegates = [GCenterDelegate]()
    
    public static let instance = GCenter.read()
    
    private var trainings = [GTraining]()
    private var categoried_moves = DEFAULT_CATEGORIED_MOVES
    var lastModified = Date(timeIntervalSince1970: 0)
    
    private override init() {
        super.init()
    }
    
    private static func read() -> GCenter {
        let def = UserDefaults.standard
        
        if let savedData = def.object(forKey: GCENTER_ROOT_KEY) as? Data {
            if let savedGCenter = NSKeyedUnarchiver.unarchiveObject(with: savedData) as? GCenter {
                return savedGCenter
            }
        }
        
        return GCenter()
    }
    
    // MARK: - NSCoding
    public required init?(coder aDecoder: NSCoder) {
        self.trainings = aDecoder.decodeObject(forKey: GCENTER_TRAININGS_KEY) as! [GTraining]
        self.categoried_moves = aDecoder.decodeObject(forKey: GCENTER_CATEGORIED_MOVES_KEY) as! [CategoryOfMoves]
        
        if let theDate = aDecoder.decodeObject(forKey: GCENTER_LAST_MODIFIED_DATE_KEY) as? Date {
            self.lastModified = theDate
        }
        
        super.init()
        
        if self.categoried_moves.count == 0 {
            self.categoried_moves = DEFAULT_CATEGORIED_MOVES
        }
    }
    
    public func encode(with aCoder: NSCoder) {
        aCoder.encode(self.trainings, forKey: GCENTER_TRAININGS_KEY)
        aCoder.encode(self.categoried_moves, forKey: GCENTER_CATEGORIED_MOVES_KEY)
        aCoder.encode(self.lastModified, forKey:GCENTER_LAST_MODIFIED_DATE_KEY)
    }
    
    public func encodeAsJson() -> [String : AnyObject] {
        return [
            "lastmodified":self.lastModified.timeIntervalSince1970 as AnyObject,
            "categoriedmoves":self.categoried_moves.map({ (el) -> [String:AnyObject] in
                return el.encodeAsJson()
            }) as AnyObject,
            "trainings":self.trainings.map({ (el) -> [String:AnyObject] in
                return el.encodeAsJson()
            }) as AnyObject
        ]
    }
    
    public func encodeCategoriedMovesAsJson() -> [String:AnyObject] {
        return [
            "lastmodified":self.lastModified.timeIntervalSince1970 as AnyObject,
            "categoriedmoves":self.categoried_moves.map({ (el) -> [String:AnyObject] in
                return el.encodeAsJson()
            }) as AnyObject
        ]
    }
    
    public func encodeTrainingAsJson(training:GTraining) -> [String:AnyObject] {
        return [
            "lastmodified":self.lastModified.timeIntervalSince1970 as AnyObject,
            "training":training.encodeAsJson() as AnyObject
        ]
    }
    
    // MARK: - Instance Methods
    public func countOfTrainings() -> Int {
        return self.trainings.count
    }
    
    public func getTrainingBy(date:SimpleDate) -> GTraining? {
        for t in self.trainings {
            if t.date == date {
                return t
            }
        }
        
        return nil
    }
    
    public func getTrainingBy(index:Int) -> GTraining {
        return self.trainings[index]
    }
    
    public func countOfCategories() -> Int {
        return self.categoried_moves.count
    }
    
    public func nameOfCategoryBy(index:Int) -> String {
        return self.categoried_moves[index].nameOfCategory
    }
    
    public func countOfMovesBy(indexOfCategory:Int) -> Int {
        return self.categoried_moves[indexOfCategory].nameOfMoves.count
    }
    
    public func nameOfMoveBy(indexOfCategory:Int, indexOfMove:Int) -> String {
        return self.categoried_moves[indexOfCategory].nameOfMoves[indexOfMove]
    }
    
    public func indexPathFor(nameOfMove:String) -> (Int, Int)? {
        for indexOfCategory in 0..<countOfCategories() {
            for indexOfMove in 0..<countOfMovesBy(indexOfCategory: indexOfCategory) {
                if nameOfMoveBy(indexOfCategory: indexOfCategory, indexOfMove: indexOfMove) == nameOfMove {
                    return (indexOfCategory, indexOfMove)
                }
            }
        }
        
        return nil
    }
    
    public func nameOfCategoryBy(nameOfMove:String) -> String? {
        if let (indexOfCategory, _) = indexPathFor(nameOfMove: nameOfMove) {
            return nameOfCategoryBy(index: indexOfCategory)
        }
        
        return nil
    }
    
    private func exist(nameOfMove:String) -> Bool {
        for c in self.categoried_moves {
            for m in c.nameOfMoves {
                if m == nameOfMove {
                    return true
                }
            }
        }
        
        return false
    }
    
    func appendDelegate(delegate:GCenterDelegate) {
        self.delegates.append(delegate)
    }
    
    func sync() {
        WebServices.fetchLastModified { (success, lastModifiedServer) in
            if !success {
                return
            }
            
            let lastModifiedLocal = Int(GCenter.instance.lastModified.timeIntervalSince1970)
            
            if lastModifiedLocal == lastModifiedServer { // 本地和服务器相同版本
                // do nothing
            } else if lastModifiedServer == 0 { // 服务器上没有内容,本地有内容
                WebServices.uploadAll(callback: { (success) in
                    // do nothing
                })
            } else { // 服务器上有内容,本地可能有内容,可能没有内容
                WebServices.downloadAll(callback: { (success) in
                    // do nothing
                })
            }
            
            DispatchQueue.main.async {
//                self.refreshLastModifiedLabel()
                /*
                 
                 
                 // MARK: - Instance Methods
                 private func refreshLastModifiedLabel() {
                 if GCenter.instance.lastModified.timeIntervalSince1970 == 0 {
                 self.lastModifiedMessageLabel.text = ""
                 } else {
                 let dateFormatter = DateFormatter()
                 dateFormatter.locale = Locale.current //设置时区，时间为当前系统时间
                 //输出样式
                 dateFormatter.dateFormat = "yyyy-MM-dd HH:mm:ss"
                 
                 self.lastModifiedMessageLabel.text = "已同步:" + dateFormatter.string(from : GCenter.instance.lastModified)
                 }
                 }
 */
            }
        }
    }
    
    // MARK: - Modification Methods
    public func add(nameOfMove:String, byIndexOfCategory indexOfCategory:Int, atIndexOfMove indexOfMove:Int) -> Bool {
        if exist(nameOfMove: nameOfMove) {
            return false
        }
        
        self.categoried_moves[indexOfCategory].nameOfMoves.insert(nameOfMove, at: indexOfMove)
        
        self.save(onModified: true)
        WebServices.refreshAllMoves { (success) in
            // do nothing
        }
        
        self.delegates.forEach { (d) in
            d.centerModifiedByHumanPower()
        }
        return true
    }
    
    public func rename(newNameOfMove:String, oldNameOfMove:String) {
        if exist(nameOfMove: newNameOfMove) {
            return
        }
        
        for c in self.categoried_moves {
            for index in 0..<c.nameOfMoves.count {
                if c.nameOfMoves[index] == oldNameOfMove {
                    c.nameOfMoves[index] = newNameOfMove
                    return
                }
            }
        }
        self.save(onModified: true)
        WebServices.refreshAllMoves { (success) in
            // do nothing
        }
        
        self.delegates.forEach { (d) in
            d.centerModifiedByHumanPower()
        }
    }
    
    public func deleteMoveBy(indexOfCategory:Int, andIndexOfMove indexOfMove:Int) {
        self.categoried_moves[indexOfCategory].nameOfMoves.remove(at: indexOfMove)
        
        self.save(onModified: true)
        WebServices.refreshAllMoves { (success) in
            // do nothing
        }
        
        self.delegates.forEach { (d) in
            d.centerModifiedByHumanPower()
        }
    }
    
    public func setTraining(newTraining:GTraining) {
        // 遍历已有的training,把同一天的删掉
        var newTrainings = [GTraining]()
        for t in self.trainings {
            if !(t.date.year == newTraining.date.year && t.date.month == newTraining.date.month && t.date.day == newTraining.date.day) {
                newTrainings.append(t)
            }
        }
        
        if !newTraining.isEmpty() {
            newTrainings.append(newTraining)
        }
        
        self.trainings = newTrainings
        
        self.trainings.sort { (t1, t2) -> Bool in
            if t1.date.year < t2.date.year {
                return true
            }
            if t1.date.month < t2.date.month {
                return true
            }
            if t1.date.day < t2.date.day {
                return true
            }
            
            return false
        }
        self.save(onModified: true)
        WebServices.newTraining(newTraining: newTraining) { (success) in
            // do nothing
        }
        
        self.delegates.forEach { (d) in
            d.centerModifiedByHumanPower()
        }
    }
    
    public func refreshBy(dict: [String : AnyObject]) {
        self.lastModified = Date(timeIntervalSince1970: dict["lastmodified"] as! TimeInterval)
        
        self.categoried_moves = (dict["categoriedmoves"] as! [[String:AnyObject]]).map({ (theDict) -> CategoryOfMoves in
            return CategoryOfMoves(dict: theDict)
        })
        if self.categoried_moves.count == 0 {
            self.categoried_moves = DEFAULT_CATEGORIED_MOVES
        }
        
        self.trainings = (dict["trainings"] as! [[String:AnyObject]]).map({ (theDict) -> GTraining in
            return GTraining(dict: theDict)
        })
        
        self.save(onModified: false)
        
        self.delegates.forEach { (d) in
            d.centerModifiedByUnnaturalPower()
        }
    }
    
    public func clear() {
        UserDefaults.standard.removeObject(forKey: GCENTER_ROOT_KEY)
        
        self.trainings.removeAll()
        self.categoried_moves = DEFAULT_CATEGORIED_MOVES
        self.lastModified = Date(timeIntervalSince1970: 0)
        
        self.delegates.forEach { (d) in
            d.centerModifiedByUnnaturalPower()
        }
    }
    
    public func save(onModified:Bool) {
        if onModified {
            self.lastModified = Date()
        }
        
        let data = NSKeyedArchiver.archivedData(withRootObject: self)
        let def = UserDefaults.standard
        def.set(data, forKey: GCENTER_ROOT_KEY)
        def.synchronize()
    }
}

fileprivate let GTRAINING_DATE_KEY = "GTRAINING_DATE"
fileprivate let GTRAINING_MOVES_KEY = "GTRAINING_MOVES"
fileprivate let GTRAINING_FEELING_KEY = "GTRAINING_FEELING"

public class GTraining : NSObject, NSCoding, WLJsonable {
    public var date:SimpleDate
    public var moves:[GMove]
    public var feeling:String
    
    public init(date:SimpleDate, moves:[GMove], feeling:String) {
        self.date = date
        self.moves = moves
        self.feeling = feeling
        
        super.init()
    }
    
    // MARK: - NSCoding
    public required init?(coder aDecoder: NSCoder) {
        self.date = aDecoder.decodeObject(forKey: GTRAINING_DATE_KEY) as! SimpleDate
        self.moves = aDecoder.decodeObject(forKey: GTRAINING_MOVES_KEY) as! [GMove]
        self.feeling = aDecoder.decodeObject(forKey: GTRAINING_FEELING_KEY) as! String
        
        super.init()
    }
    
    public func encode(with aCoder: NSCoder) {
        aCoder.encode(self.date, forKey: GTRAINING_DATE_KEY)
        aCoder.encode(self.moves, forKey: GTRAINING_MOVES_KEY)
        aCoder.encode(self.feeling, forKey: GTRAINING_FEELING_KEY)
    }
    
    // MARK: - WLJsonable
    public required init(dict: [String : AnyObject]) {
        self.date = SimpleDate(dict: dict["date"] as! [String:AnyObject])
        self.moves = (dict["moves"] as! [[String:AnyObject]]).map({ (theDict) -> GMove in
            return GMove(dict: theDict)
        })
        self.feeling = dict["feeling"] as! String
        
        super.init()
    }
    
    public func encodeAsJson() -> [String : AnyObject] {
        return [
            "date":self.date.encodeAsJson() as AnyObject,
            "moves":self.moves.map({ (el) -> [String:AnyObject] in
                return el.encodeAsJson()
            }) as AnyObject,
            "feeling":self.feeling as AnyObject
        ]
    }
    
    // MARK: - Instance Methods
    public func isEmpty() -> Bool {
        return self.moves.count == 0 && self.feeling.count == 0
    }
    
    public override var description:String {
        var dict = [String:Int]()
        var moves = Set<String>()
        for m in self.moves {
            moves.insert(m.name)
        }
        for m in moves {
            if let nameOfCategory = GCenter.instance.nameOfCategoryBy(nameOfMove: m) {
                if dict.keys.contains(nameOfCategory) {
                    dict[nameOfCategory] = dict[nameOfCategory]! + 1
                } else {
                    dict[nameOfCategory] = 1
                }
            }
        }
        var strings = [String]()
        for (nameOfCategory, _) in dict {
            strings.append(nameOfCategory)
        }
        let joinedString = strings.joined(separator: " + ")
        
        return "\(self.date.description) ⎮ \(self.moves.count)个动作 ⎮ \(joinedString)"
    }
 }

fileprivate let GMOVE_NAME_KEY = "GMOVE_NAME"
fileprivate let GMOVE_WEIGTH_KEY = "GMOVE_WEIGHT"
fileprivate let GMOVE_TIMES_EACH_GROUP_KEY = "GMOVE_TIMESEACHGROUP"

public class GMove : NSObject, NSCoding, WLJsonable {
    public var name:String
    public var weight:Int
    
    public var times:Int
    
    public init(name:String, weight:Int, times:Int) {
        self.name = name
        self.weight = weight
        self.times = times
        
        super.init()
    }
    
    // MARK: - NSCoding
    public required init?(coder aDecoder: NSCoder) {
        self.name = aDecoder.decodeObject(forKey: GMOVE_NAME_KEY) as! String
        self.weight = aDecoder.decodeInteger(forKey: GMOVE_WEIGTH_KEY)
        self.times = aDecoder.decodeInteger(forKey: GMOVE_TIMES_EACH_GROUP_KEY)

        super.init()
    }
    
    public func encode(with aCoder: NSCoder) {
        aCoder.encode(self.name, forKey: GMOVE_NAME_KEY)
        aCoder.encode(self.weight, forKey: GMOVE_WEIGTH_KEY)
        aCoder.encode(self.times, forKey: GMOVE_TIMES_EACH_GROUP_KEY)
    }
    
    // MARK: - WLJsonable
    public required init(dict: [String : AnyObject]) {
        self.name = dict["name"] as! String
        self.weight = dict["weight"] as! Int
        self.times = dict["times"] as! Int
        
        super.init()
    }
    
    public func encodeAsJson() -> [String : AnyObject] {
        return [
            "name":self.name as AnyObject,
            "weight":self.weight as AnyObject,
            "times":self.times as AnyObject
        ]
    }
    
    // MARK: - Instance Methods
    public func clone() -> GMove {
        return GMove(name: self.name, weight: self.weight, times: self.times)
    }
}

fileprivate let CATEGORY_OF_MOVES_NAME_OF_CATEGORY_KEY = "CATEGORY_OF_MOVES_NAME_OF_CATEGORY_KEY"
fileprivate let CATEGORY_OF_MOVES_NAME_OF_MOVES_KEY = "CATEGORY_OF_MOVES_NAME_OF_MOVES_KEY"

public class CategoryOfMoves : NSObject, NSCoding, WLJsonable {
    let nameOfCategory:String
    var nameOfMoves:[String]
    
    init(nameOfCategory:String, nameOfMoves:[String]) {
        self.nameOfMoves = nameOfMoves
        self.nameOfCategory = nameOfCategory
    }
    
    // MARK: - NSCoding
    public required init?(coder aDecoder: NSCoder) {
        self.nameOfCategory = aDecoder.decodeObject(forKey: CATEGORY_OF_MOVES_NAME_OF_CATEGORY_KEY) as! String
        self.nameOfMoves = aDecoder.decodeObject(forKey: CATEGORY_OF_MOVES_NAME_OF_MOVES_KEY) as! [String]
        
        super.init()
    }
    
    public func encode(with aCoder: NSCoder) {
        aCoder.encode(self.nameOfCategory, forKey: CATEGORY_OF_MOVES_NAME_OF_CATEGORY_KEY)
        aCoder.encode(self.nameOfMoves, forKey: CATEGORY_OF_MOVES_NAME_OF_MOVES_KEY)
    }
    
    // MARK: - WLJsonable
    public required init(dict: [String : AnyObject]) {
        self.nameOfCategory = dict["nameofcategory"] as! String
        self.nameOfMoves = dict["nameofmoves"] as! [String]
        
        super.init()
    }
    
    public func encodeAsJson() -> [String : AnyObject] {
        return [
            "nameofcategory" : self.nameOfCategory as AnyObject,
            "nameofmoves" : self.nameOfMoves as AnyObject
        ]
    }
}

protocol GCenterDelegate {
    func centerModifiedByUnnaturalPower() // 被非自然力量改变 == 不是人为操作导致的改变
    func centerModifiedByHumanPower() // 人为操作导致的改变
}
