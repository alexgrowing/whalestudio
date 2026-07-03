//
//  WLBase.swift
//  WhaleLib
//
//  Created by apple on 16/2/22.
//  Copyright © 2016年 WhaleStudio. All rights reserved.
//

import Foundation

public func printLog<T>(_ message: T,
    file: String = #file,
    method: String = #function,
    line: Int = #line)
{
    //    #if DEBUG
    print("\((file as NSString).lastPathComponent)[\(line)], \(method): \(message)")
    //    #endif
}

fileprivate let SIMPLE_DATE_YEAR_KEY = "SIMPLE_DATE_YEAR_KEY"
fileprivate let SIMPLE_DATE_MONTH_KEY = "SIMPLE_DATE_MONTH_KEY"
fileprivate let SIMPLE_DATE_DAY_KEY = "SIMPLE_DATE_DAY_KEY"

public class SimpleDate:NSObject, NSCoding, WLJsonable {
    public let year:Int
    public let month:Int
    public let day:Int
    
    public init(date:Date) {
        let calendar = Calendar.current
        let dateComponents = calendar.dateComponents([.year, .month, .day], from: date)
        
        self.year = dateComponents.year!
        self.month = dateComponents.month!
        self.day = dateComponents.day!
        
        super.init()
    }
    
    public func encode(with aCoder: NSCoder) {
        aCoder.encode(self.year, forKey: SIMPLE_DATE_YEAR_KEY)
        aCoder.encode(self.month, forKey: SIMPLE_DATE_MONTH_KEY)
        aCoder.encode(self.day, forKey: SIMPLE_DATE_DAY_KEY)
    }
    
    public required init?(coder aDecoder: NSCoder) {
        self.year = aDecoder.decodeInteger(forKey: SIMPLE_DATE_YEAR_KEY)
        self.month = aDecoder.decodeInteger(forKey: SIMPLE_DATE_MONTH_KEY)
        self.day = aDecoder.decodeInteger(forKey: SIMPLE_DATE_DAY_KEY)
        
        super.init()
    }
    
    public func plus(days:Int) -> SimpleDate {
        var dc = DateComponents.init()
        dc.timeZone = TimeZone.current
        dc.year = self.year
        dc.month = self.month
        dc.day = self.day + days
        
        return SimpleDate(date: Calendar.current.date(from: dc)!)
    }
    
    func asDate() -> Date {
        var dc = DateComponents()
        dc.year = self.year
        dc.month = self.month
        dc.day = self.day
        
        return Calendar.current.date(from: dc)!
    }
    
    override public var description: String {
        let formatter = DateFormatter()
        formatter.dateFormat = "yyyy-MM-dd"
        
        return formatter.string(from: self.asDate())
    }
    
    // MARK: - WLJsonable
    required public init(dict: [String : AnyObject]) {
        self.year = dict["year"] as! Int
        self.month = dict["month"] as! Int
        self.day = dict["day"] as! Int
        
        super.init()
    }
    
    public func encodeAsJson() -> [String : AnyObject] {
        return [
            "year":self.year as AnyObject,
            "month":self.month as AnyObject,
            "day":self.day as AnyObject
        ]
    }
}

public func == (left:SimpleDate, right:SimpleDate) -> Bool {
    return left.year == right.year && left.month == right.month && left.day == right.day
}

public protocol WLJsonable {
    init(dict:[String:AnyObject])
    
    func encodeAsJson() -> [String:AnyObject]
}

extension Array {
    public func shuffle() -> Array {
        var list = self
        for index in 0..<list.count {
            let newIndex = Int(arc4random_uniform(UInt32(list.count-index))) + index
            if index != newIndex {
                list.swapAt(index, newIndex)
            }
        }
        return list
    }
}

extension String {
    //返回第一次出现的指定子字符串在此字符串中的索引
    //（如果backwards参数设置为true，则返回最后出现的位置）
    public func positionOf(sub:String, backwards:Bool = false)->Int {
        var pos = -1
        
        if let range = range(of:sub, options: backwards ? .backwards : .literal ) {
            if !range.isEmpty {
                pos = self.distance(from:startIndex, to:range.lowerBound)
            }
        }
        return pos
    }
}
