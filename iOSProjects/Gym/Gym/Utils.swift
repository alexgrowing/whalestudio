//
//  Utils.swift
//  Gym
//
//  Created by alex on 2018/1/9.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import UIKit
import WhaleLib

public class Utils {
    public static func firstMonthCellDay(year:Int, month:Int, isChinese:Bool) -> SimpleDate {
        var comp = DateComponents.init()
        comp.timeZone = TimeZone.current
        comp.year = year
        comp.month = month
        comp.day = 1
        
        let firstDay = Calendar.current.date(from: comp)!
        let weekday = Calendar.current.component(Calendar.Component.weekday, from: firstDay)
        
        if isChinese {
            if weekday == 1 {
                comp.day = comp.day! - 6
            } else {
                comp.day = comp.day! - (weekday - 2)
            }
        } else {
            comp.day = comp.day! - (weekday - 1)
        }
        
        let firstCellDay = Calendar.current.date(from: comp)!
        
        return SimpleDate(date: firstCellDay)
    }
    
    public static func nextMonth(currentYear:Int, currentMonth:Int) -> (year:Int, month:Int) {
        var nextMonth = currentMonth + 1
        var yearOfNextMonth = currentYear
        if nextMonth > 12 {
            nextMonth = 1
            yearOfNextMonth = yearOfNextMonth + 1
        }
        
        return (yearOfNextMonth, nextMonth)
    }
    
    public static func previousMonth(currentYear:Int, currentMonth:Int) -> (year:Int, month:Int) {
        var previousMonth = currentMonth - 1
        var yearOfPreviousMonth = currentYear
        if previousMonth < 1 {
            previousMonth = 12
            yearOfPreviousMonth = yearOfPreviousMonth - 1
        }
        
        return (yearOfPreviousMonth, previousMonth)
    }
}
