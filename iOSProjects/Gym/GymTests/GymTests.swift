//
//  GymTests.swift
//  GymTests
//
//  Created by alex on 2017/10/30.
//  Copyright © 2017年 WhaleStudio. All rights reserved.
//

import XCTest
import Gym
import WhaleLib

class GymTests: XCTestCase {
    
    override func setUp() {
        super.setUp()
        // Put setup code here. This method is called before the invocation of each test method in the class.
    }
    
    override func tearDown() {
        // Put teardown code here. This method is called after the invocation of each test method in the class.
        super.tearDown()
    }
    
    func testUtils() {
        let sd = Utils.firstMonthCellDay(year: 2008, month: 6, isChinese: true)
        print(sd)
//        assert(Utils.set(year: 2008, month: 2) == 6)
//        assert(Utils.set(year: 2008, month: 3) == 7)
//        assert(Utils.set(year: 2008, month: 4) == 3)
//        assert(Utils.set(year: 2008, month: 5) == 5)
//        assert(Utils.set(year: 2008, month: 6) == 1)
    }
    
    func testExample() {
        let move1 = GMove(name: "硬拉", weight: 10, times: 20)
        let move2 = GMove(name: "山羊挺身", weight: 0, times: 30)
        let move3 = GMove(name: "倒蹬", weight: 0, times: 15)
        
        let dateFormatter = DateFormatter()
        dateFormatter.locale = Locale.current // 设置时区
        dateFormatter.dateFormat = "yyyy-MM-dd"
        
        let d1 = dateFormatter.date(from: "2017-11-1")!
        let d2 = dateFormatter.date(from: "2017-11-12")!
        let training1 = GTraining(date: SimpleDate(date:d1), moves: [move1, move2], feeling: "好极了")
        let training2 = GTraining(date: SimpleDate(date:d2), moves: [move2, move3], feeling: "还行吧")
        
        let data = NSKeyedArchiver.archivedData(withRootObject: [training1, training2])
        let def = UserDefaults.standard
        def.set(data, forKey: "TRAININGS")
        def.synchronize()
        
        if let savedData = def.object(forKey: "TRAININGS") as? Data {
            if let savedTrainings = NSKeyedUnarchiver.unarchiveObject(with: savedData) as? [GTraining] {
                XCTAssert(savedTrainings.count == 2)
                
                XCTAssert(savedTrainings[0].feeling == "好极了")
                XCTAssert(savedTrainings[1].feeling == "还行吧")
                
                XCTAssert(savedTrainings[0].date == SimpleDate(date:d1))
                XCTAssert(savedTrainings[1].date == SimpleDate(date:d2))
                
                XCTAssert(savedTrainings[0].moves.count == 2)
                XCTAssert(savedTrainings[1].moves.count == 2)
                
                XCTAssert(savedTrainings[0].moves[0].name == "硬拉" && savedTrainings[0].moves[0].weight == 10 && savedTrainings[0].moves[0].times == 20)
                XCTAssert(savedTrainings[0].moves[1].name == "山羊挺身" && savedTrainings[0].moves[1].weight == 0 && savedTrainings[0].moves[1].times == 30)
                XCTAssert(savedTrainings[1].moves[0].name == "山羊挺身" && savedTrainings[1].moves[0].weight == 0 && savedTrainings[1].moves[0].times == 30)
                XCTAssert(savedTrainings[1].moves[1].name == "倒蹬" && savedTrainings[1].moves[1].weight == 0 && savedTrainings[1].moves[1].times == 15)
            }
        }
    }
 
    /*
    func testPerformanceExample() {
        // This is an example of a performance test case.
        self.measure {
            // Put the code you want to measure the time of here.
        }
    }
 */
    
}
