//
//  KnowledgeCardTests.swift
//  KnowledgeCardTests
//
//  Created by alex on 2018/4/21.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import XCTest
import KnowledgeCard
import WhaleLib

class KnowledgeCardTests: XCTestCase {
    
    override func setUp() {
        super.setUp()
        // Put setup code here. This method is called before the invocation of each test method in the class.
    }
    
    override func tearDown() {
        // Put teardown code here. This method is called after the invocation of each test method in the class.
        super.tearDown()
    }
    
    func testExample() {
        let array = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        var (a, b, c, d, e, f, g, h, i, j) = (0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
        for _ in 0..<1_0000 {
            switch array.shuffle()[0] {
            case 1: a = a + 1
            case 2: b = b + 1
            case 3: c = c + 1
            case 4: d = d + 1
            case 5: e = e + 1
            case 6: f = f + 1
            case 7: g = g + 1
            case 8: h = h + 1
            case 9: i = i + 1
            case 10: j = j + 1
            default: break
            }
        }
        print("第一个数值的分布:\(a, b, c, d, e, f, g, h, i, j)")
        
        // 测试性能，对元素个数为 10 万个的数组排序所需的时间
        let interval = NSDate().timeIntervalSince1970
        let arr = [Int](repeating: 100, count: 10_0000)
        _ = arr.shuffle()
        let interval1 = NSDate().timeIntervalSince1970
        print("所需时间:\(interval1 - interval)")
    }
    
    func testPerformanceExample() {
        // This is an example of a performance test case.
        self.measure {
            // Put the code you want to measure the time of here.
        }
    }
    
}
