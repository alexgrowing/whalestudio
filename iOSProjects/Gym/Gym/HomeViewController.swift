//
//  HomeViewController.swift
//  Gym
//
//  Created by alex on 2018/1/25.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import UIKit
import WhaleLib
import SnapKit

class HomeViewController : UIViewController, UIScrollViewDelegate, DayOfDaysCollectionViewDelegate, DetailViewControllerDelegate, GCenterDelegate {
    @IBOutlet weak var currentMonthOfYearLabel: UILabel!
    @IBOutlet weak var calendarScrollView: UIScrollView!
    
    private var leftCalendarView:DaysInMonthCollectionView!
    private var centerCalendarView:DaysInMonthCollectionView!
    private var rightCalendarView:DaysInMonthCollectionView!
    
    override func viewDidLoad() {
        super.viewDidLoad()
        
        self.calendarScrollView.isPagingEnabled = true
        self.calendarScrollView.showsVerticalScrollIndicator = false
        self.calendarScrollView.showsHorizontalScrollIndicator = false
        self.calendarScrollView.scrollsToTop = false
        self.calendarScrollView.delegate = self
        
        self.leftCalendarView = DaysInMonthCollectionView()
        self.calendarScrollView.addSubview(self.leftCalendarView)
        self.leftCalendarView.snp.makeConstraints { (make) in
            make.size.equalTo(self.calendarScrollView)
            make.left.equalTo(self.calendarScrollView.snp.left)
            make.top.equalTo(self.calendarScrollView.snp.top)
        }
        self.leftCalendarView.delegateOfDateEdit = self

        self.self.centerCalendarView = DaysInMonthCollectionView()
        self.calendarScrollView.addSubview(self.centerCalendarView)
        self.centerCalendarView.snp.makeConstraints { (make) in
            make.size.equalTo(self.leftCalendarView)
            make.top.equalTo(self.leftCalendarView)
            make.left.equalTo(self.leftCalendarView.snp.right)
        }
        self.centerCalendarView.delegateOfDateEdit = self
        
        self.rightCalendarView = DaysInMonthCollectionView()
        self.calendarScrollView.addSubview(self.rightCalendarView)
        self.rightCalendarView.snp.makeConstraints { (make) in
            make.size.equalTo(self.centerCalendarView)
            make.top.equalTo(self.centerCalendarView)
            make.left.equalTo(self.centerCalendarView.snp.right)
        }
        self.rightCalendarView.delegateOfDateEdit = self
        
        let dcOfToday = Calendar.current.dateComponents([.year, .month], from: Date())
        let yearOfCenterCalendarView = dcOfToday.year!
        let monthOfCenterCalendarView = dcOfToday.month!
        
        self.resetYearAndMonthOfCenterCalendarView(currentYear: yearOfCenterCalendarView, currentMonth: monthOfCenterCalendarView)
        
        GCenter.instance.appendDelegate(delegate: self)
    }
    
    override func viewDidAppear(_ animated: Bool) {
        let tempSize = self.calendarScrollView.bounds.size
        self.calendarScrollView.contentSize = CGSize(width: tempSize.width * 3, height: tempSize.height)
        
        self.centerlizeCenterCalendarView()
        
        super.viewDidAppear(animated)
    }
    
    @IBAction func onPreviousMonthPressed() {
        let tempSize = self.calendarScrollView.bounds.size

        self.calendarScrollView.scrollRectToVisible(CGRect(x: 0, y: 0, width: tempSize.width, height: tempSize.height), animated: true)
    }
    
    @IBAction func onNextMonthPressed() {
        let tempSize = self.calendarScrollView.bounds.size

        self.calendarScrollView.scrollRectToVisible(CGRect(x: tempSize.width * 2, y: 0, width: tempSize.width, height: tempSize.height), animated: true)
    }
    
    // MARK: - UIScrollViewDelegate
    func scrollViewDidEndScrollingAnimation(_ scrollView: UIScrollView) {
        let page = Int(self.calendarScrollView.contentOffset.x / self.calendarScrollView.frame.size.width)
        
        self.afterScrollTo(page: page)
    }
    
    func scrollViewDidEndDecelerating(_ scrollView: UIScrollView) {
        self.scrollViewDidEndScrollingAnimation(scrollView)
    }
    
    // MARK: - DayOfDaysCollectionViewDelegate
    func editContentOfDate(date: SimpleDate) {
        if let vc = self.storyboard?.instantiateViewController(withIdentifier: "detailvc") as? DetailViewController {
            vc.delegate = self
            
            self.present(vc, animated: true, completion: {
                if let training = GCenter.instance.getTrainingBy(date: date) {
                    vc.training = training
                } else {
                    vc.training = GTraining(date: date, moves: [GMove](), feeling: "")
                }
            })
        }
    }
    
    // MARK: - DetailViewControllerDelegate
    func onSaveDetailViewController(newTraining: GTraining) {
        GCenter.instance.setTraining(newTraining: newTraining)
        
        self.centerCalendarView.reloadData()
    }
    
    // MARK: - GCenterDelegate
    func centerModifiedByUnnaturalPower() {
        DispatchQueue.main.async {
            self.reloadAllCalendarViews()
        }
    }
    
    func centerModifiedByHumanPower() {
        // do nothing
    }
    
    // MARK: - Instance Methods
    private func afterScrollTo(page:Int) {
        let currentMonth:(year:Int, month:Int)
        if page == 0 {
            currentMonth = self.leftCalendarView.getCurrentMonth()
        } else if page == 2 {
            currentMonth = self.rightCalendarView.getCurrentMonth()
        } else {
            currentMonth = self.centerCalendarView.getCurrentMonth()
        }
        
        self.resetYearAndMonthOfCenterCalendarView(currentYear: currentMonth.year, currentMonth: currentMonth.month)
        self.centerlizeCenterCalendarView()
    }
    
    private func resetYearAndMonthOfCenterCalendarView(currentYear:Int, currentMonth:Int) {
        self.currentMonthOfYearLabel.text = "\(currentYear)年\(currentMonth)月"
        
        let previousMonth = Utils.previousMonth(currentYear: currentYear, currentMonth: currentMonth)
        self.leftCalendarView.resetBy(currentYear: previousMonth.year, currentMonth: previousMonth.month)
        
        self.centerCalendarView.resetBy(currentYear: currentYear, currentMonth: currentMonth)
        
        let nextMonth = Utils.nextMonth(currentYear: currentYear, currentMonth: currentMonth)
        self.rightCalendarView.resetBy(currentYear: nextMonth.year, currentMonth: nextMonth.month)
    }
    
    private func centerlizeCenterCalendarView() {
        let tempSize = self.calendarScrollView.bounds.size
        
        self.calendarScrollView.scrollRectToVisible(CGRect(x: tempSize.width, y: 0, width: tempSize.width, height: tempSize.height), animated: false)
    }
    
    private func reloadAllCalendarViews() {
        self.leftCalendarView.reloadData()
        self.centerCalendarView.reloadData()
        self.rightCalendarView.reloadData()
    }
}
