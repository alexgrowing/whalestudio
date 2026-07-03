//
//  DisplayViewController.swift
//  VideoLineDemo
//
//  Created by 王炜 on 2017/2/25.
//  Copyright © 2017年 Willie. All rights reserved.
//

import UIKit
import Photos

class DisplayViewController: UIViewController {
    
    /// 相册中请求出的asset，由外部赋值
    var phAsset: PHAsset?
    
    /// PHAsset中的AVAsset
    fileprivate var avAsset: AVAsset?
    /// 由AVAsset创建的AVPlayer
    fileprivate var player: AVPlayer?
    fileprivate var time2Seek : CMTime?
    /// AVPlayer的监听者
    fileprivate var playerTimeObserver: AnyObject?
    
    /// 片段的起始时间，单位秒
    fileprivate var startSecond = 0.0
    
    /// 播放控制按钮
    fileprivate lazy var playButton: UIButton = {
        let playButton = UIButton()
        playButton.setTitle("播放", for: .normal)
        playButton.backgroundColor = UIColor.red
        playButton.sizeToFit()
        return playButton
    }()
    
    fileprivate lazy var action1Button : UIButton = {
        let btn = UIButton()
        btn.setTitle("act1", for: .normal)
        btn.backgroundColor = UIColor.red
        btn.sizeToFit()
        return btn
    }()
    
    fileprivate lazy var action2Button : UIButton = {
        let btn = UIButton()
        btn.setTitle("act2", for: .normal)
        btn.backgroundColor = UIColor.red
        btn.sizeToFit()
        return btn
    }()
    /// videoLine
    fileprivate var videoLine: VideoLine!
    
    
    override func viewDidLoad() {
        super.viewDidLoad()
        view.backgroundColor = UIColor.white
        
        // 请求AVAsset
        self.requestAVAsset()
    }
    
    override func viewDidDisappear(_ animated: Bool) {
        super.viewDidDisappear(animated)
        
        // 移除播放器监听
        if let actualObserver = playerTimeObserver {
            player?.removeTimeObserver(actualObserver)
        }
    }
    
    deinit {
        print("deinit")
    }
}

let HEIGHT_OF_VIDEO_LINE:CGFloat = 50

private extension DisplayViewController {
    
    func requestAVAsset() {
        
        // 创建PHVideoRequestOptions实例
        let options = PHVideoRequestOptions()
        // 如果本地没有此视频，不允许从iCloud下载
        options.isNetworkAccessAllowed = false
        // 忽略质量，最快加载速度
        options.deliveryMode = .fastFormat
        // 从PHAsset中请求AVAsset
        PHImageManager.default().requestAVAsset(forVideo: phAsset!, options: options) { (asset, _, _) in
            DispatchQueue.main.async {
                self.avAsset = asset
                self.initPlayer()
            }
        }
    }
    
    func initPlayer() {
        
        // 1.初始化AVPlayer
        
        // 通过AVAsset创建一个AVPlayer实例
        player = AVPlayer(playerItem: AVPlayerItem(asset: avAsset!))
        // 给player添加一个监听，并指定更新周期
        playerTimeObserver = player?.addPeriodicTimeObserver(forInterval: CMTimeMakeWithSeconds(0.01, preferredTimescale: 600), queue: nil, using: { [weak self] (time) in
            
            let second = CMTimeGetSeconds(time)
            print(String(format:"current %.2f", second))
            
            self?.videoLine.update(second: second)
        }) as AnyObject?
        
        // 2.初始化AVPlayerLayer
        
        // 通过AVPlayer创建一个AVPlayerLayer实例
        let playerLayer = AVPlayerLayer(player: player)
        // 设置显示方式，frame等
        playerLayer.videoGravity = AVLayerVideoGravity.resizeAspect
        playerLayer.frame = CGRect(x: 0, y: 64, width: SCREEN_WIDTH, height: SCREEN_HEIGHT - 64 - HEIGHT_OF_VIDEO_LINE)
        playerLayer.backgroundColor = UIColor.darkGray.cgColor
        view.layer.addSublayer(playerLayer)
        
        // 3.添加控制按钮
        
        playButton.addTarget(self, action: #selector(playButtonClick), for: .touchUpInside)
        playButton.center = view.center
        view.addSubview(playButton)
        
        action1Button.addTarget(self, action: #selector(action1ButtonClick), for: .touchUpInside)
        action1Button.center = CGPoint(x: 100, y: view.center.y)
        view.addSubview(action1Button)
        action2Button.addTarget(self, action: #selector(action2ButtonClick), for: .touchUpInside)
        action2Button.center = CGPoint(x:view.bounds.width - 100, y:view.center.y)
        view.addSubview(action2Button)
        
        // 4.初始化VideoLine
        self.initVideoLine()
        
        let audioSession = AVAudioSession.sharedInstance()
        do {
            try audioSession.setCategory(.playAndRecord, options: .defaultToSpeaker)
        } catch {
            print(error)
        }
    }
    
    func initVideoLine() {
        // 通过构造器指定frame，以及绑定的AVAsset
        videoLine = VideoLine(frame: CGRect(x: 0, y: SCREEN_HEIGHT - HEIGHT_OF_VIDEO_LINE, width: SCREEN_WIDTH, height: HEIGHT_OF_VIDEO_LINE), asset: avAsset!)
        // 设置代理
        videoLine.delegate = self
        // 自定义UI
        videoLine.leftSlider.image = #imageLiteral(resourceName: "slider")
        videoLine.thumbnailSize = CGSize(width: 30, height: HEIGHT_OF_VIDEO_LINE)
        // 添加到父视图上
        view.addSubview(videoLine)
        // 开始处理数据
        videoLine.process()
    }
    
    func doPlayerPause() {
        player?.pause()
        playButton.setTitle("播放", for: .normal)
    }
    
    func doPlayerPlay() {
        player?.play()
        playButton.setTitle("暂停", for: .normal)
    }
    
    @objc func playButtonClick() {
        if player?.rate != 0 {
            self.doPlayerPause()
        } else {
            self.doPlayerPlay()
        }
    }
    
    @objc func action1ButtonClick() {
        let mixComposition = AVMutableComposition()
        let videoTrack = mixComposition.addMutableTrack(withMediaType: .video, preferredTrackID: .zero)
        do {
            try videoTrack?.insertTimeRange(CMTimeRangeMake(start: .zero, duration: CMTime(seconds: 5, preferredTimescale: 1)), of: (self.avAsset?.tracks(withMediaType: .video)[0])!, at: .zero)
            try videoTrack?.insertTimeRange(CMTimeRangeMake(start: CMTime(seconds: 10, preferredTimescale: 1), duration: CMTime(seconds: 5, preferredTimescale: 1)), of: (self.avAsset?.tracks(withMediaType: .video)[0])!, at: CMTime(seconds: 5, preferredTimescale: 1))
        } catch {
            print(error)
        }
        
        let audioTrack = mixComposition.addMutableTrack(withMediaType: .audio, preferredTrackID: .zero)
        do {
            try audioTrack?.insertTimeRange(CMTimeRangeMake(start: .zero, duration: self.avAsset!.duration), of: (self.avAsset?.tracks(withMediaType: .audio)[0])!, at: .zero)
        } catch {
            print(error)
        }
        
        let paths = NSSearchPathForDirectoriesInDomains(.documentDirectory, .userDomainMask, true)
        let documentDirectory = paths[0]
        let myPathDoc = String(format: "%@/%@-%d.mp4", documentDirectory, "mergedVidio", arc4random() % 1000)
        let url = URL(fileURLWithPath: myPathDoc)
        
        if let exporter = AVAssetExportSession.init(asset: mixComposition, presetName: AVAssetExportPresetHighestQuality) {
            exporter.outputURL = url
            exporter.outputFileType = .mp4
            exporter.shouldOptimizeForNetworkUse = true
            exporter.exportAsynchronously {
                DispatchQueue.main.async {
                    if exporter.status == .completed {
                        
                        if UIVideoAtPathIsCompatibleWithSavedPhotosAlbum(url.path) {
                            do {
                                try
                                PHPhotoLibrary.shared().performChangesAndWait {
                                    PHAssetChangeRequest.creationRequestForAssetFromVideo(atFileURL: url)
                                }
                            } catch {
                                print(error)
                            }
                            print("save to album successfully")
                        } else {
                            print("save to album failed")
                        }
                    } else {
                        print(exporter.status)
                    }
                }
            }
        }
    }
    
    @objc func action2ButtonClick() {
        
    }
}

extension DisplayViewController: VideoLineDelegate {
    
    // MARK: VideoLineDelegate
    
    func videoLine(_ videoLine: VideoLine, sliderValueChanged startSecond: Double) {
        // startSecond是选中区间开始的秒数，endSecond是选中区间结束的秒数
        
        self.startSecond = startSecond

        let newTime2Seek = CMTimeMakeWithSeconds(startSecond, preferredTimescale: 600)
        if self.time2Seek == nil {
            self.seek(time: newTime2Seek)
        } else if CMTimeCompare(newTime2Seek, self.time2Seek!) != 0 {
            self.seek(time: newTime2Seek)
        }
    }
    
    func seek(time: CMTime) {
        self.time2Seek = time
        
        player?.seek(to: time, toleranceBefore: .zero, toleranceAfter: .zero, completionHandler: { (finished) in
            if finished {
                self.time2Seek = nil
            }
        })
    }
}
