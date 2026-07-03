//
//  KCTools.swift
//  KnowledgeCard
//
//  Created by alex on 2018/6/27.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import Foundation

private var imagePendingQueue = [String]()
private var isLoading = false
private var listOfListener = [KCImageToolsListener]()

class KCImageTools {
    static func appendImage2Queue(filename:String) {
        imagePendingQueue.append(filename)
        
        loadImage2DocumentFromFirst()
    }
    
    static func append(listener:KCImageToolsListener) {
        listOfListener.append(listener)
    }
    
    static func remove(listener:KCImageToolsListener) {
        for i in 0 ..< listOfListener.count {
            if (listOfListener[i] as AnyObject) === (listener as AnyObject) {
                listOfListener.remove(at: i)
                return
            }
        }
    }
    
    static func ensureDirectoryOfPic() {
        let picDir = directoryOfPic()
        if !FileManager.default.fileExists(atPath: picDir) {
            do {
                try FileManager.default.createDirectory(atPath: picDir, withIntermediateDirectories: true, attributes: nil)
            } catch {
                fatalError("fail to create directory:\(picDir)")
            }
        }
    }
    
    static func fullDirectoryOfImage(filename:String) -> String {
        return directoryOfPic() + "/" + filename
    }
    
    private static func directoryOfPic() -> String {
        let doc = NSSearchPathForDirectoriesInDomains(FileManager.SearchPathDirectory.documentDirectory, FileManager.SearchPathDomainMask.userDomainMask, true)[0]
        
        return doc + "/PIC"
    }
}

private func loadImage2DocumentFromFirst() {
    if isLoading {
        return
    }
    
    guard let filename = imagePendingQueue.first else {
        return
    }
    
    isLoading = true
    
    DispatchQueue.global().async {
        do {
            let imageData = try Data(contentsOf: WebServices.urlOf(filename: filename))

            FileManager.default.createFile(atPath: KCImageTools.fullDirectoryOfImage(filename: filename), contents: imageData, attributes: nil)
            
            listOfListener.forEach({ (listener) in
                listener.imageToolsImageDownloadedFromServer(filename: filename)
            })
        } catch {
            print(error)
        }
        imagePendingQueue.removeFirst()
        
        isLoading = false

        loadImage2DocumentFromFirst()
    }
}

protocol KCImageToolsListener {
    func imageToolsImageDownloadedFromServer(filename:String)
}
