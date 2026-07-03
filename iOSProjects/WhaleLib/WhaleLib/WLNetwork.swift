//
//  WLNetwork.swift
//  WhaleLib
//
//  Created by apple on 16/2/22.
//  Copyright © 2016年 WhaleStudio. All rights reserved.
//

import Foundation

public let REQUEST_TIMEOUT:TimeInterval = 10

/*
* 其中parameters中的v:AnyObject,可能是String, NSData, [String:AnyObject]
*/
public func ajax(_ url:String, parameters:[String:AnyObject]?, callback:@escaping (_ error:NSError?, _ response:[String:AnyObject]?) -> Void) {
    ajax(url, sync: false, parameters: parameters, callback: callback)
}

public func ajax(_ url:String, sync:Bool, parameters:[String:AnyObject]?, callback:@escaping (_ error:NSError?, _ response:[String:AnyObject]?) -> Void) {
    let req = NSMutableURLRequest(url:URL(string:url)!, cachePolicy:URLRequest.CachePolicy.reloadIgnoringLocalCacheData, timeoutInterval:REQUEST_TIMEOUT)
    req.httpMethod = "POST"
    
    if let theParameters = parameters {
        var bodySegments = [String]()
        for (k, v) in theParameters {
            /*
            if let dataV = v as? Data {
                body.append("\(k)=".data(using: String.Encoding.utf8)!)
                body.append(dataV)
            } else
                */
            if let mapV = v as? [String:AnyObject] {
                if let jsonableData = try? JSONSerialization.data(withJSONObject: mapV, options: JSONSerialization.WritingOptions.prettyPrinted) {
                    let jsonString = String(data: jsonableData, encoding: .utf8)!
                    bodySegments.append("\(k)=\(jsonString)")
                }
            } else {
                bodySegments.append("\(k)=\(v)")
            }
        }

        req.httpBody = bodySegments.joined(separator: "&").addingPercentEncoding(withAllowedCharacters: .urlPathAllowed)!.data(using: String.Encoding.utf8)!
    }
    
    let semaphore = DispatchSemaphore(value: 0) // for sync
    
    let dataTask = URLSession.shared.dataTask(with: req as URLRequest) { (data, res, error) in
        if let theError = error {
            callback(theError as NSError?, nil)
        } else {
            callback(error as NSError?, (try? JSONSerialization.jsonObject(with: data!, options: JSONSerialization.ReadingOptions.mutableContainers)) as? [String:AnyObject])
        }
        
        semaphore.signal()
    }
    
    dataTask.resume()
    
    if sync {
        _ = semaphore.wait(timeout: DispatchTime.distantFuture)
    }
}



/*
public func unzipAjax(_ url:String, parameters:[String:AnyObject]?, callback:@escaping (_ error:NSError?, _ response:[String:AnyObject]?) -> Void) {
    let req = NSMutableURLRequest(url:URL(string:url)!, cachePolicy:URLRequest.CachePolicy.reloadIgnoringLocalCacheData, timeoutInterval:REQUEST_TIMEOUT)
    req.httpMethod = "POST"
    
    if let theParameters = parameters {
        let body = NSMutableData()
        var isFirstParameter = true
        for (k, v) in theParameters {
            if !isFirstParameter {
                body.append("&".data(using: String.Encoding.utf8)!)
            }
            
            if let dataV = v as? Data {
                body.append("\(k)=".data(using: String.Encoding.utf8)!)
                body.append(dataV)
            } else if let mapV = v as? [String:AnyObject] {
                if let jsonableData = try? JSONSerialization.data(withJSONObject: mapV, options: JSONSerialization.WritingOptions.prettyPrinted) {
                    body.append("\(k)=".data(using: String.Encoding.utf8)!)
                    body.append(jsonableData)
                }
            } else {
                body.append("\(k)=\(v)".data(using: String.Encoding.utf8)!)
            }
            
            isFirstParameter = false
        }
        
        req.httpBody = body as Data
    }
    
    URLSession.shared.dataTask(with: req as URLRequest) { (data, res, error) in
        if let theError = error {
            callback(theError as NSError?, nil)
        } else {
            if let decompressedData = try? data!.gunzippedData() {
                callback(error as NSError?, (try? JSONSerialization.jsonObject(with: decompressedData, options: JSONSerialization.ReadingOptions.mutableContainers)) as? [String:AnyObject])
            } else {
                callback(error as NSError?, (try? JSONSerialization.jsonObject(with: data!, options: JSONSerialization.ReadingOptions.mutableContainers)) as? [String:AnyObject])
            }
        }
    }.resume()
}
*/

public func upload(image:UIImage, toURL url:String, ofFileName filename:String) {
    //把图片转换成imageDate格式
    let imageData = image.jpegData(compressionQuality: 1.0)
    /*
     //建立请求对象
     let req = NSMutableURLRequest(url:URL(string:SERVER_UPLOAD_URL)!, cachePolicy:NSURLRequest.CachePolicy.reloadIgnoringLocalCacheData, timeoutInterval:REQUEST_TIMEOUT)
     req.httpMethod = "POST"
     
     //一连串上传头标签
     let boundary = "---------------------------14737809831466499882746641449"
     let contentType = "multipart/form-data; boundary=\(boundary)"
     req.addValue(contentType, forHTTPHeaderField: "Content-Type")
     
     let body = NSMutableData()
     body.append("\r\n--\(boundary)\r\n".data(using: String.Encoding.utf8)!)
     body.append("Content-Disposition: form-data; name=\"userfile\"; filename=\"\(filename)\"\r\n".data(using: String.Encoding.utf8)!)
     body.append("Content-Type: application/octet-stream\r\n\r\n".data(using: String.Encoding.utf8)!)
     body.append(NSData(data: imageData!) as Data)
     body.append("\r\n--\(boundary)--\r\n".data(using: String.Encoding.utf8)!)
     req.httpBody = body as Data
     */
    
    var req = URLRequest(url:URL(string:url)!, cachePolicy:NSURLRequest.CachePolicy.reloadIgnoringLocalCacheData, timeoutInterval:REQUEST_TIMEOUT)
    req.httpMethod = "POST"
    
    //一连串上传头标签
    let boundary = "---------------------------14737809831466499882746641449"
    let contentType = "multipart/form-data; boundary=\(boundary)"
    req.addValue(contentType, forHTTPHeaderField: "Content-Type")
    
    let body = NSMutableData()
    body.append("\r\n--\(boundary)\r\n".data(using: String.Encoding.utf8)!)
    body.append("Content-Disposition: form-data; name=\"userfile\"; filename=\"\(filename)\"\r\n".data(using: String.Encoding.utf8)!)
    body.append("Content-Type: application/octet-stream\r\n\r\n".data(using: String.Encoding.utf8)!)
    body.append(NSData(data: imageData!) as Data)
    body.append("\r\n--\(boundary)--\r\n".data(using: String.Encoding.utf8)!)
    req.httpBody = body as Data
    
    URLSession.shared.dataTask(with: req) { (data, res, error) in
        // do nothing
    }.resume()
}
