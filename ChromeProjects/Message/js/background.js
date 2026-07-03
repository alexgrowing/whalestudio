
//响应开始(用来检测媒体文件地址大小等信息)
chrome.webRequest.onResponseStarted.addListener(
    function(data){
        findMedia(data);
    },
    {urls: ["http://*/*", "https://*/*"]},
    ["responseHeaders"]
);

function findMedia(data){
    if (data["url"] != undefined && data["url"].endsWith(".m3u8")) {
        console.log(data["url"])
    }
}