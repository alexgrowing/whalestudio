chrome.webRequest.onBeforeRequest.addListener(
  function(details) {
    var url = details.url;
    if (url.endsWith(".m3u8")) {
      console.log("Detected m3u8 request: " + url);
      // Do something with the m3u8 request here
    }
  },
  {urls: ["<all_urls>"]},
  ["blocking"]
);