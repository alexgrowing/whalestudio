package monitor

import (
	"bytes"
	"compress/gzip"
	"encoding/json"
	"io/ioutil"
	"net/http"

	"golang.org/x/text/encoding/simplifiedchinese"
)

// Start2 Start
func Start2() {
	str := "你好，中国"
	var gbkBytes, _ = simplifiedchinese.GBK.NewEncoder().Bytes([]byte(str))

	var utf8Bytes, _ = simplifiedchinese.GBK.NewDecoder().Bytes(gbkBytes)

	println(string(utf8Bytes))
}

// StartDy2018 Start
func StartDy2018() {
	client := &http.Client{}

	// url := "http://t66y.com/thread0806.php?fid=26&search=&page=1"
	url := "https://www.dy2018.com/"
	// url := "https://www.baidu.com"

	payload := make(map[string]interface{})

	// payload["offset"] = 0
	// payload["limit"] = 36
	// payload["sort"] = "relevance"
	// payload["locale"] = "cn_zh"
	// payload["url_locale"] = "cn/zh"
	// payload["item_type"] = []string{"product"}
	// payload["category"] = ""
	// payload["urlParams"] = ""

	bytesData, _ := json.Marshal(payload)
	reader := bytes.NewReader(bytesData)

	println("1")
	if request, err := http.NewRequest("GET", url, reader); err == nil {
		request.Header.Set("accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.9		")
		request.Header.Set("accept-encoding", "gzip, deflate, br")
		request.Header.Set("accept-language", "zh-CN,zh;q=0.9,en;q=0.8")
		request.Header.Set("cache-control", "max-age=0")
		request.Header.Set("cookie", "_ga=GA1.2.1951555167.1577238372; gr_user_id=f9a94925-6b5b-4312-815f-ce5b63e0478f; Hm_lvt_a68dc87e09b2a989eec1a0669bfd59eb=1608185081; Hm_lvt_b786b3a5dbac7560eb5f7de55097bd3b=1608185081; X_CACHE_KEY=147c3837d19b481a879452c39cede5fd; _gid=GA1.2.502962575.1608790509; gr_session_id_bce67daadd1e4d71=6056dc00-e196-4631-9873-8a214a4916f2; gr_session_id_bce67daadd1e4d71_6056dc00-e196-4631-9873-8a214a4916f2=true; Hm_lpvt_a68dc87e09b2a989eec1a0669bfd59eb=1608795356; Hm_lpvt_b786b3a5dbac7560eb5f7de55097bd3b=1608795356")
		request.Header.Set("if-modified-since", "Thu, 24 Dec 2020 07:22:35 GMT")
		request.Header.Set("if-none-match", "W/\"5fe441bb-79ca\"")
		request.Header.Set("sec-fetch-dest", "document")
		request.Header.Set("sec-fetch-mode", "navigate")
		request.Header.Set("sec-fetch-site", "none")
		request.Header.Set("sec-fetch-user", "?1")
		request.Header.Set("upgrade-insecure-requests", "1")
		request.Header.Set("user-agent", "Mozilla/5.0 (Macintosh; Intel Mac OS X 11_1_0) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/87.0.4280.67 Safari/537.36")

		println("2")
		response, _ := client.Do(request)
		println("3")
		var gr, _ = gzip.NewReader(response.Body)
		defer gr.Close()
		respBytes, _ := ioutil.ReadAll(gr)
		println("4")
		var utf8Bytes, _ = simplifiedchinese.GBK.NewDecoder().Bytes(respBytes)
		println(string(utf8Bytes))

		println("5")
	}
	println("6")
}

// Start Start
func Start() {
	client := &http.Client{}

	url := "http://t66y.com/thread0806.php?fid=26&search=&page=1"
	// url := "https://www.dy2018.com/"
	// url := "https://www.baidu.com"

	payload := make(map[string]interface{})

	// payload["offset"] = 0
	// payload["limit"] = 36
	// payload["sort"] = "relevance"
	// payload["locale"] = "cn_zh"
	// payload["url_locale"] = "cn/zh"
	// payload["item_type"] = []string{"product"}
	// payload["category"] = ""
	// payload["urlParams"] = ""

	bytesData, _ := json.Marshal(payload)
	reader := bytes.NewReader(bytesData)

	println("1")
	if request, err := http.NewRequest("GET", url, reader); err == nil {
		request.Header.Set("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.9")
		request.Header.Set("Accept-Encoding", "gzip, deflate")
		request.Header.Set("Accept-Language", "zh-CN,zh;q=0.9,en;q=0.8")
		request.Header.Set("Cache-Control", "max-age=0")
		request.Header.Set("Connection", "keep-alive")
		request.Header.Set("cookie", "__cfduid=d36c7ec956baee0f687e71c4c5aa5a5b31607484193; 227c9_lastvisit=0%091608258930%09%2Fthread0806.php%3Ffid%3D26%26search%3D%26page%3D2")
		request.Header.Set("Host", "t66y.com")
		request.Header.Set("Upgrade-Insecure-Requests", "1")
		request.Header.Set("User-Agent", "Mozilla/5.0 (Macintosh; Intel Mac OS X 11_1_0) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/87.0.4280.67 Safari/537.36")

		request.Close = true
		println("2")
		var response, err = client.Do(request)
		if err != nil {
			println(err.Error())
		} else {
			println("3")
			var gr, _ = gzip.NewReader(response.Body)
			defer gr.Close()
			respBytes, _ := ioutil.ReadAll(gr)
			println("4")
			var utf8Bytes, _ = simplifiedchinese.GBK.NewDecoder().Bytes(respBytes)
			println(string(utf8Bytes))

			println("5")
		}
	}
	println("6")
}
