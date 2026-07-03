package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io/ioutil"
	"net/http"
	"strconv"
	"time"
	"ws/base"
)

func main() {
	print("HelloWorld")
	// startTimer(0)
}

func startTimer(timesChecked int) {
	fmt.Println("开始第", timesChecked, "次检测")
	if !doMonitor() {
		return
	}

	select {
	case <-time.After(60 * time.Second):
		startTimer(timesChecked + 1)
	}
}

func doMonitor() bool {
	client := &http.Client{}

	//url := "https://www.hermes.cn/cn/zh/search?s=picotin#positionsku=H060991CK89||%E7%B1%BB%E5%88%AB"
	url := "https://cde.hermes.cn/search/fulltext/lindy"
	//url := "https://cde.hermes.cn/search/fulltext/picotin"

	payload := make(map[string]interface{})

	payload["offset"] = 0
	payload["limit"] = 36
	payload["sort"] = "relevance"
	payload["locale"] = "cn_zh"
	payload["url_locale"] = "cn/zh"
	payload["item_type"] = []string{"product"}
	payload["category"] = ""
	payload["urlParams"] = ""

	bytesData, _ := json.Marshal(payload)
	reader := bytes.NewReader(bytesData)

	if request, err := http.NewRequest("POST", url, reader); err == nil {
		request.Header.Set("Accept", "*/*")
		request.Header.Set("Content-Type", "application/json;charset=UTF-8")
		request.Header.Set("Origin", "https://www.hermes.cn")
		request.Header.Set("Referer", "https://www.hermes.cn/cn/zh/search?s=picotin")
		request.Header.Set("User-Agent", "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_13_6) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/72.0.3626.81 Safari/537.36")
		request.Header.Set("X-Hermes-Request-ID", "chrome_6c64b2978dbfefe37c6ab45017bb9231")

		response, _ := client.Do(request)

		respBytes, _ := ioutil.ReadAll(response.Body)

		ob := make(map[string]interface{})
		json.Unmarshal(respBytes, &ob)

		items := (ob["products"].(map[string]interface{}))["items"].(map[string]interface{})

		itemsDetail := items["items"].([]interface{})
		countOfItemsFound := items["total"].(float64)

		if countOfItemsFound == 0 {
			return true
		}

		var buffer bytes.Buffer

		for i := 0; i < len(itemsDetail); i++ {
			var detail = itemsDetail[i].(map[string]interface{})

			var title = detail["title"].(string)
			var color = detail["avg_color"].(string)
			var imageURL = "https:" + detail["image"].(string)
			var shoppingURL = "https://www.hermes.cn/cn/zh/" + detail["url"].(string)

			buffer.WriteString(title + "--" + color + "<br>")
			buffer.WriteString("<img src='" + imageURL + "'/><br>")
			buffer.WriteString(shoppingURL + "<br>")
			buffer.WriteString("------------------------------------------<br>")
		}

		base.SendEmail("找到"+strconv.Itoa(int(countOfItemsFound))+"个产品", buffer.String(), "18101584@qq.com")
	}

	return false
}

func printMap(ob map[string]interface{}) {
	jsonBytes, _ := json.MarshalIndent(ob, "", "    ")
	fmt.Println(string(jsonBytes))
}
