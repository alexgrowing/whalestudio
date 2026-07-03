package main

import (
	"encoding/json"
	"fmt"
	"io/ioutil"
	"net/http"
	"os"
	"strconv"
	"time"
	"ws/base"
	"gopkg.in/mgo.v2/bson"
	"text/template"
	"io"
	"bytes"
	"bufio"
	"strings"
	"github.com/PuerkitoBio/goquery"
	"golang.org/x/net/html"
	"log"
)

const (
	dbName = "CompanyFinance"

	tableNameBalance = "Blance"
	tableNameCashFlow = "CashFlow"
	tableNameIncome = "Income"
	tableNameSource = "Source"
)

var companys = []string {
"AAPL", "BABA", "TSLA", "DIS", "BIDU",
"JD", "FB", "SNE", "NFLX", "MSFT",
"GOOG", "GOOGL", "AMZN", "KO", "NTDOY",
"PFE", "MRK", "PDD", "TWTR", "WFC",
"NVDA", "QCOM", "WB", "SINA", "MS", "BRK.A","DATA","NTES","SBUX",
}

var companiesFromQianzhan = []string {
	"data.n", "tsla.o", "aapl.o","baba.n","dis.n","bidu.o","jd.o","fb.o","sne.n",
	"nflx.o","msft.o","goog.o","googl.o","amzn.o","ko.n","pfe.n","mrk.n","pdd.o",
	"twtr.n", "wfc.n","nvda.o","qcom.o","wb.o","sina.o","ms.n","brk.a","sbux.o",
}

var companiesFromHK = []string {
	"03690", // 美团点评
	"01810", // 小米
	"00700", // 腾讯
	"01458", // 周黑鸭
	"02378", // 保诚
	"01299", // 友邦保险
}

var kindsOfReport = []string {
	"zichanfuzhai",
	"xianjinliuliang",
	"lirun",
}

func main() {
	checkAttributesOfReports()
	//checkAll()

	//exportAsExcel("WB", "2018-06")

	//exportAllSeasonsAsCSV("DATA")
	//exportAllSeasonsAsCSV("PFE")
	//exportAllSeasonsAsCSV("MRK")
	//exportAllSeasonsAsCSV("KO")
	//exportAllSeasonsAsCSV("GOOGL")
	//exportAllSeasonsAsCSV("AAPL")
}

func fetchFinanceReportFromQianzhan() {
	for _, c := range companiesFromQianzhan {
		export2CSVByGoquery(c, true)
	}

	for _, c := range companiesFromHK {
		export2CSVByGoquery(c, false)
	}
}

func checkCountOfReports() {
	for _, k := range kindsOfReport {
		for _, hkCompany := range companiesFromHK {
			if count, err := base.DBCount(dbName, tableNameSource, bson.M{"symbol":hkCompany, "财报类型":k}); err == nil {
				fmt.Println(hkCompany, ".", k, ".count:", count)
			} else {
				log.Fatal(err)
			}
		}

		for _, usCompany := range companiesFromQianzhan {
			if count, err := base.DBCount(dbName, tableNameSource, bson.M{"symbol":usCompany, "财报类型":k}); err == nil {
				fmt.Println(usCompany, ".", k, ".count:", count)
			} else {
				log.Fatal(err)
			}
		}
	}
}

func checkAttributesOfReports() {
	for _, k := range kindsOfReport {
		allReports := make([]base.SM, 0)
		base.DBFindAll(dbName, tableNameSource, bson.M{"财报类型":k}, &allReports)

		attributes := base.SM{}
		for _, r := range allReports {
			for k, _ := range r {
				if attributes[k] == nil {
					attributes[k] = r["symbol"]
				}
			}
		}

		fmt.Println(k, ".count:",len(attributes))
		for k, v := range attributes {
			fmt.Println(k, ":", v)
		}
	}
}

func exportAllSeasonsAsCSV(symbol string) {
	var bss []BalanceSheetQ
	base.DBFindAll(dbName, tableNameBalance, bson.M{"symbol":symbol}, &bss)

	lines := make([]string, 0)

	if f, err := os.Open("large-tag.csv"); err == nil {
		buf := bufio.NewReader(f)
		for {
			if line, err := buf.ReadString('\n'); err == nil {
				lines = append(lines, strings.TrimSpace(line))
			} else if err == io.EOF {
				break
			}
		}
	}

	for _, bs := range bss {
		date := bs.Date

		var is IncomeStatementQ
		base.DBFindOne(dbName, tableNameIncome, bson.M{"symbol":symbol, "date":date}, &is)

		var cfs CashFlowStatementQ
		base.DBFindOne(dbName, tableNameCashFlow, bson.M{"symbol":symbol, "date":date}, &cfs)

		dict := base.SM{}
		dict["BS"] = bs
		dict["IS"] = is
		dict["CFS"] = cfs
		dict["SYMBOL"] = symbol

		filename := "large-value.csv"

		t := template.Must(template.New("").ParseFiles(filename))

		//f, _ := os.Create("large-" + date + ".csv")
		writer := bytes.NewBuffer(make([]byte, 0))
		t.ExecuteTemplate(writer, filename, dict)

		numberOfLine := 0
		reader := bufio.NewReader(writer)
		for {
			if line, err := reader.ReadString('\n'); err == nil {
				lines[numberOfLine] = lines[numberOfLine] + ";" + strings.TrimSpace(line)
			} else if err == io.EOF {
				break
			} else {
				fmt.Println(err)
			}

			numberOfLine++
		}
	}

	ofilename := "CSV/" + symbol + ".csv"
	var f *os.File
	if _, err := os.Stat(ofilename); os.IsNotExist(err) {
		f, _ = os.Create(ofilename)
	} else {
		f, _ = os.Open(ofilename)
	}

	fileWriter := bufio.NewWriter(f)
	for _, line := range lines  {
		fileWriter.WriteString(line)
		fileWriter.WriteString("\n")
	}
	fileWriter.Flush()
	f.Close()
}

func exportAsExcel(symbol string, date string) {
	bs := BalanceSheetQ{}
	base.DBFindOne(dbName, tableNameBalance, bson.M{"symbol":symbol, "date":date}, &bs)

	is := IncomeStatementQ{}
	base.DBFindOne(dbName, tableNameIncome, bson.M{"symbol":symbol, "date":date}, &is)

	cfs := CashFlowStatementQ{}
	base.DBFindOne(dbName, tableNameCashFlow, bson.M{"symbol":symbol, "date":date}, &cfs)

	dict := base.SM{}
	dict["BS"] = bs
	dict["IS"] = is
	dict["CFS"] = cfs
	dict["SYMBOL"] = symbol
	dict["DATE"] = date

	t := template.New("")
	t = template.Must(t.ParseFiles("large.xml"))

	f, _ := os.Create("test.xml")
	defer f.Close()
	t.ExecuteTemplate(f, "large.xml", dict)
	f.Sync()
}

var collector map[string][]string

func checkAll() {
	collector = make(map[string][]string)
	for _, c := range companys {
		check(c, "2018-06")
	}

	for k,v := range collector {
		fmt.Println(k, "-", len(v),":",v)
	}
}

func check(symbol string, date string) {
	bs := BalanceSheetQ{}
	base.DBFindOne(dbName, tableNameBalance, bson.M{"symbol":symbol, "date":date}, &bs)

	is := IncomeStatementQ{}
	base.DBFindOne(dbName, tableNameIncome, bson.M{"symbol":symbol, "date":date}, &is)

	cfs := CashFlowStatementQ{}
	base.DBFindOne(dbName, tableNameCashFlow, bson.M{"symbol":symbol, "date":date}, &cfs)

	c := 0

	c = c + assert([]float64 {bs.TotalAssets},
		[]float64 {bs.TotalCurrentAssets, bs.TotalNonCurrentAssets},
		"资产总额=流动资产总额+长期资产总额", symbol)
	c = c + assert([]float64 {bs.TotalCurrentAssets},
		[]float64 {bs.TotalCash, bs.Receivables, bs.PrepaidExpenses, bs.Inventories, bs.OtherCurrentAssets},
		"流动资产总额=现金总额+应收账款+预付费用+存货+其他流动资产", symbol)
	c = c + assert([]float64 {bs.TotalCash},
		[]float64{bs.CashAndCashEquivalents, bs.ShortTermInvestments},
		"现金总额=现金及现金等价物+短期投资", symbol)
	c = c + assert([]float64 {bs.TotalNonCurrentAssets},
		[]float64{bs.NetPropertyPlantAndEquipment,bs.DeferredIncomeTaxes, bs.EquityAndOtherInvestments,bs.Goodwill, bs.OtherLongTermAssets},
		"长期资产总额=固定资产总额+递延税+股票及其他投资+商誉价值+其他长期资产", symbol)
	c = c + assert([]float64 {bs.NetPropertyPlantAndEquipment},
		[]float64{bs.GrossProperty, bs.AccumulatedDepreciation},
		"固定资产总额=固定资产+累积折旧", symbol)
	c = c + assert([]float64 {bs.TotalLiabilitiesAndStockholdersEquity},
		[]float64{bs.TotalLiabilities, bs.TotalStockholdersEquity},
		"负债和股东权益总计=负债总额+股东权益总计", symbol)
	c = c + assert([]float64 {bs.TotalLiabilities},
		[]float64{bs.TotalCurrentLiabilities, bs.TotalNonCurrentLiabilities},
		"负债总额=流动负债总额+长期负债总额", symbol)
	//c = c + assert([]float64 {bs.TotalLiabilities},
	//	[]float64{bs.PayablesAndAccruedExpenses, bs.AccountsPayable, bs.TaxesPayable, bs.AccruedLiabilities, bs.Deposits, bs.FederalFundsPurchased, bs.DerivativeLiabilities,
	//		bs.Payables, bs.TradingLiabilities, bs.ShortTermBorrowing, bs.ShortTermDebt, bs.AccruedExpensesAndLiabilities, bs.CapitalLeases, bs.OtherCurrentLiabilities, bs.LongTermDebt,
	//		bs.DeferredTaxes, bs.MinorityInterest, bs.DeferredTaxesLiabilities, bs.DeferredRevenues, bs.OtherLongTermLiabilities, bs.OtherLiabilities},
	//	"负债总额=应付款项及应计费用+应付账款+应付税款+应计债务+存款额+联邦基金费用+衍生负债+应付款项+交易负债+短期借债+短期借贷+预提支出及负债+租赁资本+其他流动负债+长期负债+递延税金+少数股东权益+递延所得税负债+递延收入+其他长期负债+其他负债", symbol)
	c = c + assert([]float64 {bs.TotalCurrentLiabilities},
		[]float64{bs.AccountsPayable, bs.TaxesPayable, bs.AccruedLiabilities, bs.ShortTermDebt, bs.OtherCurrentLiabilities},
		"流动负债总额=应付账款+应付税款+应计债务+短期借贷+其他流动负债", symbol)
	c = c + assert([]float64 {bs.TotalNonCurrentLiabilities},
		[]float64{bs.LongTermDebt, bs.DeferredTaxesLiabilities, bs.DeferredRevenues, bs.OtherLongTermLiabilities},
		"长期负债总额=长期负债+递延所得税负债+递延收入+其他长期负债", symbol)
	c = c + assert([]float64 {bs.TotalStockholdersEquity},
		[]float64{bs.AdditionalPaidInCapital, bs.PreferredStock, bs.CommonStock, bs.RetainedEarnings, bs.TreasuryStock, bs.AccumulatedOtherComprehensiveIncome},
		"股东权益总计=资本公积+优先股+普通股+留存收益+库存股份+累积其他综合收益", symbol)
	c = c + assert([]float64 {cfs.NetIncome},
		[]float64{is.NetIncomeFromContinuingOperations},
		"净利润=利润表.持续经营收益", symbol)
	c = c + assert([]float64 {cfs.NetCashUsedForInvestingActivities},
		[]float64{cfs.InvestmentsInPropertyPlantAndEquipment, cfs.AcquisitionsNet, cfs.PurchasesOfInvestments, cfs.SalesMaturitiesOfInvestments, cfs.OtherInvestingActivities},
		"投资活动带来的净现金流=固定资产投资+收购+购买投资资产+债务/销售投资+其他投资活动", symbol)
	c = c + assert([]float64 {cfs.NetCashProvidedByUsedForFinancingActivities},
		[]float64{cfs.DebtIssued, cfs.DebtRepayment, cfs.CommonStockIssued, cfs.CommonStockRepurchased, cfs.DividendPaid, cfs.OtherFinancingActivities},
		"融资活动带来的净现金流=债券发行+债券偿还+普通股发行+普通股回购+股息支付+其他金融活动", symbol)
	c = c + assert([]float64 {cfs.NetChangeInCash},
		[]float64{cfs.NetCashProvidedByOperatingActivities, cfs.NetCashUsedForInvestingActivities, cfs.NetCashProvidedByUsedForFinancingActivities, cfs.EffectOfExchangeRateChanges},
		"净现金变化=经营活动带来的净现金流+投资活动带来的净现金流+融资活动带来的净现金流+汇率变动的影响", symbol)
	c = c + assert([]float64 {cfs.OperatingCashFlow},
		[]float64{cfs.NetCashProvidedByOperatingActivities},
		"营运现金流量=经营活动带来的净现金流", symbol)
	c = c + assert([]float64 {cfs.CapitalExpenditure},
		[]float64{cfs.InvestmentsInPropertyPlantAndEquipment},
		"资本支出=固定资产投资", symbol)
	c = c + assert([]float64 {cfs.FreeCashFlow},
		[]float64{cfs.OperatingCashFlow, cfs.CapitalExpenditure},
		"自由现金流=营运现金流量+资本支出", symbol)
	c = c + assert([]float64 {cfs.CashAtEndOfPeriod},
		[]float64{cfs.CashAtBeginningOfPeriod, cfs.NetChangeInCash},
		"期末现金流=期初现金流+净现金变化", symbol)
	c = c + assert([]float64 {is.Revenue},
		[]float64{is.GrossProfit, is.CostOfRevenue},
		"总收入=毛利+成本", symbol)
	c = c + assert([]float64 {is.TotalOperatingExpenses},
		[]float64{is.ResearchAndDevelopment, is.SalesGeneralAndAdministrative, is.OtherOperatingExpenses},
		"营业成本总额=开发费用+销售、管理及行政费用+其他营业费用", symbol)
	c = c + assert([]float64 {is.IncomeBeforeTaxes, is.InterestExpense},
		[]float64{is.OperatingIncome, is.OtherIncomeExpense},
		"税前利润=营业收入+其他收入（支出）-利息支出", symbol)
	c = c + assert([]float64 {is.NetIncomeFromContinuingOperations, is.ProvisionForIncomeTaxes},
		[]float64{is.IncomeBeforeTaxes, is.OtherIncome},
		"持续经营收益=税前利润-所得税费用+其他收益", symbol)
	c = c + assert([]float64 {is.NetIncome},
		[]float64{is.NetIncomeFromContinuingOperations},
		"净利润=持续经营收益", symbol)
	c = c + assert([]float64 {is.NetIncomeAvailableToCommonShareholders, is.PreferredDividend},
		[]float64{is.NetIncome},
		"归属于股东的净利润=净利润-优先股利", symbol)
	c = c + assert([]float64 {is.DilutedWeightedAverageSharesOutstanding},
		[]float64{is.NetIncomeAvailableToCommonShareholders},
		"息税折旧摊销前利润=归属于股东的净利润", symbol)

	if c > 0 {
		fmt.Println("############", symbol, "&", date, "问题数:", c, "############")
	}
}

func assert(left []float64, right []float64, message string, symbol string) int {
	var sumRight float64 = 0
	for _, r := range right {
		sumRight += r
	}
	var sumLeft float64 = 0
	for _, l := range left {
		sumLeft += l
	}
	if sumLeft != sumRight {
		fmt.Println(message)
		fmt.Println("sum(",left, ")!=sum(", right, ")" )

		if v, exist := collector[message]; exist {
			collector[message] = append(v, symbol)
		} else {
			collector[message] = []string{symbol}
		}
		return 1
	}

	return 0
}

func updateFinanceReports() {
	for _, s := range companys {
		fetchFinanceReportFromXueQiu(s)
	}
}

func fetchFinanceReportFromXueQiu(symbol string) {
	countOfNewRecord := 0

	bs := &BalanceSheet{}
	doPost("finance_us_balance_sheet", symbol, bs) // financeUSBalanceSheetList
	for _, v := range bs.Array {
		if c,err := base.DBCount(dbName, tableNameBalance, bson.M{"symbol":symbol, "date":v.Date}); err == nil {
			if c == 0 {
				base.DBInsert(dbName, tableNameBalance, v)
				countOfNewRecord++
			}
		} else {
			fmt.Println("error:", err)
		}
	}

	cfs := &CashFlowStatement{}
	doPost("finance_us_cash_flow_statement", symbol, cfs) // financeUSCashFlowStatementList
	for _, v := range cfs.Array {
		if c,err := base.DBCount(dbName, tableNameCashFlow, bson.M{"symbol":symbol, "date":v.Date}); err == nil {
			if c == 0 {
				base.DBInsert(dbName, tableNameCashFlow, v)
				countOfNewRecord++
			}
		} else {
			fmt.Println("error:", err)
		}
	}

	is := &IncomeStatement{}
	doPost("finance_us_income_statement", symbol, is) // financeUSIncomeStatementList
	for _, v := range is.Array {
		if c,err := base.DBCount(dbName, tableNameIncome, bson.M{"symbol":symbol, "date":v.Date}); err == nil {
			if c == 0 {
				base.DBInsert(dbName, tableNameIncome, v)
				countOfNewRecord++
			}
		} else {
			fmt.Println("error:", err)
		}
	}

	fmt.Println(symbol, " 新增记录数:", strconv.Itoa(countOfNewRecord))
}

func doPost(kind string, symbol string, ob interface{}) {
	client := &http.Client{}
	url := "https://xueqiu.com/stock/" + kind + ".json?symbol=" + symbol + "&data_type=1&dateAscType=desc&_=" + strconv.FormatInt(time.Now().Unix(), 10)

	req, err := http.NewRequest("GET", url, nil) //建立一个请求
	if err != nil {
		fmt.Println("Fatal error ", err.Error())
		os.Exit(0)
	}
	//Add 头协议
	req.Header.Add("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8")
	//req.Header.Add("Accept-Encoding", "gzip, deflate, br")
	req.Header.Add("Accept-Language", "zh-CN,zh;q=0.9,en;q=0.8")
	req.Header.Add("Connection", "keep-alive")
	req.Header.Add("Cache-Control", "max-age=0")
	req.Header.Add("Cookie", "device_id=2b009892f65ce3fad7aac38c3182f82b; s=ed11rof6wu; __utmz=1.1528696341.1.1.utmcsr=baidu|utmccn=(organic)|utmcmd=organic; aliyungf_tc=AQAAANG1eRIHUQUAyk/dco6gK4B/q3sd; Hm_lvt_1db88642e346389874251b5a1eded6e3=1535437025,1535714956; remember=1; remember.sig=K4F3faYzmVuqC0iXIERCQf55g2Y; xq_a_token=e26a52ed03c1c3a401e3bd4555badaf3ea375281; xq_a_token.sig=FpIzSe7_BsU4yk_OrZX62M8tYuI; xq_r_token=166430ed43e3990927cb8d41fe240a720692bade; xq_r_token.sig=FMuTotbSK0EGa0EN5J58ZGakp5M; xq_is_login=1; xq_is_login.sig=J3LxgPVPUzbBg3Kee_PquUfih7Q; u=3996182971; u.sig=Qz9HuIDusmV-jyOOYTWc3g0W8EQ; __utmc=1; bid=c9b0182b2e519e29a61fe1adc3e9faef_jlhx24bx; __utma=1.1495902061.1528696341.1535875771.1535898202.4; Hm_lpvt_1db88642e346389874251b5a1eded6e3=1535898664")
	req.Header.Add("Host", "xueqiu.com")
	req.Header.Add("Upgrade-Insecure-Requests", "1")
	req.Header.Add("User-Agent", "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_13_6) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/67.0.3396.99 Safari/537.36")
	response, err := client.Do(req) //提交
	defer response.Body.Close()
	cookies := response.Cookies() //遍历cookies
	for _, cookie := range cookies {
		fmt.Println("cookie:", cookie)
	}

	body, err1 := ioutil.ReadAll(response.Body)
	if err1 != nil {
		// handle error
	}

	json.Unmarshal(body, ob)
}

/*
kind:[zichanfuzhai]
 */
func doGetFromQianzhan(kind string, symbol string) {
	client := &http.Client{}
	url := "https://stock.qianzhan.com/us/" + kind + "_" + symbol + ".html"

	req, err := http.NewRequest("GET", url, nil) //建立一个请求
	if err != nil {
		fmt.Println("Fatal error ", err.Error())
		os.Exit(0)
	}
	//Add 头协议
	req.Header.Add("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8")
	//req.Header.Add("Accept-Encoding", "gzip, deflate, br")
	req.Header.Add("Accept-Language", "zh-CN,zh;q=0.9,en;q=0.8")
	req.Header.Add("Connection", "keep-alive")
	req.Header.Add("Cache-Control", "max-age=0")
	req.Header.Add("Cookie", "qznewsite.uid=ycba0izhvbscy5jrjvtz5bru; Hm_lvt_044fec3d5895611425b9021698c201b1=1537155048; qz.newsite=61844DC737539CB6E5E18C641367A52CBD8A99E177858D95EFFF41118212805BA5F44F16DC4887BB3FD1A4026B10E9ACC1BD7E7BA1A238BFBC1A2ED6F87458437FE6BFFC03A0B184F5AB483747F3ECA17C859F57C6062FEBCF184C1A05CBDC0A56ADEA4DAF78D0819C6BAFAB2A49C48BD578501682A1360BC3866E2D734FD93437228821; user.email=13770535063; Hm_lpvt_044fec3d5895611425b9021698c201b1=1537231097")
	req.Header.Add("Host", "stock.qianzhan.com")
	req.Header.Add("Upgrade-Insecure-Requests", "1")
	req.Header.Add("User-Agent", "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_13_6) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/67.0.3396.99 Safari/537.36")
	response, err := client.Do(req) //提交
	defer response.Body.Close()
	cookies := response.Cookies() //遍历cookies
	for _, cookie := range cookies {
		fmt.Println("cookie:", cookie)
	}

	body, err1 := ioutil.ReadAll(response.Body)
	if err1 != nil {
		// handle error
	}

	fmt.Println(string(body))
}

func export2CSVByGoquery(symbol string, us bool) {
	for _, k := range kindsOfReport {
		url := ""
		if us {
			url = "https://stock.qianzhan.com/us/" + k + "_" + symbol + ".html"
		} else {
			url = "https://stock.qianzhan.com/hk/" + k + "_" + symbol + ".hk.html"
		}
		doGetByGoquery(k, symbol, url)
	}
}

func doGetByGoquery(kind string, symbol string, url string) {
	records := make([]base.SM, 0)

	res, _ := http.Get(url)
	root, _ := html.Parse(res.Body)
	doc := goquery.NewDocumentFromNode(root)

	doc.Find("th").Each(func(indexOfTH int, th *goquery.Selection) {
		v := strings.TrimSpace(th.Text())

		if len(v) == 0 {
			return
		}

		sm := base.SM{}
		sm["财报时间段"] = v
		sm["财报类型"] = kind
		sm["symbol"] = symbol
		records = append(records, sm)
	})

	var nameOfAttribute = ""
	trSelections := doc.Find("#tblBody1 tr")
	trSelections.Each(func(indexOfTR int, tr *goquery.Selection) {
		tr.Find("td").Each(func(indexOfTD int, td *goquery.Selection) {
			v := strings.TrimSpace(td.Text())

			if indexOfTD == 0 {
				nameOfAttribute = v
			} else {
				records[indexOfTD - 1][nameOfAttribute] = v
			}
		})
	})

	var countOfNewRecord = 0
	for _, r := range records {
		if c,err := base.DBCount(dbName, tableNameSource, bson.M{"symbol":symbol, "财报类型":r["财报类型"], "财报时间段":r["财报时间段"]}); err == nil {
			if c == 0 {
				base.DBInsert(dbName, tableNameSource, r)
				countOfNewRecord++
			}
		} else {
			fmt.Println("error:", err)
		}
	}

	fmt.Println(symbol, ".", kind, ":count of new records:", countOfNewRecord)
}

type BalanceSheet struct {
	Array []BalanceSheetQ `json:"financeUSBalanceSheetList"`
}

type BalanceSheetQ struct {
	AccountsPayable                       float64 `json:"accounts_payable"` // 应付账款
	AccruedExpensesAndLiabilities         float64 `json:"accrued_expenses_and_liabilities"` // 预提支出及负债
	AccruedLiabilities                    float64 `json:"accrued_liabilities"` // 应计债务
	AccumulatedDepreciation               float64 `json:"accumulated_depreciation"` // 累积折旧
	AccumulatedOtherComprehensiveIncome   float64 `json:"accumulated_other_comprehensive_income"` // 累积其他综合收益
	AdditionalPaidInCapital               float64 `json:"additional_paid_in_capital"` // 资本公积
	AllowanceForLoanLosses                float64 `json:"allowance_for_loan_losses"` // 备付贷款损失
	CapitalLeases                         float64 `json:"capital_leases"` // 租赁资本
	CashAndCashEquivalents                float64 `json:"cash_and_cash_equivalents"` // 现金及现金等价物
	CashAndDueFromBanks                   float64 `json:"cash_and_due_from_banks"` // 现金及到期存款
	CommonStock                           float64 `json:"common_stock"` // 普通股
	CurrencyUnit                          string  `json:"currency_unit"`
	DataType                              int     `json:"data_type"`
	Date                                  string  `json:"date"`
	DebtSecurities                        float64 `json:"debt_securities"` // 债务证券
	DeferredIncomeTaxes                   float64 `json:"deferred_income_taxes"` // 递延税
	DeferredRevenues                      float64 `json:"deferred_revenues"` // 递延收入
	DeferredTaxes                         float64 `json:"deferred_taxes"` // 递延税金
	DeferredTaxesLiabilities              float64 `json:"deferred_taxes_liabilities"` // 递延所得税负债
	Deposits                              float64 `json:"deposits"` // 存款额
	DerivativeAssets                      float64 `json:"derivative_assets"` // 衍生资产
	DerivativeLiabilities                 float64 `json:"derivative_liabilities"` // 衍生负债
	EquityAndOtherInvestments             float64 `json:"equity_and_other_investments"` // 股票及其他投资
	FederalFundsPurchased                 float64 `json:"federal_funds_purchased"` // 联邦基金费用
	FederalFundsSold                      float64 `json:"federal_funds_sold"` // 联邦基金卖出所得
	Goodwill                              float64 `json:"goodwill"` // 商誉价值
	GrossProperty                         float64 `json:"gross_property"` // 固定资产
	IntangibleAssets                      float64 `json:" intangible_assets"` // 无形资产
	Inventories                           float64 `json:"inventories"` // 存货
	Investments                           float64 `json:"investments"` // 投资
	IsLock                                int     `json:"is_lock"`
	Loans                                 float64 `json:"loans"` // 贷款
	LongTermDebt                          float64 `json:"long_term_debt"` // 长期负债
	MinorityInterest                      float64 `json:"minority_interest"` // 少数股东权益
	NetLoans                              float64 `json:"net_loans"` // 贷款净额
	NetPropertyPlantAndEquipment          float64 `json:"net_property_plant_and_equipment"` // 固定资产总额
	NonCurrentAssets                      float64 `json:"non_current_assets"` // 长期资产
	OtherAssets                           float64 `json:"other_assets"` // 其他资产
	OtherCurrentAssets                    float64 `json:"other_current_assets"` // 其他流动资产
	OtherCurrentLiabilities               float64 `json:"other_current_liabilities"` // 其他流动负债
	OtherIntangibleAssets                 float64 `json:"other_intangible_assets"` // 其他无形资产
	OtherLiabilities                      float64 `json:"other_liabilities"` // 其他负债
	OtherLongTermAssets                   float64 `json:"other_long_term_assets"` // 其他长期资产
	OtherLongTermLiabilities              float64 `json:"other_long_term_liabilities"` // 其他长期负债
	Payables                              float64 `json:"payables"` // 应付款项
	PayablesAndAccruedExpenses            float64 `json:"payables_and_accrued_expenses"` // 应付款项及应计费用
	PreferredStock                        float64 `json:"preferred_stock"` // 优先股
	PremisesAndEquipment                  float64 `json:"premises_and_equipment"` // 厂房设施与设备
	PrepaidExpenses                       float64 `json:"prepaid_expenses"` // 预付费用
	PropertyAndEquipment                  float64 `json:"property_and_equipment"` // 机器设备
	Receivables                           float64 `json:"receivables"` // 应收账款
	RetainedEarnings                      float64 `json:"retained_earnings"` // 留存收益
	SecuritiesAndInvestments              float64 `json:"securities_and_investments"` // 证券及投资
	SecuritiesBorrowed                    float64 `json:"securities_borrowed"` // 借入证券
	ShortTermBorrowing                    float64 `json:"short_term_borrowing"` // 短期借债
	ShortTermDebt                         float64 `json:"short_term_debt"` // 短期借贷
	ShortTermInvestments                  float64 `json:"short_term_investments"` // 短期投资
	Symbol                                string  `json:"symbol"`
	TaxesPayable                          float64 `json:"taxes_payable"` // 应付税款
	TotalAssets                           float64 `json:"total_assets"` // 资产总额
	TotalCash                             float64 `json:"total_cash"` // 现金总额
	TotalCurrentAssets                    float64 `json:"total_current_assets"` // 流动资产总额
	TotalCurrentLiabilities               float64 `json:"total_current_liabilities"` // 流动负债总额
	TotalLiabilities                      float64 `json:"total_liabilities"` // 负债总额
	TotalLiabilitiesAndStockholdersEquity float64 `json:"total_liabilities_and_stockholders_equity"` // 负债和股东权益总计
	TotalNonCurrentAssets                 float64 `json:"total_non_current_assets"` // 长期资产总额
	TotalNonCurrentLiabilities            float64 `json:"total_non_current_liabilities"` // 长期负债总额
	TotalStockholdersEquity               float64 `json:"total_stockholders_equity"` // 股东权益总计
	TradingLiabilities                    float64 `json:"trading_liabilities"` // 交易负债
	TreasuryStock                         float64 `json:"treasury_stock"` // 库存股份
	UpdateTime                            int64   `json:"update_time"`
}

type CashFlowStatement struct {
	Array []CashFlowStatementQ `json:"financeUSCashFlowStatementList"`
}

type CashFlowStatementQ struct {
	AccruedLiabilities                          float64 `json:"accrued_liabilities"` // 应计债务
	AcquisitionsNet                             float64 `json:"acquisitions__net"` // 收购
	AcquisitionsAndDispositions                 float64 `json:"acquisitions_and_dispositions"` // 并购和处置
	AmortizationOfDebtAndIssuanceCosts          float64 `json:"amortization_of_debt_and_issuance_costs"` // 债务和发行成本摊销
	CapitalExpenditure                          float64 `json:"capital_expenditure"` // 资本支出
	CashAtBeginningOfPeriod                     float64 `json:"cash_at_beginning_of_period"` // 期初现金流
	CashAtEndOfPeriod                           float64 `json:"cash_at_end_of_period"` // 期末现金流
	CashFlowsFromFinancingActivities            float64 `json:"cash_flows_from_financing_activities"` // 融资活动带来的现金流
	ChangeInShortTermBorrowing                  float64 `json:"change_in_short_term_borrowing"` // 短期借款变化
	CommonStockIssued                           float64 `json:"common_stock_issued"` // 普通股发行
	CommonStockRepurchased                      float64 `json:"common_stock_repurchased"` // 普通股回购
	CurrencyUnit                                string  `json:"currency_unit"`
	Date                                        string  `json:"date"`
	DebtIssued                                  float64 `json:"debt_issued"` // 债券发行
	DebtRepayment                               float64 `json:"debt_repayment"` // 债券偿还
	DeferredTaxBenefitExpense                   float64 `json:"deferred_tax_benefit_expense"` // 递延所得税费用(收益)
	DepreciationAmortization                    float64 `json:"depreciation_amortization"` // 折旧与摊销
	DividendPaid                                float64 `json:"dividend_paid"` // 股息支付
	EffectOfExchangeRateChanges                 float64 `json:"effect_of_exchange_rate_changes"` // 汇率变动的影响
	FreeCashFlow                                float64 `json:"free_cash_flow"` // 自由现金流
	GainsLossOnDispositionOfBusinesses          float64 `json:"gains_loss_on_disposition_of_businesses"` // 业务处置利得（损失）
	IncomeTaxesPayable                          float64 `json:"income_taxes_payable"` // 应付所得税
	Inventory                                   float64 `json:"inventory"` // 存货
	InvestmentAssetImpairmentCharges            float64 `json:"investment_asset_impairment_charges"` // 投资/资产减损支出
	InvestmentsGainsLosses                      float64 `json:"investments_gains_losses"` // 投资损失（收益）
	InvestmentsInPropertyPlantAndEquipment      float64 `json:"investments_in_property_plant_and_equipment"` // 固定资产投资
	IsLock                                      float64 `json:"is_lock"`
	Loans                                       float64 `json:"loans"` // 贷款
	LongTermDebtIssued                          float64 `json:"long_term_debt_issued"` // 长期债券发行
	LongTermDebtRepayment                       float64 `json:"long_term_debt_repayment"` // 长期债券偿还
	NetCashProvidedByOperatingActivities        float64 `json:"net_cash_provided_by_operating_activities"` // 经营活动带来的净现金流
	NetCashProvidedByUsedForFinancingActivities float64 `json:"net_cash_provided_by_used_for_financing_activities"` // 融资活动带来的净现金流
	NetCashUsedForInvestingActivities           float64 `json:"net_cash_used_for_investing_activities"` // 投资活动带来的净现金流
	NetChangeInCash                             float64 `json:"net_change_in_cash"` // 净现金变化
	NetIncome                                   float64 `json:"net_income"` // 净利润
	OperatingCashFlow                           float64 `json:"operating_cash_flow"` // 营运现金流量
	OtherAssetsAndLiabilities                   float64 `json:"other_assets_and_liabilities"` // 其他资产与负债
	OtherFinancingActivities                    float64 `json:"other_financing_activities"` // 其他金融活动
	OtherInvestingActivities                    float64 `json:"other_investing_activities"` // 其他投资活动
	OtherNonCashItems                           float64 `json:"other_non_cash_items"` // 其他非现金项目
	OtherOperatingActivities                    float64 `json:"other_operating_activities"` // 其他经营活动
	OtherWorkingCapital                         float64 `json:"other_working_capital"` // 其他营运资金
	Payables                                    float64 `json:"payables"` // 应付款项
	PrepaidExpenses                             float64 `json:"prepaid_expenses"` // 预付费用
	PropertyAndEquipmentsNet                    float64 `json:"property__and_equipments_net"` // 财产和设备
	ProvisionForCreditLosses                    float64 `json:"provision_for_credit_losses"` // 信用损失计提
	PurchasesOfIntangibles                      float64 `json:"purchases_of_intangibles"` // 购买无形资产
	PurchasesOfInvestments                      float64 `json:"purchases_of_investments"` // 购买投资资产
	Receivable                                  float64 `json:"receivable"` // 应收账款
	RepurchasesOfTreasuryStock                  float64 `json:"repurchases_of_treasury_stock"` // 库存股回购
	SalesMaturitiesOfInvestments                float64 `json:"sales_maturities_of_investments"` // 债务/销售投资
	StockBasedCompensation                      float64 `json:"stock_based_compensation"` // 股权补偿
	Symbol                                      string  `json:"symbol"`
	UpdateTime                                  int64   `json:"update_time"`
}

type IncomeStatement struct {
	Array []IncomeStatementQ `json:"financeUSIncomeStatementList"`
}

type IncomeStatementQ struct {
	AmortizationOfIntangibles               float64 `json:"amortization_of_intangibles"` // 资产摊销费用
	BasicEarningsPerShare                   float64 `json:"basic_earnings_per_share"` // 基本每股收益
	BasicWeightedAverageSharesOutstanding   float64 `json:"basic_weighted_average_shares_outstanding"` // 基本加权平均股数
	CommissionsAndFees                      float64 `json:"commissions_and_fees"` // 佣金及费用支出
	CompensationAndBenefits                 float64 `json:"compensation_and_benefits"` // 薪酬福利支出
	CostOfRevenue                           float64 `json:"cost_of_revenue"` // 成本
	CurrencyUnit                            string  `json:"currency_unit"`
	DataType                                int     `json:"data_type"`
	Date                                    string  `json:"date"`
	DepreciationAndAmortization             float64 `json:"depreciation_and_amortization"` // 折旧及摊销
	DilutedEarningsPerShare                 float64 `json:"diluted_earnings_per_share"` // 摊薄每股收益
	DilutedWeightedAverageSharesOutstanding float64 `json:"diluted_weighted_average_shares_outstanding"` // 摊薄加权平均股数
	Ebitda                                  float64 `json:"ebitda"` // 息税折旧摊销前利润
	GrossProfit                             float64 `json:"gross_profit"` // 毛利
	IncomeBeforeIncomeTaxes                 float64 `json:"income_before_income_taxes"` // 所得税前利润
	IncomeBeforeTaxes                       float64 `json:"income_before_taxes"` // 税前利润
	IncomeFromDiscontinuedOperations        float64 `json:"income_from_discontinued_operations"` // 非持续经营收益
	IncomeLossFromContOpsBeforeTaxes        float64 `json:"income_loss_from_cont_ops_before_taxes"` // 税前可持续业务收益（亏损）
	IncomeTaxes                             float64 `json:"income_taxes"` // 所得税
	InsurancePremium                        float64 `json:"insurance_premium"` // 保险收益（费用）
	InterestExpense                         float64 `json:"interest_expense"` // 利息支出
	IsLock                                  int     `json:"is_lock"`
	NetIncome                               float64 `json:"net_income"` // 净利润
	NetIncomeAvailableToCommonShareholders  float64 `json:"net_income_available_to_common_shareholders"` // 归属于股东的净利润
	NetIncomeFromContinuingOperations       float64 `json:"net_income_from_continuing_operations"` // 持续经营收益
	NetInterestIncome                       float64 `json:"net_interest_income"` // 净利息收入
	NonoperatingIncome                      float64 `json:"nonoperating_income"` // 营业外收入
	NonrecurringExFpense                    float64 `json:"nonrecurring_ex_fpense"` // 一次性费用
	OperatingExpenses                       float64 `json:"operating_expenses"`
	OperatingIncome                         float64 `json:"operating_income"` // 营业收入
	OtherAssets                             float64 `json:"other_assets"` // 其他资产
	OtherExpense                            float64 `json:"other_expense"`
	OtherIncome                             float64 `json:"other_income"` // 其他收益
	OtherIncomeExpense                      float64 `json:"other_income_expense"` // 其他收入（支出）
	OtherOperatingExpenses                  float64 `json:"other_operating_expenses"` // 其他营业费用
	OtherSpecialCharges                     float64 `json:"other_special_charges"` // 其他特殊费用
	PreferredDividend                       float64 `json:"preferred_dividend"` // 优先股利
	ProvisionBenefitForTaxes                float64 `json:"provision_benefit_for_taxes"` // 备付税
	ProvisionForIncomeTaxes                 float64 `json:"provision_for_income_taxes"` // 所得税费用
	ResearchAndDevelopment                  float64 `json:"research_and_development"` // 开发费用
	Revenue                                 float64 `json:"revenue"` // 总收入
	RevenuesNetOfInterestExpense            float64 `json:"revenues_net_of_interest_expense"` // 收入，净利息费用
	SalesGeneralAndAdministrative           float64 `json:"sales_general_and_administrative"` // 销售、管理及行政费用
	SecuritiesGainsLosses                   float64 `json:"securities_gains_losses"` // 证券投资收益（亏损）
	Symbol                                  string  `json:"symbol"`
	TechCommunicationAndEquipment           float64 `json:"tech_communication_and_equipment"` // 电信及设备费用
	TotalInterestExpense                    float64 `json:"total_interest_expense"`
	TotalInterestIncome                     float64 `json:"total_interest_income"`
	TotalNetRevenue                         float64 `json:"total_net_revenue"`
	TotalNoninterestExpenses                float64 `json:"total_noninterest_expenses"`
	TotalNoninterestRevenue                 float64 `json:"total_noninterest_revenue"`
	TotalNonoperatingIncome                 float64 `json:"total_nonoperating_income"` // 营业外收入总额
	TotalOperatingExpenses                  float64 `json:"total_operating_expenses"` // 营业成本总额
	UpdateTime                              int64   `json:"update_time"`
}
