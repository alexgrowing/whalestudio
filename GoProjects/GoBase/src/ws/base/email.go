package base

import (
	"encoding/base64"
	"net/mail"
	"fmt"
	"net/smtp"
	"regexp"
)

func SendEmail(subject string, body string, toEmail string) error {
	b64 := base64.NewEncoding("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")
	host := "smtpdm.aliyun.com"
	email := "noreply@whalestudio.cn"
	password := "RgdP9yy4bJxy"
	from := mail.Address{"鲸鱼工作室", email}
	to := mail.Address{"尊贵的用户", toEmail}
	header := make(map[string]string)
	header["From"] = from.String()
	header["To"] = to.String()
	header["Subject"] = fmt.Sprintf("=?UTF-8?B?%s?=", b64.EncodeToString([]byte(subject)))
	header["MIME-Version"] = "1.0"
	header["Content-Type"] = "text/html; charset=UTF-8"
	header["Content-Transfer-Encoding"] = "base64"
	message := ""
	for k, v := range header {
		message += fmt.Sprintf("%s: %s\r\n", k, v)
	}
	message += "\r\n" + b64.EncodeToString([]byte(body))
	auth := smtp.PlainAuth(
		"",
		email,
		password,
		host,
	)

	return smtp.SendMail(
		host + ":80",
		auth,
		email,
		[]string{to.Address},
		[]byte(message),
	)
}

func SendVerifyCode(code string, toEmail string) error {
	return SendEmail("验证码:" + code, "验证码:" + code, toEmail)
}

func ValidateFormatOfEmail(email string) bool {
	match, _ := regexp.MatchString("^[A-Za-z\\d]+([-_.][A-Za-z\\d]+)*@([A-Za-z\\d]+[-.])+[A-Za-z\\d]{2,4}$", email)

	return match
}

func ValidatePasswordStrength(password string) bool {
	if match, _ := regexp.MatchString("^[0-9]+$", password); match {
		return false
	}
	if match, _ := regexp.MatchString("^[a-zA-Z]+$", password); match {
		return false
	}

	match, _ := regexp.MatchString("^[0-9A-Za-z]{8,20}$", password)

	return match
}