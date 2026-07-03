package tool

import (
	"crypto/md5"
	"crypto/rand"
	"encoding/base64"
	"encoding/hex"
	"io"
)

func GenerateUUID() string {
	bytes := make([]byte, 48)
	if _, err := io.ReadFull(rand.Reader, bytes); err != nil {
		return ""
	}
	return "LAND[" + md5Encode(base64.URLEncoding.EncodeToString(bytes)) + "]"
}

func md5Encode(in string) string {
	h := md5.New()
	h.Write([]byte(in))
	return hex.EncodeToString(h.Sum(nil))
}
