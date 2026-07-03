package base

import (
	"bytes"
	"compress/gzip"
	"encoding/json"
	"log"
	"net/http"
	"time"
	"crypto/md5"
	"crypto/rand"
	"encoding/base64"
	"encoding/hex"
	"io"
	"strconv"
	mrand "math/rand"
)

type SM map[string]interface{}

var server_start_time = time.Now()
var length_of_output_bytes = int64(0)

var randomGenerator = mrand.New(mrand.NewSource(time.Now().UnixNano()))

func CreateRandomInt(maxI int) int {
	return randomGenerator.Intn(maxI)
}

func ReadLengthOfOutputBytes() int64 {
	return length_of_output_bytes
}

func ReadServerStartTime() time.Time {
	return server_start_time
}

func LengthOfBytesAsString(lengthOfBytes int64) string {
	var lengthOfB int64 = 0
	var lengthOfK int64 = 0
	var lengthOfM int64 = 0
	var lengthOfG int64 = 0

	lengthOfB = lengthOfBytes
	if lengthOfB >= 1024 {
		lengthOfK = lengthOfB / 1024
		lengthOfB = lengthOfB % 1024
	}
	if lengthOfK >= 1024 {
		lengthOfM = lengthOfK / 1024
		lengthOfK = lengthOfK % 1024
	}
	if lengthOfM >= 1024 {
		lengthOfG = lengthOfM / 1024
		lengthOfM = lengthOfM % 1024
	}

	return strconv.FormatInt(lengthOfG, 10) + "G" + strconv.FormatInt(lengthOfM, 10) + "M" + strconv.FormatInt(lengthOfK, 10) + "K" + strconv.FormatInt(lengthOfB, 10) + "B"
}

func (self SM) MarkErrorMessage(message string) {
	self["error"] = message
}

func (self SM) MarkAsSuccess() {
	self["success"] = "OK"
}

func (self SM) Write(w http.ResponseWriter) {
	w.Header().Set("content-type", "application/json;charset=utf-8")

	if bytes, err := json.Marshal(self); err == nil {
		w.Write(bytes)
		length_of_output_bytes = length_of_output_bytes + int64(len(bytes))
	} else {
		log.Fatal(err.Error())
	}
}

func (self SM) ZipWrite(w http.ResponseWriter) {
	w.Header().Set("content-type", "application/json;charset=utf-8")
	w.Header().Set("content-encoding", "gzip")

	if bytesOfSource, err := json.Marshal(self); err == nil {
		var buf bytes.Buffer

		gzipWriter := gzip.NewWriter(&buf)

		gzipWriter.Write(bytesOfSource)
		gzipWriter.Flush()
		gzipWriter.Close()

		compressedBytes := buf.Bytes()

		/*
			if gzipReader, err := gzip.NewReader(&buf); err == nil {
				log.Println("gunzip")
				defer gzipReader.Close()

				if undatas, err := ioutil.ReadAll(gzipReader); err == nil {
					log.Println("gunzip.size:", len(undatas))
				} else {
					log.Println("gunzip error:", err)
				}
			}
		*/
		w.Write(compressedBytes)
		length_of_output_bytes = length_of_output_bytes + int64(len(compressedBytes))
	} else {
		log.Fatal(err.Error())
	}
}

func (self SM) AsBytes() []byte {
	if bytes, err := json.Marshal(self); err == nil {
		return bytes
	}

	return []byte{}
}

func UniqueId() string {
	b := make([]byte, 48)

	if _, err := io.ReadFull(rand.Reader, b); err != nil {
		return ""
	}
	return GetMd5String(base64.URLEncoding.EncodeToString(b))
}

//生成32位md5字串
func GetMd5String(s string) string {
	h := md5.New()
	h.Write([]byte(s))
	return hex.EncodeToString(h.Sum(nil))
}