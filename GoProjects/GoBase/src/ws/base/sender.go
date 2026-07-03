package base

import "encoding/json"

type MessageSender2Client interface {
	Send2Client(message *DGBytesMessage)
	UniqueIDOfSender() string
}

type DGBytesMessage struct {
	OriginalMessage map[string]interface{}
	bytesEncoded    []byte
}

func NewBytesMessage(message map[string]interface{}) *DGBytesMessage {
	bytesMess := DGBytesMessage{}
	bytesMess.OriginalMessage = message

	return &bytesMess
}

func (self *DGBytesMessage) GetEncodedBytes() ([]byte, error) {
	if self.bytesEncoded == nil {
		bytes, err := json.Marshal(self.OriginalMessage)
		if err == nil {
			self.bytesEncoded = bytes
		} else {
			return bytes, err
		}
	}

	return self.bytesEncoded, nil
}