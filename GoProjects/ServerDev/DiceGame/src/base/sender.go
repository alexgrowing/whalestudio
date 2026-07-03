package base

import "encoding/json"

// MessageSender2Client MessageSender2Client
type MessageSender2Client interface {
	Send2Client(message *DGBytesMessage)
	UniqueIDOfSender() string
	Shutdown()
}

// DGBytesMessage DGBytesMessage
type DGBytesMessage struct {
	OriginalMessage map[string]interface{}
	bytesEncoded    []byte
}

// NewBytesMessage NewBytesMessage
func NewBytesMessage(message map[string]interface{}) *DGBytesMessage {
	bytesMess := DGBytesMessage{}
	bytesMess.OriginalMessage = message

	return &bytesMess
}

// GetEncodedBytes GetEncodedBytes
func (me *DGBytesMessage) GetEncodedBytes() ([]byte, error) {
	if me.bytesEncoded == nil {
		bytes, err := json.Marshal(me.OriginalMessage)
		if err == nil {
			me.bytesEncoded = bytes
		} else {
			return bytes, err
		}
	}

	return me.bytesEncoded, nil
}
