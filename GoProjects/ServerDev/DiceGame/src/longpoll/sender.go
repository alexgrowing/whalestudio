package longpoll

import (
	"base"
)

type SessionMessageSender2Client struct {
	SessionID string
}

/*
 * return if message is sent successfully
 */
func (self *SessionMessageSender2Client) Send2Client(message *base.DGBytesMessage) {

	bytes, err := message.GetEncodedBytes()
	if err == nil {
		globalSession.sendMessageBySessionID(self.SessionID, bytes)
	}
}

func (self *SessionMessageSender2Client) UniqueIDOfSender() string {
	return self.SessionID
}

func (self *SessionMessageSender2Client) Shutdown() {
	globalSession.destroySessionIDInforBySid(self.SessionID)
}

