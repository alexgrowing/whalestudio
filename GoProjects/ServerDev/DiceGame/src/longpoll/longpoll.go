package longpoll

import (
	"time"
	"strconv"
	"log"
	"net/http"
	"sync"
	"ws/base"
)

func RegisterListener(listener Listener) {
	globalSession.listener = listener
}

func CreateSessionID() string {
	return globalSession.createSessionID()
}

func Poll(sid string, w http.ResponseWriter) {
	if !globalSession.validateSessionID(sid) {
		const_POLL_INVALID_SID.ZipWrite(w)
	}

	if messageChan := globalSession.registerSenderBySessionID(sid); messageChan != nil {
		select {
		case message := <-messageChan:
			w.Header().Set("content-type", "application/json")

			w.Write(message)
		case <-time.After(time.Duration(const_TIME_OUT_OF_ASK_FOR_RELOOP) * time.Second):
			globalSession.unregisterSenderBySessionID(sid)
			const_POLL_TIME_OUT_LOOP.ZipWrite(w)
		}
	} else {
		const_POLL_INVALID_SID.ZipWrite(w)
	}
}

func TestSendMessage(sid string) {
	ret := base.SM{}
	ret["time"] = time.Now()
	globalSession.sendMessageBySessionID(sid, ret.AsBytes())
}

func SessionsAlive() base.SM {
	ret := base.SM{}

	ret["nextID"] = globalSession.nextSessionID
	ret["countOfAliveSessions"] = len(globalSession.all)

	smOfSessions := make([]base.SM, 0)
	for sid, infor := range globalSession.all {
		smOfSessions = append(smOfSessions, base.SM{
			"sid":sid,
			"created":time.Now().Sub(infor.whenCreated).String(),
			"lastActive":time.Now().Sub(infor.whenLastActive).String(),
		})
	}

	ret["sessions"] = smOfSessions

	return ret
}

const const_TIME_OUT_OF_CLIENT_LOST_CONNECTION = 30 // 服务器端长时间拿不到客户端请求的Pool
const const_TIME_OUT_OF_ASK_FOR_RELOOP = 5          // 为了防止客户端认为timeout了,就发个信息给客户端让其reloop
const const_TIMES_OF_TRYING_TO_SEND_MESSAGE = 3

//const const_POLL_TIME_OUT_LOOP = "{\"LOOP\":true}"
//const const_POLL_INVALID_SID = "{\"LOOP\":false}"
var const_POLL_TIME_OUT_LOOP = base.SM{"LOOP":true}
var const_POLL_INVALID_SID = base.SM{"LOOP":false}

type sessionIDInfor struct {
	sid         string
	messageChan chan []byte
	lifeChan    chan bool
	waiting4NewLoop bool

	whenCreated time.Time
	whenLastActive time.Time

	sendMessageLock *sync.Mutex
}

func (self *sessionIDInfor) registerSender() {
	// 因为启动lifeChan需要另起一个线程,所以需要用一个变量【waiting4NewLoop】标识lifeChan是否已经启动
	if self.waiting4NewLoop {
		self.waiting4NewLoop = false
		self.messageChan = make(chan []byte)

		self.lifeChan <- true // to stop timer bomb
	} else {
		log.Println("sleep to register sender")

		time.Sleep(time.Duration(1) * time.Second)
		self.registerSender()
	}
}

func (self *sessionIDInfor) unregisterSender() {
	self.messageChan = nil

	// 另起一个线程运行activateTimer,因为这个方法会阻塞线程
	go func() {
		self.waiting4NewLoop = true

		select {
		case <-self.lifeChan:
			break
		case <-time.After(time.Duration(const_TIME_OUT_OF_CLIENT_LOST_CONNECTION) * time.Second):
			globalSession.destroySessionIDInfor(self)
		}
	}()
}

/*
 * return if message send successfully
 */
func (self *sessionIDInfor) sendMessage(message []byte) bool {
	self.sendMessageLock.Lock()
	defer self.sendMessageLock.Unlock()

	return  self.privateSendMessage(message, 1)
}

func (self *sessionIDInfor) privateSendMessage(message []byte, timesOfTrying int) bool {
	if self.messageChan != nil {
		mchan := self.messageChan

		self.unregisterSender()

		self.whenLastActive = time.Now()
		mchan <- message

		return true
	} else if timesOfTrying > const_TIMES_OF_TRYING_TO_SEND_MESSAGE {
		return false
	} else {
		//log.Println(self.sid, ":Sleep ", timesOfTrying * 2, " second 4 message channel to client")
		time.Sleep(time.Duration(timesOfTrying * 2) * time.Second)
		return self.privateSendMessage(message, timesOfTrying + 1)
	}
}

type session struct {
	nextSessionID uint64
	all           map[string]*sessionIDInfor
	listener Listener
}

func (self *session) createSessionID() string {
	newID := self.nextSessionID
	self.nextSessionID++
	newInfor := sessionIDInfor{}

	newStringID := strconv.FormatUint(newID, 10)
	newInfor.sid = newStringID

	newInfor.lifeChan = make(chan bool)
	newInfor.whenCreated = time.Now()
	newInfor.whenLastActive = time.Now()
	newInfor.sendMessageLock = new(sync.Mutex)

	newInfor.unregisterSender()

	self.all[newStringID] = &newInfor
	return newStringID
}

/*
 * return if message is sent successfully
 */
func (self *session) sendMessageBySessionID(sid string, message []byte) {
	if infor, ok := self.all[sid]; ok {
		if !infor.sendMessage(message) {
			log.Println("before destroy:" + string(message));
			self.destroySessionIDInforBySid(sid)
		}
	}
}

func (self *session) registerSenderBySessionID(sid string) chan []byte {
	infor, ok := self.all[sid]
	if ok {
		infor.registerSender()

		return infor.messageChan
	}

	return nil
}

func (self *session) unregisterSenderBySessionID(sid string) {
	infor, ok := self.all[sid]
	if ok {
		infor.unregisterSender()
	}
}

func (self *session) validateSessionID(sid string) bool {
	_, ok := self.all[sid]
	return ok
}

func (self *session) destroySessionIDInforBySid(sid string) {
	if _, ok := self.all[sid]; ok {
		delete(self.all, sid)
		self.listener.OnSessionIDDestroyed(sid)
	}
}

/*
func stack() string {
	var buf [2 << 10]byte
	return string(buf[:runtime.Stack(buf[:], true)])
}
*/

func (self *session) destroySessionIDInfor(infor *sessionIDInfor) {
	self.destroySessionIDInforBySid(infor.sid)
}

func initializeGlobalSession() *session {
	session := session{}
	session.nextSessionID = 156732
	session.all = make(map[string]*sessionIDInfor)

	return &session
}

var globalSession = initializeGlobalSession()

type Listener interface {
	OnSessionIDDestroyed(sid string)
}