open util/ordering[Time]

sig Token{}
sig Time{}

fact Traces{
	all t:Time | one e:Event | t = e.current
}

abstract sig Event {current : Time}
abstract sig HTTPEvent extends Event {uri : one Token}
sig HTTPRequest extends HTTPEvent{}
sig HTTPResponse extends HTTPEvent{}

fact ReqToRes{
	all req:HTTPRequest | some res:HTTPResponse | req.uri = res.uri and res.current in req.current.*next
	all res:HTTPResponse | some req:HTTPRequest | req.uri = res.uri and req.current in (Time - res.current.*next)
}

run {
	#HTTPRequest = 1
}
