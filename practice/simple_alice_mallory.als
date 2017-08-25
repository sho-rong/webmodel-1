open util/ordering[Time]

/***********************

Network Component

***********************/
abstract sig NetworkEndpoint{}
abstract sig HTTPConformist extends NetworkEndpoint{}
sig HTTPServer extends HTTPConformist{}
abstract sig HTTPClient extends HTTPConformist{
  owner:WebPrincipal // owner of the HTTPClient process
}
sig Browser extends HTTPClient {}

fact ReqAndResMaker{
	no req:HTTPRequest | req.from in HTTPServer
	no req:HTTPRequest | req.to in HTTPClient
	no res:HTTPResponse | res.from in HTTPClient
	no res:HTTPResponse | res.to in HTTPServer
}

/***********************

Event

***********************/
abstract sig Event {current : one Time}

abstract sig NetworkEvent extends Event {
	from: NetworkEndpoint,
	to: NetworkEndpoint
}

abstract sig HTTPEvent extends NetworkEvent {}

sig HTTPRequest extends HTTPEvent {}
sig HTTPResponse extends HTTPEvent {}

/***********************

Token

************************/
sig Time {}

fact Traces{
	all t:Time | one e:Event | t = e.current
}

/***********************

Network Character

***********************/
abstract sig Principal {
	servers : set NetworkEndpoint,
}

abstract sig PassivePrincipal extends Principal{}{
	servers in HTTPConformist
}

abstract sig WebPrincipal extends PassivePrincipal {}

sig ACTIVEATTACKER extends Principal{}	//GadgetAttacker
sig PASSIVEATTACKER extends PassivePrincipal{}	//WebAttacker
sig WEBATTACKER extends WebPrincipal{}	//NetworkAttacker

sig Alice extends WebPrincipal {}
sig Mallory extends WEBATTACKER {}

/****************************

Test Code

****************************/
run test_alice{
	//one HTTPRequest
	//one HTTPResponse

	one HTTPClient
	one HTTPServer

	one Alice
	one Mallory

	all s:HTTPServer | s in Mallory.servers
	all c:HTTPClient | c in Alice.servers
} for 2
