open util/ordering[Time]

abstract sig Principal {
	servers : set NetworkEndpoint,
}

//異なるプリンシパルは同じDNS、同じサーバを持たない
fact DNSIsDisjointAmongstPrincipals {
	all disj p1,p2 : Principal | no (p1.servers & p2.servers)
}

sig Time {}
sig Token {}

pred happensBeforeOrdering[first:Event,second:Event]{
	second.current in first.current.*next
}

fact Traces{
	all t:Time | one e:Event | t = e.current
}

sig NetworkEndpoint{}

abstract sig Event {current : Time}

abstract sig NetworkEvent extends Event {
    from: NetworkEndpoint,
    to: NetworkEndpoint
}

abstract sig HTTPConformist extends NetworkEndpoint{}
sig HTTPServer extends HTTPConformist{cache : lone PublicCache}
abstract sig HTTPClient extends HTTPConformist{
  owner:WebPrincipal // owner of the HTTPClient process
}
sig Browser extends HTTPClient {cache : lone PrivateCache}

abstract sig HTTPHeader {}
abstract sig HTTPResponseHeader extends HTTPHeader{}
abstract sig HTTPRequestHeader extends HTTPHeader{}
abstract sig HTTPGeneralHeader extends HTTPHeader{}
abstract sig HTTPEntityHeader extends HTTPHeader{}
abstract sig Status  {}
abstract sig RedirectionStatus extends Status {}

fact noOrphanedHeaders {
	all h:HTTPRequestHeader|some req:HTTPRequest|h in req.headers
	all h:HTTPResponseHeader|some resp:HTTPResponse|h in resp.headers
	all h:HTTPGeneralHeader|some req:HTTPRequest, resp:HTTPResponse|h in req.headers or h in resp.headers
	all h:HTTPEntityHeader|some req:HTTPRequest, resp:HTTPResponse|h in req.headers or h in resp.headers
}

abstract sig HTTPEvent extends NetworkEvent {
	headers: set HTTPHeader,
	host : Origin,
	uri : one Token
}

sig HTTPRequest extends HTTPEvent {
	body :  set Token
}

sig HTTPResponse extends HTTPEvent {
	statusCode : Status,
	reuse: lone CacheStatus
}

enum CacheStatus{OK, NG}

fact reusePossibility{
	all res:HTTPResponse |
		res in Cache.stored implies #(res.reuse)=1
		else #(res.reuse)=0
}

fact ReqToRes{
	all req:HTTPRequest | some res:HTTPResponse | req.uri = res.uri and res.current in req.current.*next
	all res:HTTPResponse | some req:HTTPRequest | req.uri = res.uri and req.current in (Time - res.current.*next)
}

lone sig c301,c302,c303,c304,c305,c306,c307 extends RedirectionStatus {}
lone sig c200,c401 extends Status{}

sig HTTPTransaction {
	req : HTTPRequest,
	resp : lone HTTPResponse,
	cause : lone HTTPTransaction
}{
	some resp implies {
		happensBeforeOrdering[req,resp]
	}
}

fact CauseHappensBeforeConsequence  {
	all t1: HTTPTransaction | some (t1.cause) implies
	       some t0:HTTPTransaction | (t0 in t1.cause and happensBeforeOrdering[t0.resp, t1.req])
}

fun getTrans[e:HTTPEvent]:HTTPTransaction{
	(req+resp).e
}

lone sig Alice extends WebPrincipal {}
lone sig Mallory extends WEBATTACKER {}

sig Origin {}

fact HTTPTransactionsAreSane {
	all disj t,t':HTTPTransaction | no (t.resp & t'.resp ) and no (t.req & t'.req)
}

/****************************

HTTPServer Definitions

****************************/
lone sig ACTIVEATTACKER extends Principal{}

//Passive Principals match their http / network parts
abstract sig PassivePrincipal extends Principal{}{
	servers in HTTPConformist
}

lone sig PASSIVEATTACKER extends PassivePrincipal{}
sig WebPrincipal extends PassivePrincipal {
  httpClients : set HTTPClient
} { httpClients.owner = this }

//HTTPAdherent so that it can make requests too
lone sig WEBATTACKER extends WebPrincipal{}

abstract sig NormalPrincipal extends WebPrincipal{}
lone sig GOOD extends NormalPrincipal{}
lone sig SECURE extends NormalPrincipal{}
lone sig ORIGINAWARE extends NormalPrincipal{}

fact NormalPrincipalsDontMakeRequests {
	no aReq:HTTPRequest | aReq.from in NormalPrincipal.servers
}

/****************************

Cache Definitions

****************************/
sig PragmaHeader extends HTTPRequestHeader{}
/*
sig IfModifiedSinceHeader extends HTTPRequestHeader{modified: one Time}
sig IfNoneMatchHeader extends HTTPRequestHeader{etag: one Int}
sig ETagHeader extends HTTPResponseHeader{etag: one Int}
sig LastModifiedHeader extends HTTPResponseHeader{modified: one Int}
sig AgeHeader extends HTTPResponseHeader{age : one Int}{age > 0}
sig CacheControlHeader extends HTTPGeneralHeader{options : set CacheOption}
sig DateHeader extends HTTPGeneralHeader{date: one Int}{
	date > 0
}
*/

sig IfModifiedSinceHeader extends HTTPRequestHeader{}
sig IfNoneMatchHeader extends HTTPRequestHeader{}
sig ETagHeader extends HTTPResponseHeader{}
sig LastModifiedHeader extends HTTPResponseHeader{}
sig AgeHeader extends HTTPResponseHeader{}
sig CacheControlHeader extends HTTPGeneralHeader{options : set CacheOption}
sig DateHeader extends HTTPGeneralHeader{}

sig ConnectionHeader extends HTTPGeneralHeader{next: one HTTPConformist}
sig WarningHeader extends HTTPGeneralHeader{}
//sig ExpiresHeader extends HTTPEntityHeader{expire: one Int}{expire > 0}
sig ExpiresHeader extends HTTPEntityHeader{}

/*
fact limitDateHeader{
	all disj e1,e2 :HTTPEvent |
		(one d:DateHeader | d in e1.headers) and (one d:DateHeader | d in e2.headers) and (e1.current in e2.current.*next) implies
			all disj d1,d2 :DateHeader |
				{
					d1 in e1.headers
					d2 in e2.headers
					d1.date > d2.date
				}
}
*/

abstract sig CacheOption{}
abstract sig RequestCacheOption extends CacheOption{}
abstract sig ResponseCacheOption extends CacheOption{}
sig NoCache,NoStore,NoTransform extends CacheOption{}
sig OnlyIfCached extends RequestCacheOption{}
//sig MaxStale,MinStale extends RequestCacheOption{time: one Int}
sig MaxStale,MinStale extends RequestCacheOption{}
sig MustRevalidate,Public,Private,ProxyRevalidate extends ResponseCacheOption{}
//sig Maxage,SMaxage extends ResponseCacheOption{time: one Int}
sig Maxage,SMaxage extends ResponseCacheOption{}

abstract sig HTTPIntermediary extends HTTPConformist{}
sig HTTPProxy extends HTTPIntermediary{}
sig HTTPGateway extends HTTPIntermediary{}

abstract sig Cache{
	stored: set HTTPResponse,
	//current: one Int,
	/*reqtime: one Int,
	restime: one Int*/
}{
	//current > 0
	/*reqtime > 0
	restime > 0
	#stored  = 1 implies current > restime and restime > reqtime*/

	#stored>0 implies no NoStore	//for NoStore
	#stored>0 implies #AgeHeader>0
}

sig PrivateCache extends Cache{}{
	all res:HTTPResponse |
		res in stored implies
			(some op:Maxage | op in HTTPResponse.headers.options) or
			(some d:DateHeader, e:ExpiresHeader | d in HTTPResponse.headers and e in HTTPResponse.headers)

	/*
	#stored>0 and #(HTTPResponse -> Maxage)>0 implies	//for Maxage
		getExpiration[HTTPResponse.headers.age, HTTPResponse.headers.date, Maxage.time, restime, reqtime, current] > 0


	#stored>0 and #(HTTPResponse -> ExpiresHeader)>0 and #(HTTPResponse -> Maxage)=0 implies	//for ExpiresHeader and DateHeader
		getExpiration[HTTPResponse.headers.age, HTTPResponse.headers.date, ExpiresHeader.expire.minus[DateHeader.date], restime, reqtime, current] > 0
	*/
}

sig PublicCache extends Cache{}{
	no res:HTTPResponse |
		res in stored implies
			no h:CacheControlHeader | h in res.headers and (Private in h.options)

	all res:HTTPResponse |
		res in stored implies
			(some op:SMaxage | op in HTTPResponse.headers.options) or
			(some op:Maxage | op in HTTPResponse.headers.options) or
			(some d:DateHeader, e:ExpiresHeader | d in HTTPResponse.headers and e in HTTPResponse.headers)

	/*
	#stored>0 and #(HTTPResponse -> SMaxage)>0 implies	//for SMaxage
		getExpiration[HTTPResponse.headers.age, HTTPResponse.headers.date, SMaxage.time, restime, reqtime, current] > 0

	#stored>0 and #(HTTPResponse -> Maxage)>0 and #(HTTPResponse -> SMaxage)=0 implies	//for Maxage
		getExpiration[HTTPResponse.headers.age, HTTPResponse.headers.date, Maxage.time, restime, reqtime, current] > 0

	#stored>0 and #(HTTPResponse -> ExpiresHeader)>0 and  #(HTTPResponse -> SMaxage)=0 and #(HTTPResponse -> Maxage)=0 implies	//for ExpiresHeader and DateHeader
		getExpiration[HTTPResponse.headers.age, HTTPResponse.headers.date, ExpiresHeader.expire.minus[DateHeader.date], restime, reqtime, current] > 0
	*/
}

fact noOrphanedCaches {
	all c:Cache |
		some e:NetworkEndpoint | c = e.cache
}

fact noMultipleCaches {
	no disj e1, e2:NetworkEndpoint | e1.cache = e2.cache
}

/*
fact reuseCache{
	all req:HTTPRequest |
		some res:HTTPResponse |
			res.uri = req.uri and res in Cache.stored implies
				one reuse_res:HTTPResponse |
					(one h:CacheControlHeader | h in res.headers and (one op:Maxage | op in h.options) and (one op:SMaxage | op in h.options)) or (one e:ExpiresHeader | e in res.headers) implies
						checkExpiration[res] implies
							{
								copyResponse[reuse_res, res]
								reuse_res.current in res.current.*next
							}
						else
							{
								validationResponse[reuse_res] implies
									{
										//
									}
								else
									{
										//
									}
							}
}
*/

pred copyResponse[tar:HTTPResponse, res:HTTPResponse]{
	tar.headers = res.headers
	tar.host = res.host
	tar.uri = res.uri
	tar.statusCode = res.statusCode
	tar.from = res.from
	tar.to = res.to
}

pred checkExpiration[res:HTTPResponse]{
	res.reuse = OK
}

pred validationResponse[res:HTTPResponse]{
	/*

	*/
}

/*
fun getExpiration[A:Int, D:Int, E:Int, restime:Int, reqtime:Int, current:Int]:Int{	//calculate expiration date
	let apparent = (restime.minus[D] > 0 implies restime.minus[D] else 0), corrected = A.plus[restime.minus[reqtime]] |
		let initial = (apparent > corrected implies apparent else corrected) |
			E.minus[initial.plus[current.minus[restime]]]
}

fun getExpiration[expiration:Int, res:HTTPResponse]:Int{	//calculate expiration date
	let age = res.headers.age, date = res.headers.date, restime =
}
*/

fact LimitHeader{
	all h:HTTPHeader | h in HTTPResponse.headers or h in HTTPRequest.headers
	all c:CacheOption | c in CacheControlHeader.options
	no res:HTTPResponse, req:HTTPRequest | res.headers = req.headers
	no resoption:ResponseCacheOption | resoption in HTTPRequest.headers.options
	no reqoption:RequestCacheOption | reqoption in HTTPResponse.headers.options
	all res:HTTPResponse | some h:DateHeader | res in Cache.stored and h in res.headers
	all res:HTTPResponse | some h:ExpiresHeader | res in Cache.stored and h in res.headers
	all res:HTTPResponse | some h:AgeHeader | res in Cache.stored and h in res.headers
}

run show{
	#PublicCache = 1
	#PrivateCache = 0
	#Cache.stored = 1
}

/*
fact validation[res:HTTPResponse]{
	{
		res.headers and ETagHeader implies
			//make conditional request
			one req:HTTPRequest |
				{
					req.current in res.current.*next
					req.uri = res.uri
					req.headers and IfNoneMatchHeader
					req.etag = res.etag
				}
	}
}
*/
