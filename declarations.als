open util/ordering[Time]

/***********************

DNS

************************/

sig DNS{
	parent : DNS + DNSRoot,	//ドメインの各部を所持
	resolvesTo : set NetworkEndpoint
}{
// A DNS Label resolvesTo something
//1つ以上のNetworkEndpointに接続
	some resolvesTo
}

//定数:DNSroot
one sig DNSRoot {}

//全てのDNSについて、自身からたどれるparentの集合に自身は含まれない
fact dnsIsAcyclic {
	 all x: DNS | x !in x.^parent
//	 all x:dns-dnsRoot | some x.parent
}

// s is  a subdomain of d
//sのparentをたどるとdが存在する⇔sがdのサブドメインである
pred isSubdomainOf[s: DNS, d: DNS]{
   //e.g. .stanford.edu is a subdomain of .edu
  d in s.*parent
}

//PrincipalはNetworkEndpointと対応するDNSを持つ
abstract sig Principal {
// without the -HTTPClient the HTTPS check fails
	servers : set NetworkEndpoint,
	dnslabels : set DNS,
}

//DNSから対象のPrincipalを取得
fun getPrincipalFromDNS[dns : DNS]:Principal{
	dnslabels.dns
}

//Originから対象のPrincipalを取得
fun getPrincipalFromOrigin[o: Origin]:Principal{
	getPrincipalFromDNS[o.dnslabel]
}

//異なるプリンシパルは同じDNS、同じサーバを持たない
fact DNSIsDisjointAmongstPrincipals {
	all disj p1,p2 : Principal | (no (p1.dnslabels & p2.dnslabels)) and ( no (p1.servers & p2.servers))
//The servers disjointness is a problem for virtual hosts. We will replace it with disjoint amongst attackers and trusted people or something like that
}

// turn this on for intermediate checks
// run show {} for 6



/***********************

Items

************************/

sig Time {}

fact Traces{
	all t:Time | one e:Event | t = e.current
}

abstract sig Token {}
//秘匿情報 作成者、期限を持つ
abstract sig Secret extends Token {
	madeBy : Principal,
	expiration : one Int,
}

sig Uri{}
//使用されないURIは存在しない
fact noOrphanedUri{
	all u:Uri | some e:HTTPEvent | u = e.uri
}

sig URL {path:Path, host:Origin}

//時系列に従ったモデルの考察
// second.pre >= first.post
pred happensBefore[first:Event,second:Event]{
	second.current in first.current.*next
}

abstract sig Method {}
one sig GET extends Method {}
one sig PUT  extends Method {}
one sig POST extends Method {}
one sig DELETE extends Method {}
one sig OPTIONS extends Method {}

fun safeMethods[]:set Method {
	GET+OPTIONS
}

abstract sig Status  {}
abstract sig RedirectionStatus extends Status {}
lone sig c301,c302,c303,c304,c305,c306,c307 extends RedirectionStatus {}
lone sig c200,c401 extends Status{}

/***********************

Network component

************************/

sig NetworkEndpoint{cache : lone Cache}

// we don't make HTTPServer abstract, it will be defined by the owner

abstract sig HTTPConformist extends NetworkEndpoint{}
sig HTTPServer extends HTTPConformist{}
abstract sig HTTPClient extends HTTPConformist{
  owner:WebPrincipal // owner of the HTTPClient process
}
sig Browser extends HTTPClient {
	trustedCA : set certificateAuthority
}

/*sig InternetExplorer extends Browser{}
sig InternetExplorer7 extends InternetExplorer{}
sig InternetExplorer8 extends InternetExplorer{}
sig Firefox extends Browser{}
sig Firefox3 extends Firefox {}
sig Safari extends Browser{}*/



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

abstract sig NormalPrincipal extends WebPrincipal{} { 	dnslabels.resolvesTo in servers}
lone sig GOOD extends NormalPrincipal{}
lone sig SECURE extends NormalPrincipal{}
lone sig ORIGINAWARE extends NormalPrincipal{}

fact NonActiveFollowHTTPRules {
// Old rule was :
//	all t:HTTPTransaction | t.resp.from in HTTPServer implies t.req.host.server = t.resp.from
// We rewrite to say HTTPAdherents cant spoof from part ... here we don't say anything about principal
	all httpresponse:HTTPResponse | httpresponse.from in HTTPConformist implies httpresponse.from in httpresponse.host.dnslabel.resolvesTo
}

fact SecureIsHTTPSOnly {
// Add to this the fact that transaction schema is consistent
	all httpevent:HTTPEvent | httpevent.from in SECURE.servers implies httpevent.host.schema = HTTPS
//	STS Requirement : all sc : ScriptContext | some (getPrincipalFromOrigin[sc.owner] & SECURE ) implies sc.transactions.req.host.schema=HTTPS
}

fact CSRFProtection {
	all aResp:HTTPResponse | aResp.from in ORIGINAWARE.servers and aResp.statusCode=c200 implies {
		(resp.aResp).req.method in safeMethods or (
		let theoriginchain = ((resp.aResp).req.headers & OriginHeader).theorigin |
			some theoriginchain and theoriginchain.dnslabel in ORIGINAWARE.dnslabels
		)
	}
}

fact NormalPrincipalsHaveNonTrivialDNSValues {
// Normal Principals don't mess around with trivial DNS values
   DNSRoot !in NormalPrincipal.dnslabels.parent
}

fact WebPrincipalsObeyTheHostHeader {
	all aResp:HTTPResponse |
		let p = servers.(aResp.from) |
			p in WebPrincipal implies {
				//the host header a NormalPrincipal Sets is always with the DNSLabels it owns
				aResp.host.dnslabel in p.dnslabels
				// it also makes sure that the from server is the same one that the dnslabel resolvesTo
				aResp.from in aResp.host.dnslabel.resolvesTo

				//additionally it responds to some request and keep semantics similar to the way Browsers keep them
				some t:HTTPTransaction | t.resp = aResp and t.req.host.dnslabel = t.resp.host.dnslabel and t.req.host.schema = t.resp.host.schema
			}
}

fact NormalPrincipalsDontMakeRequests {
	no aReq:HTTPRequest | aReq.from in NormalPrincipal.servers
}



/***********************************

Client Definitions

************************************/
// Each user is associated with a set of network locations
// from where they use their credentials
pred isAuthorizedAccess[user:WebPrincipal, loc:NetworkEndpoint]{
  loc in user.httpClients
}

/*fun smartClient[]:set Browser {
  Firefox3 + InternetExplorer8
}*/

// Ideally want tp use the old Principals thing

sig WWWAuthnHeader extends HTTPResponseHeader{}{
  all resp:HTTPResponse| (some (WWWAuthnHeader & resp.headers)) => resp.statusCode=c401
}


// each user has at most one password
sig UserPassword extends UserToken { }

// sig AliceUserPassword extends UserPassword {} {id = Alice and madeBy in Alice }

pred somePasswordExists {
  some UserPassword //|p.madeBy in Alice
}

//run somePasswordExists for 8


pred basicModelIsConsistent {
  some ScriptContext
  some t1:HTTPTransaction |{
    some (t1.req.from & Browser ) and
    some (t1.resp)
  }
}



/***********************

Event

************************/

abstract sig Event {current : one Time}

abstract sig NetworkEvent extends Event {
    from: NetworkEndpoint,
    to: NetworkEndpoint
}

abstract sig HTTPEvent extends NetworkEvent {
	headers: set HTTPHeader,
	host : Origin,
	uri: one Uri
}

sig HTTPRequest extends HTTPEvent {
  // host + path == url
	method: Method,
	path : Path,
	queryString : set attributeNameValuePair,  // URL query string parameters
	body :  set Token
}

sig HTTPResponse extends HTTPEvent {
	statusCode : Status
}

abstract sig CacheEvent extends Event {
	happen: one Cache,
	target: one HTTPResponse
}
sig CacheStore extends CacheEvent {}
sig CacheReuse extends CacheEvent {}
sig CacheVerification extends CacheEvent {}

//CacheStoreの発生条件
fact happenCacheStore{
	all store:CacheStore | one res:HTTPResponse | {
		//レスポンスが直前にやりとりされている
		happensBefore[res, store]
		//e.current = res.current.next
		store.target = res
		store.happen = res.to.cache

		//レスポンスのヘッダ条件
		store.happen in PrivateCache implies {	//for PrivateCache
			(one op:Maxage | op in res.headers.options) or
			(one d:DateHeader, e:ExpiresHeader | d in res.headers and e in res.headers)
		}else{	//for PublicCache
			(one op:Maxage | op in res.headers.options) or
			(one op:SMaxage | op in res.headers.options) or
			(one d:DateHeader, e:ExpiresHeader | d in res.headers and e in res.headers)

			no op:Private | op in res.headers.options
		}
		one h:AgeHeader | h in res.headers
	}
}

//CacheReuseの発生条件
fact happenCacheReuse{
	all reuse:CacheReuse | one store:CacheStore, req:HTTPRequest |{
		//応答するリクエストに対する条件
		happensBefore[req, reuse]
		reuse.target.uri = req.uri

		//過去の格納イベントに対する条件
		happensBefore[store, reuse]
		reuse.target = store.target
	}
}

//検証イベントの流れ
//CacheVerification -> HTTPRequest -> HTTPResponse -> CacheStore/HTTPResponse
fact happenCacheVerification{
	all veri:CacheVerification | {
		//応答するリクエストに対する条件
		one req:HTTPRequest |{
			happensBefore[req, veri]
			veri.target.uri = req.uri
		}

		//過去の格納イベントに対する条件
		one store:CacheStore | {
			happensBefore[store, veri]
			veri.target = store.target
			(one h:ETagHeader | h in veri.target.headers) or (one h:LastModifiedHeader | h in veri.target.headers)
		}

		//条件付リクエストの生成
		one req:HTTPRequest | {
			//リクエストの基本情報設定
			happensBefore[veri, req]
			one p:NetworkEndpoint | {
				p.cache = veri.happen
				req.from = p
			}
			req.to = veri.target.from
			req.uri = veri.target.uri

			//リクエストのヘッダ設定
			((one h:ETagHeader | h in veri.target.headers) implies (one h:IfNoneMatchHeader | h in req.headers)) or
			((one h:LastModifiedHeader | h in veri.target.headers) implies (one h:IfModifiedSinceHeader | h in req.headers))

			one h:HTTPHeader | {
				h in req.headers
				h in IfNoneMatchHeader + IfModifiedSinceHeader
			}

			//条件付リクエストへの応答
			one res:HTTPResponse | {
				happensBefore[veri, res]
				res.from = req.to
				res.to = req.from
				(res.statusCode = c200) or (res.statusCode = c304)	//200:新しいレスポンスを使用, 304:レスポンスを再利用

				//検証結果に対する動作（再利用 or 新レスポンス）
				(res.statusCode = c200) implies
					one reuse:CacheReuse | {
						happensBefore[veri, reuse]
						//reuse.current = veri.current.next.next.next
						reuse.target = veri.target
					}

				(res.statusCode = c304) implies
					one res_result:HTTPResponse | {
						happensBefore[veri, res_result]
						//res_result.current = veri.current.next.next.next
						res_result.uri = res.uri
						res_result.from = res.from
						one req:HTTPRequest | {
							req.current.next = veri.current
							res_result.to = req.from
						}
					}
			}
		}
	}
}



/***********************

Headers

************************/

abstract sig HTTPHeader {}
abstract sig HTTPResponseHeader extends HTTPHeader{}
abstract sig HTTPRequestHeader extends HTTPHeader{}
abstract sig HTTPGeneralHeader extends HTTPHeader{}
abstract sig HTTPEntityHeader extends HTTPHeader{}

sig IfModifiedSinceHeader extends HTTPRequestHeader{}
sig IfNoneMatchHeader extends HTTPRequestHeader{}
sig ETagHeader extends HTTPResponseHeader{}
sig LastModifiedHeader extends HTTPResponseHeader{}
sig AgeHeader extends HTTPResponseHeader{}
sig CacheControlHeader extends HTTPGeneralHeader{options : set CacheOption}
sig DateHeader extends HTTPGeneralHeader{}
sig ExpiresHeader extends HTTPEntityHeader{}

abstract sig CacheOption{}
abstract sig ResponseCacheOption extends CacheOption{}
sig NoCache,NoStore,NoTransform extends CacheOption{}
sig Maxage,SMaxage,Private,Public extends ResponseCacheOption{}

fact noOrphanedHeaders {
	all h:HTTPRequestHeader|one req:HTTPRequest|h in req.headers
	all h:HTTPResponseHeader|one resp:HTTPResponse|h in resp.headers
	all h:HTTPGeneralHeader|one e:HTTPEvent | h in e.headers
	all h:HTTPEntityHeader|one e:HTTPEvent | h in e.headers
	all c:CacheOption | c in CacheControlHeader.options
}



/***********************

Caches

************************/

abstract sig Cache{}
sig PrivateCache extends Cache{}
sig PublicCache extends Cache{}

//どの端末にも属さないキャッシュは存在しない
fact noOrphanedCaches {
	all c:Cache |
		one e:NetworkEndpoint | c = e.cache
}

//同じ端末に2つ以上のキャッシュは存在しない
fact noMultipleCaches {
	no disj e1, e2:NetworkEndpoint | e1.cache = e2.cache
}

// Browsers run a scriptContext
sig ScriptContext {
	owner : Origin,
	location : Browser,
	transactions: set HTTPTransaction
}{
// Browsers are honest, they set the from correctly
	transactions.req.from = location
}

//sig location extends HTTPResponseHeader {targetOrigin : Origin, targetPath : Path}
// The name location above easily conflicts with other attributes and variables with the same name.
// We should follow the convention of starting type names with a capital letter.
// Address this in later clean-up.

sig attributeNameValuePair { name: Token, value: Token}

sig LocationHeader extends HTTPResponseHeader {
  targetOrigin : Origin,
  targetPath : Path,
  params : set attributeNameValuePair  // URL request parameters
}

abstract sig RequestAPI{} // extends Event


sig HTTPTransaction {
	req : HTTPRequest,
	resp : lone HTTPResponse,
	cert : lone Certificate,
	cause : lone HTTPTransaction + RequestAPI
}{
	some resp implies {
		//response can come from anyone but HTTP needs to say it is from correct person and hosts are the same, so schema is same
		resp.host = req.host
		happensBefore[req,resp]
	}

	req.host.schema = HTTPS implies some cert and some resp
	some cert implies req.host.schema = HTTPS

}

fact CauseHappensBeforeConsequence  {
	all t1: HTTPTransaction | some (t1.cause) implies {
       (some t0:HTTPTransaction | (t0 in t1.cause and happensBefore[t0.resp, t1.req]))
       or (some r0:RequestAPI | (r0 in t1.cause ))
       // or (some r0:RequestAPI | (r0 in t1.cause and happensBefore[r0, t1.req]))
    }
}

fun getTrans[e:HTTPEvent]:HTTPTransaction{
	(req+resp).e
}

fun getScriptContext[t:HTTPTransaction]:ScriptContext {
		transactions.t
}

fun getContextOf[request:HTTPRequest]:Origin {
	(transactions.(req.request)).owner
}

pred isCrossOriginRequest[request:HTTPRequest]{
		getContextOf[request].schema != request.host.schema or
		getContextOf[request].dnslabel != request.host.dnslabel
}

// moved CORS to a separate file cors.alf for modularization

/************************************
* CSRF
*
************************************/
// RFC talks about having Origin Chain and not a single Origin
// We handle Origin chain by having multiple Origin Headers
sig OriginHeader extends HTTPRequestHeader {theorigin: Origin}


fun getFinalResponse[request:HTTPRequest]:HTTPResponse{
        {response : HTTPResponse | not ( response.statusCode in RedirectionStatus) and response in ((req.request).*(~cause)).resp}
}

pred isFinalResponseOf[request:HTTPRequest, response : HTTPResponse] {
       not ( response.statusCode in RedirectionStatus)
       response in ((req.request).*(~cause)).resp
}

//enum Port{P80,P8080}
enum Schema{HTTP,HTTPS}
sig Path{}
sig INDEX,HOME,SENSITIVE, PUBLIC, LOGIN,LOGOUT,REDIRECT extends Path{}
sig PATH_TO_COMPROMISE extends SENSITIVE {}

// sig User extends WebPrincipal { }

lone sig Alice extends WebPrincipal {}
lone sig Mallory extends WEBATTACKER {}

sig Origin {
//	port: Port,
	schema: Schema,
	dnslabel : DNS,
}

abstract sig certificateAuthority{}
one sig BADCA,GOODCA extends certificateAuthority{}

sig Certificate {
	ca : certificateAuthority,
	cn : DNS,
	ne : NetworkEndpoint
}{

	//GoodCAVerifiesNonTrivialDNSValues
	ca in GOODCA and cn.parent != DNSRoot implies
			some p:Principal | {
				cn in p.dnslabels
				ne in p.servers
				ne in cn.resolvesTo
			}
}

/****************************
Cookie Stuff
****************************/
// Currently the String type is taken but not yet implemented in Alloy
// We will replace String1 with String when the latter is fully available in Alloy
sig String1 {}

sig UserToken extends Secret {
        id : WebPrincipal
}

sig Cookie extends Secret {
	name : Token,
	value : Token,
	domain : DNS,
	path : Path,
}{}

sig SecureCookie extends Cookie {}

sig CookieHeader extends HTTPRequestHeader{ thecookie : Cookie }
sig SetCookieHeader extends HTTPResponseHeader{	thecookie : Cookie }

fact SecureCookiesOnlySentOverHTTPS{
		all e:HTTPEvent,c:SecureCookie | {
				e.from in Browser + NormalPrincipal.servers
				httpPacketHasCookie[c,e]
		} implies e.host.schema=HTTPS

}

fact CookiesAreSameOriginAndSomeOneToldThemToTheClient{
	all areq:HTTPRequest |{
			areq.from in Browser
			some ( areq.headers & CookieHeader)
	} implies  all acookie :(areq.headers & CookieHeader).thecookie | some aresp: location.(areq.from).transactions.resp | {
				//don't do same origin check as http cookies can go over https
				aresp.host.dnslabel = areq.host.dnslabel
				acookie in (aresp.headers & SetCookieHeader).thecookie
				happensBefore[aresp,areq]
	}
}

pred httpPacketHasCookie[c:Cookie,httpevent:HTTPRequest+HTTPResponse]{
				(httpevent in HTTPRequest and  c in (httpevent.headers & CookieHeader).thecookie ) or
				(httpevent in HTTPResponse and c in (httpevent.headers & SetCookieHeader).thecookie)
}

pred hasKnowledgeViaUnencryptedHTTPEvent[c: Cookie, ne : NetworkEndpoint, usageEvent: Event]{
		ne !in WebPrincipal.servers + Browser
		some httpevent : HTTPEvent | {
			happensBefore[httpevent,usageEvent]
			httpevent.host.schema = HTTP
			httpPacketHasCookie[c,httpevent]
		}
}

pred hasKnowledgeViaDirectHTTP[c:Cookie,ne:NetworkEndpoint,usageEvent:Event]{
		some t: HTTPTransaction | {
		happensBefore[t.req,usageEvent]
		httpPacketHasCookie[c,t.req]
		t.resp.from = ne
	} or {
		happensBefore[t.resp,usageEvent]
		httpPacketHasCookie[c,t.resp]
		some ((transactions.t).location & ne)
		}
}

pred hasKnowledgeCookie[c:Cookie,ne:NetworkEndpoint,usageEvent:Event]{
	ne in c.madeBy.servers or hasKnowledgeViaUnencryptedHTTPEvent[c,ne,usageEvent] or hasKnowledgeViaDirectHTTP[c,ne,usageEvent]
}

fact BeforeUsingCookieYouNeedToKnowAboutIt{
	all e:HTTPRequest + HTTPResponse |
// Use httpPacketHasCookie
			all c:(e.(HTTPRequest <: headers) & CookieHeader).thecookie + (e.(HTTPResponse <: headers) & SetCookieHeader).thecookie |
					hasKnowledgeCookie[c,e.from,e]
}

fact NormalPrincipalsOnlyUseCookiesTheyMade{
	all e:HTTPResponse |
		all c:(e.headers & SetCookieHeader).thecookie | {
			e.from in NormalPrincipal.servers implies c.madeBy = e.from[servers]
		}
}

fact NormalPrincipalsDontReuseCookies{
	all p:NormalPrincipal | no disj e1,e2:HTTPResponse | {
			(e1.from + e2.from) in p.servers
			some ( 	(e1.headers & SetCookieHeader).thecookie & (e2.headers & SetCookieHeader).thecookie )
	}
}

/*
run show2 {
	some (SetCookieHeader).thecookie
} for 6
*/

/***********************

HTTP Facts

************************/
fact scriptContextsAreSane {
	all disj sc,sc':ScriptContext | no (sc.transactions & sc'.transactions)
	all t:HTTPTransaction | t.req.from in Browser implies t in ScriptContext.transactions
}


fact HTTPTransactionsAreSane {
	all disj t,t':HTTPTransaction | no (t.resp & t'.resp ) and no (t.req & t'.req)
}

//run basicModelIsConsistent  for 8 but 3 HTTPResponse//, 3 HTTPRequest,

// run findBasicModelInstance  for 6  but 2 HTTPResponse,
//2 HTTPRequest, 2 RequestAPI, 0 GOOD, 0 SECURE ,2 Secret, 0 String1
//1 ACTIVEATTACKER, 1 WEBATTACKER, 1 ORIGINAWARE,
//, 2  Origin,

run show{
	#HTTPResponse = 1
	#HTTPRequest = 1
	#CacheStore = 1
	#Event = 3
}
