open util/ordering[Time]

/***********************

Network Component

***********************/
abstract sig NetworkEndpoint{}
abstract sig HTTPConformist extends NetworkEndpoint{cache : lone Cache}
sig HTTPServer extends HTTPConformist{}
abstract sig HTTPClient extends HTTPConformist{
	owner:WebPrincipal // owner of the HTTPClient process
}
sig Browser extends HTTPClient {
}

abstract sig HTTPIntermediary extends HTTPConformist{}
sig HTTPProxy extends HTTPIntermediary{}
sig HTTPGateway extends HTTPIntermediary{}

fact MoveOfIntermediary{
	all tr:HTTPTransaction |{
		tr.request.to in HTTPIntermediary and one tr.response implies{	//応答を行う場合、その応答を得る別のトランザクションがリクエストとレスポンスの間に存在する
			some tr':HTTPTransaction |{
				//tr.req -> tr'.req -> tr'.res -> tr.res
				tr'.request.current in tr.request.current.*next
				tr.response.current in tr'.response.current.*next

				//通常のユーザ + WEBATTACKERが所有する中継者のふるまい
				tr.request.to in WebPrincipal.servers implies{
					tr'.request.from = tr.request.to
					tr'.request.uri = tr.request.uri
					tr.response.body = tr'.response.body
					tr.response.statusCode = tr'.response.statusCode
				}
			}
		}
	}
}

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

abstract sig HTTPEvent extends NetworkEvent {
	headers: set HTTPHeader,
	uri: one Uri,
	body: set Token
}

sig HTTPRequest extends HTTPEvent {
}
sig HTTPResponse extends HTTPEvent {
	statusCode: one Status
}
sig CacheReuse extends NetworkEvent{target: one HTTPResponse}

//firstがsecondよりも前に発生しているか確認
pred happensBefore[first:Event,second:Event]{
	second.current in first.current.next.*next
}

//HTTPResponseの発生条件
fact happenResponse{
	all res:HTTPResponse | one req:HTTPRequest |{
		//レスポンスに対する条件
		happensBefore[req, res]
		res.uri = req.uri
		res.from = req.to
		res.to = req.from

		//HTTPTransactionに登録
		one t:HTTPTransaction | t.request = req and t.response = res

		//所属するTransactionはただ一つ
		one tr:HTTPTransaction | res = tr.response
	}
}

//CacheReuseの発生条件
fact happenCacheReuse{
	all reuse:CacheReuse | one str:StateTransaction |
		{
			happensBefore[reuse.target, reuse]

			str.re_res = reuse
			reuse.to = str.request.from
			reuse.from in str.request.(from + to)

			some pre, post:CacheState |
				(post in str.afterState and JustBeforeState[pre, post, str]) implies
					{
						reuse.target in pre.dif.store
						reuse.from.cache = pre.eq.cache
					}

			reuse.target.uri = str.request.uri
		}
}

//ある再利用を行うトランザクションでレスポンス時点で検証済みか判定
pred checkVerification[str:StateTransaction]{
	one str.re_res	//再利用で応答している

	//検証を行っているトランザクションが成立している
	some str':StateTransaction |	//tr': 検証を行うトランザクション
	{
		str' != str
		one str'.response	//検証のレスポンスが存在する

		str'.request.current in str.request.current.*next	//tr.request => tr'.request
		str.re_res.current in str'.response.current.*next	//tr'.response => tr.reuse

		str'.request.from = str.re_res.from
		str'.request.to = str.re_res.target.from
		str'.request.uri = str.request.uri

		//検証可能なレスポンスがtr.request時点で格納されている
		some tar_res:HTTPResponse |
		{
			tar_res.uri = str.request.uri

			//検証対象のレスポンスがtr.request時点で格納されている
			one cs:CacheState |
			{
				cs in str.beforeState
				cs.eq.cache = str.re_res.from.cache
				tar_res in cs.dif.store
			}

			//検証対象のレスポンスに必要なヘッダが含まれている
			some h:HTTPHeader |
			{
				h in ETagHeader + LastModifiedHeader
				h in tar_res.headers
			}

			//格納レスポンスのヘッダに適した条件付きリクエストのヘッダを生成
			(some h:ETagHeader | h in tar_res.headers) implies	//格納レスポンスがETagHeaderを持っていた場合、IfNoneMatchHeaderを付けて送信
				(some h:IfNoneMatchHeader | h in str'.request.headers)
			(some h:LastModifiedHeader | h in tar_res.headers) implies	//格納レスポンスがLastModifiedHeaderを持っていた場合、IfModifiedSinceHeaderを付けて送信
				(some h:IfModifiedSinceHeader | h in str'.request.headers)
		}

	}
}

//条件付きリクエストのトランザクション
fact ConditionalRequestTransaction{
	all tr:HTTPTransaction |
		(some h:HTTPHeader | h in IfNoneMatchHeader + IfModifiedSinceHeader and h in tr.request.headers) implies
		{
			//検証後はそのURIに対する格納レスポンスはただ一つ
			one res:HTTPResponse |
			{
				res.uri = tr.response.uri
				one cs:CacheState |
				{
					res in cs.dif.store
					cs.eq.cache = tr.request.from.cache
					cs in tr.afterState
				}
			}

			//レスポンスの状態コード
			tr.response.statusCode in c200 + c304

			//再利用不可(c200)である場合、検証結果のレスポンスが格納される（既に格納済みであったレスポンスはすべて削除される）
			tr.response.statusCode = c200 implies
			{
				all cs:CacheState |
					(cs in tr.afterState and cs.eq.cache = tr.response.to.cache) implies
						tr.response in cs.dif.store
			}

			//再利用可(c304)である場合、検証結果のレスポンスは格納されない（既に格納済みであったレスポンスのうち一つが残る）
			tr.response.statusCode = c304 implies
			{
				all cs:CacheState |
					(cs in tr.afterState and cs.eq.cache = tr.response.to.cache) implies
						tr.response !in cs.dif.store
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
abstract sig RequestCacheOption extends CacheOption{}
abstract sig ResponseCacheOption extends CacheOption{}
sig Maxage,NoCache,NoStore,NoTransform extends CacheOption{}
sig MaxStale,MinStale,OnlyIfCached extends RequestCacheOption{}
sig MustRevalidate,Public,Private,ProxyRevalidate,SMaxage extends ResponseCacheOption{}

//どのリクエスト・レスポンスにも属さないヘッダは存在しない
//各ヘッダは適切なリクエスト・レスポンスに属する
//どのCacheControlヘッダにも属さないCacheOptiionは存在しない
fact noOrphanedHeaders {
	all h:HTTPRequestHeader|some req:HTTPRequest|h in req.headers
	all h:HTTPResponseHeader|some resp:HTTPResponse|h in resp.headers
	all h:HTTPGeneralHeader|some e:HTTPEvent | h in e.headers
	all h:HTTPEntityHeader|some e:HTTPEvent | h in e.headers
	all c:CacheOption | c in CacheControlHeader.options
	all c:RequestCacheOption | c in HTTPRequest.headers.options
	all c:ResponseCacheOption | c in HTTPResponse.headers.options
}

//CacheControlHeaderのオプションに関する制限
fact CCHeaderOption{
	//for "no-cache"
	all str:StateTransaction |
		(some op:NoCache | op in (str.request.headers.options + str.re_res.target.headers.options)) implies
			some str.re_res implies
				checkVerification[str]

	//for "no-store"
	all res:HTTPResponse |
		(some op:NoStore | op in res.headers.options) implies
			all cs:CacheState | res !in cs.dif.store

	/*
	//for only-if-cached
	all req:HTTPRequest | (some op:OnlyIfCached | op in req.headers.options) implies {
		some reuse:CacheReuse | {
			happensBefore[req, reuse]
			reuse.target.uri = req.uri
			reuse.to = req.from
		}
	}
	*/

	//for "private"
	all res:HTTPResponse |
		(some op:Private | op in res.headers.options) implies
			all cs:CacheState | res in cs.dif.store implies cs.eq.cache in PrivateCache
}

/****************************

Cache

****************************/
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
	all ep:NetworkEndpoint | lone c:Cache | c in ep.cache
}

//PrivateCacheとPrivateCacheの場所の制限
fact PublicAndPrivate{
	all pri:PrivateCache | pri in HTTPClient.cache
	all pub:PublicCache | (pub in HTTPServer.cache) or (pub in HTTPIntermediary.cache)
}

sig CacheState extends State{}{
	eq in CacheEqItem
	dif in CacheDifItem

	eq.cache in PrivateCache implies
        all res:HTTPResponse | res in dif.store implies
                {
                    (one op:Maxage | op in res.headers.options) or
                    (one d:DateHeader, e:ExpiresHeader | d in res.headers and e in res.headers)
                }

    eq.cache in PublicCache implies
        all res:HTTPResponse | res in dif.store implies
                {
                    (one op:Maxage | op in res.headers.options) or
                    (one op:SMaxage | op in res.headers.options) or
                    (one d:DateHeader, e:ExpiresHeader | d in res.headers and e in res.headers)
                }

    all res:HTTPResponse | res in dif.store implies
        one h:AgeHeader | h in res.headers
}
sig CacheEqItem extends EqItem{cache: one Cache}
sig CacheDifItem extends DifItem{store: set HTTPResponse}

//同じ内容のCacheEqItem, CacheDifItemは統合される
fact noMultipleItems{
	no disj i,i':CacheEqItem | i.cache = i'.cache
	no disj i,i':CacheDifItem | i.store = i'.store
}

//キャッシュを持つ端末を含むTransaction => StateTransactionである
//すべてのStateTransactionは、リクエストのfrom/toに含まれるキャッシュの状態をbeforeStateに持つ
//すべてのStateTransactionは、レスポンスor再利用を持つ場合、beforeStateで状態を持っているキャッシュの状態をafterStateに持つ
fact CacheInTransaction{
	all tr:HTTPTransaction |
		(some tr.request.(from + to).cache implies tr in StateTransaction)

	all str:StateTransaction |{
		str.beforeState.eq.cache = str.request.(from + to).cache
		some str.(request + re_res) implies str.afterState.eq.cache = str.beforeState.eq.cache
	}
}

fact flowCacheState{
	//初期状態のstoreをnullにする
	all cs:CacheState |
		FirstState[cs] implies
			no cs.dif.store

	//直前のキャッシュの状態を継承する（responseの場合はそれを格納可能）
	all pre, post:CacheState, str:StateTransaction |
		JustBeforeState[pre, post, str] implies {
			post in str.beforeState implies post.dif.store in pre.dif.store
			post in str.afterState implies post.dif.store in (pre.dif.store + str.response)
		}
}


/***********************

Token

************************/
sig Time {}

fact Traces{
	all t:Time | one e:Event | t = e.current
}

sig Token {}

sig Uri{}

//使用されないURIは存在しない
fact noOrphanedUri{
	all u:Uri | some e:HTTPEvent | u = e.uri
}

//レスポンスの状態コード
abstract sig Status  {}
abstract sig RedirectionStatus extends Status {}

lone sig c200,c401 extends Status{}
lone sig c301,c302,c303,c304,c305,c306,c307 extends RedirectionStatus {}


/***********************

HTTPServer Definitions

***********************/
abstract sig Principal {
// without the -HTTPClient the HTTPS check fails
	servers : set NetworkEndpoint,
}

//Passive Principals match their http / network parts
abstract sig PassivePrincipal extends Principal{}{
	servers in HTTPConformist
}

abstract sig WebPrincipal extends PassivePrincipal {
	httpClients : set HTTPClient
}{
	all c:HTTPClient | c in httpClients implies c.owner = this
}

sig Alice extends WebPrincipal {}

sig ACTIVEATTACKER extends Principal{}
sig PASSIVEATTACKER extends PassivePrincipal{}
sig WEBATTACKER extends WebPrincipal{}


/************************

HTTPTransaction

************************/
sig HTTPTransaction {
	request : one HTTPRequest,
	response : lone HTTPResponse,
	re_res : lone CacheReuse,
}{
	some response implies {
		happensBefore[request,response]
	}

	some re_res implies {
		happensBefore[request, re_res]
	}
}

fact limitHTTPTransaction{
	all req:HTTPRequest | lone t:HTTPTransaction | t.request = req
	all res:HTTPResponse | lone t:HTTPTransaction | t.response = res
	all reuse:CacheReuse | lone t:HTTPTransaction | t.re_res = reuse
	no t:HTTPTransaction |
		some t.response and some t.re_res
}


/***********************

State

************************/
abstract sig State{
	flow: set State,
	eq: one EqItem,
	dif: one DifItem,
	current: set Time
}

//同じeqをもつ => 同じbefore/afterStateに存在しない
//同じeq,difを持つStateは存在しない
fact noMultipleState{
	all str:StateTransaction |
		all disj s,s':CacheState |
			s.eq = s'.eq implies
				{
					s in str.beforeState implies s' !in str.beforeState
					s in str.afterState implies s' !in str.afterState
				}

	no disj s,s':State |{
		s.eq = s'.eq
		s.dif = s'.dif
	}
}

abstract sig EqItem{}
abstract sig DifItem{}

sig StateTransaction extends HTTPTransaction{
	beforeState: set State,
	afterState: set State
}

//すべてのStateは、どこかのbefore/afterStateに属する
//すべてのStateTransactionは、before/afterStateにStateを持つ
//使用されていないEq/DifItemは存在しない
fact noOrphanedStates{
	all s:State | s in StateTransaction.(beforeState + afterState)
	all str:StateTransaction | some str.(beforeState + afterState)
	all i:EqItem | i in State.eq
	all i:DifItem | i in State.dif
}

//flowに関する条件
fact catchStateFlow{
	all pre,post:State, str:StateTransaction |
		JustBeforeState[pre, post, str] implies
			post in pre.flow
	all s,s':State |
		s' in s.flow implies
			(some str:StateTransaction | JustBeforeState[s, s', str])
}

//StateがbeforeStateに属する <=> Stateがリクエストの時間を持つ
//StateがafterStateに属する <=> Stateがレスポンスの時間を持つ
fact StateCurrentTime{
	all s:State |
		all str:StateTransaction |
			{
				s in str.beforeState iff str.request.current in s.current
				s in str.afterState iff str.(response + re_res).current in s.current
			}

	all t:Time |
		t in State.current implies t in StateTransaction.(request + response + re_res).current
}

//preがpostの直前の状態か確認
pred JustBeforeState[pre:State, post:State, str:StateTransaction]{
	pre.eq = post.eq
	post in str.(beforeState + afterState)

	some t,t':Time |
		{
			//t:pre, t':post
			//pre->post
			t in pre.current
			t' in str.(request + response + re_res).current
			t' in str.request.current implies post in str.beforeState
			t' in str.(response + re_res).current implies post in str.afterState
			t' in t.next.*next

			all s:State, t'':Time |
				(s.eq = pre.eq and t'' in s.current) implies	//t'':s
						(t in t''.*next) or (t'' in t'.*next)	//s => pre (or) post => cs
		}
}

//sが初期状態か確認
pred FirstState[s:State]{
	all s':State |
		s.eq = s'.eq implies
			s'.current in s.current.*next	//s => s'
}


/***********************

Test Code

************************/
//レスポンスを格納
run test_store{
	#HTTPClient = 1
	#HTTPServer = 1

	#HTTPRequest = 1
	#HTTPResponse = 1

	some CacheState.dif.store
} for 2

//2つのレスポンスを同時に格納
run test_store2{
	#NetworkEndpoint = 2
	#HTTPClient = 1
	#HTTPServer = 1

	#HTTPRequest = 2
	#HTTPResponse = 2

	some cs:CacheState | #(cs.dif.store) = 2
} for 4

//再利用を観測
run test_reuse{
	#HTTPClient = 1
	#HTTPServer = 1
	#Cache = 1

	#HTTPRequest = 2
	#HTTPResponse = 1
	#CacheReuse = 1
} for 4

//検証を観測
run test_verification{
	#HTTPClient = 1
	#HTTPServer = 1
	#HTTPIntermediary = 0
	#Cache = 1
	#PrivateCache = 1

	some str:StateTransaction | checkVerification[str]
} for 6

//"private"オプションの効果を確認
//No instance found で正常
run checkPrivateOption{
	all c:Cache | c in PublicCache
	some CacheState.dif.store
	all res:HTTPResponse | one op:Private | op in res.headers.options
}

//"no-store"オプションの効果を確認
//No instance found で正常
run checkNoStoreOption{
	some CacheState.dif.store
	all res:HTTPResponse | one op:NoStore | op in res.headers.options
}

//"no-cache"オプションの効果を確認
//No instance found で正常
run checkNoCacheOption{
	some str:StateTransaction |
	{
		some op:NoCache | op in str.request.headers.options
		one str.re_res
	}

	no str:StateTransaction | checkVerification[str]
}

//same orgin BCP Attack
run test_bcp{
	#HTTPClient = 1
	#HTTPServer = 1
	#HTTPIntermediary = 1
	#PrivateCache = 1
	#PublicCache = 0

	#HTTPRequest = 3
	#HTTPResponse = 2
	#CacheReuse = 1

	#Principal = 3
	#Alice = 2
	#PASSIVEATTACKER = 1

	some tr,tr',tr'':HTTPTransaction | {
		//tr.req => tr'.req => tr'.res => tr.res => tr''.req => tr''.reuse
		tr'.request.current in tr.request.current.*next
		tr.response.current in tr'.response.current.*next
		tr''.request.current in tr.response.current.*next
		some tr''.re_res

		//tr: client <-> intermediary
		tr.request.from in HTTPClient
		tr.request.to in HTTPIntermediary

		//tr': intermediary <-> server
		tr'.request.from in HTTPIntermediary
		tr'.request.to in HTTPServer

		//tr'': client <-> ?
		tr''.request.from in HTTPClient

		tr.response.body != tr'.response.body
	}

	some c:HTTPClient | c in Alice.httpClients
	some s:HTTPServer | s in Alice.servers
	no i:HTTPIntermediary | i in Alice.servers
} for 6
