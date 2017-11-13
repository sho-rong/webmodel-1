open util/ordering[Time]

/***********************

Network Component

***********************/
abstract sig Principal {}
abstract sig NetworkEndpoint{cache : lone Cache}
abstract sig HTTPConformist extends NetworkEndpoint{}
sig HTTPServer extends HTTPConformist{}
abstract sig HTTPClient extends HTTPConformist{}
sig Browser extends HTTPClient {}

abstract sig HTTPIntermediary extends HTTPConformist{}
sig HTTPProxy extends HTTPIntermediary{}
sig HTTPGateway extends HTTPIntermediary{}

fact MoveOfServer{
	//条件付きリクエストに対する動作
	all tr:HTTPTransaction |
		tr.request.to in HTTPServer implies
			(one h:HTTPHeader | h in IfNoneMatchHeader + IfModifiedSinceHeader and h in tr.request.headers) implies
				tr.response.statusCode in c200 + c304

}

fact MoveOfIntermediary{
	all e:HTTPEvent |{
		e.from in HTTPIntermediary implies{	//e:中継者から送信されるイベント
			one original:HTTPEvent |{	//original:中継者に向けて送信されたイベント
				happensBefore[original, e]

				e.from = original.to
				e.uri = original.uri

				original in HTTPRequest implies {
					//checkNotResponsed[original, e.current]
					e in HTTPRequest
				}

				original in HTTPResponse implies {
					e in HTTPResponse
					e.statusCode = original.statusCode
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
	body :  set Token
}

sig HTTPRequest extends HTTPEvent {}
sig HTTPResponse extends HTTPEvent {statusCode: one Status}
sig CacheReuse extends NetworkEvent{target: one HTTPResponse}

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
	}
}

//CacheReuseの発生条件
fact happenCacheReuse{
	/*all reuse:CacheReuse | one req:HTTPRequest |{
		//応答するリクエストに対する条件
		happensBefore[req, reuse]
		req.uri = reuse.target.uri
		req.from = reuse.to
		reuse.from in req.to + req.from

		//HTTPTransactionに登録 ＆ 再利用レスポンスが先にストアされている
		one tr:HTTPTransaction | {
			tr.request = req
			tr.re_res = reuse
			some cs:CacheState | {
				cs in tr.beforeState
				cs.cache = reuse.from.cache
				reuse.target in cs.store
			}
		}
	}*/

	all reuse:CacheReuse | one tr:HTTPTransaction |
		{
			tr.re_res = reuse
			reuse.to = tr.request.from
			reuse.from in tr.request.(from + to)

			reuse.target in tr.beforeState.store
			reuse.target.uri = tr.request.uri
		}
}

//firstがsecondよりも前に発生しているか確認
pred happensBefore[first:Event,second:Event]{
	second.current in first.current.next.*next
}

//あるトランザクションでレスポンス時点で検証済みか判定
pred checkVerification[tr:HTTPTransaction, store:HTTPResponse, p:NetworkEndpoint]{
	some tr':HTTPTransaction |
		{
			one res:HTTPResponse | res = tr'.response

			tr'.request.current in tr.request.current.*next	//tr.request -> tr'.request
			tr.response.current in tr'.response.current.*next	//tr'.response -> tr.response

			tr'.request.from = p
			tr'.request.to = store.from

			//tr'.requestが条件付きレスポンスである
			some h:HTTPHeader |
				{
					h in IfNoneMatchHeader + IfModifiedSinceHeader
					h in tr'.request.headers
				}

			//格納レスポンスのヘッダに適した条件付きリクエストのヘッダを生成
			(some h:ETagHeader | h in store.headers) implies	//格納レスポンスがETagHeaderを持っていた場合、IfNoneMatchHeaderを付けて送信
				(some h:IfNoneMatchHeader | h in tr'.request.headers)
			else (some h:LastModifiedHeader | h in store.headers) implies	//格納レスポンスがLastModifiedHeaderを持っていた場合、IfModifiedSinceHeaderを付けて送信
				(some h:IfModifiedSinceHeader | h in tr'.request.headers)
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

//for simple model
sig Maxage,NoCache,NoStore extends CacheOption{}
sig OnlyIfCached extends RequestCacheOption{}
sig Private,SMaxage extends ResponseCacheOption{}

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
	all reuse:CacheReuse |{
		(some op:NoCache | op in reuse.target.headers.options) implies {
			one tr:HTTPTransaction |
				{
					reuse = tr.re_res
					checkVerification[tr, tr.re_res.target, tr.re_res.from]
				}
		}
	}

	//for "no-store"
	all res:HTTPResponse |
		(some op:NoStore | op in res.headers.options) implies
			all cs:CacheState | res !in cs.store

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
			all cs:CacheState | res in cs.store implies cs.cache in PrivateCache
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
	all p:NetworkEndpoint | lone c:Cache | c in p.cache
}

fact PublicAndPrivate{
	all pri:PrivateCache | pri in HTTPClient.cache
	all pub:PublicCache | (pub in HTTPServer.cache) or (pub in HTTPIntermediary.cache)
}

sig CacheTransaction extends HTTPTransaction{
	beforeState: set CacheState,
	afterState: set CacheState
}{
	#beforeState <= 2
	#afterState <= 2

	beforeState.cache = request.from.cache + request.to.cache
	afterState.cache = beforeState.cache
}

sig CacheState{
	//p: set CacheState,
	cache: one Cache,
	store: set HTTPResponse,
	current: set Time
}{
    cache in PrivateCache implies
        all res:HTTPResponse | res in store implies
                {
                    (one op:Maxage | op in res.headers.options) or
                    (one d:DateHeader, e:ExpiresHeader | d in res.headers and e in res.headers)
                }

    cache in PublicCache implies
        all res:HTTPResponse | res in store implies
                {
                    (one op:Maxage | op in res.headers.options) or
                    (one op:SMaxage | op in res.headers.options) or
                    (one d:DateHeader, e:ExpiresHeader | d in res.headers and e in res.headers)
                }

    all res:HTTPResponse | res in store implies
        one h:AgeHeader | h in res.headers
}

//すべてのCacheStateはいずれかのTransactionに含まれる
fact noOrphanedCacheState{
	all cs:CacheState | cs in CacheTransaction.(beforeState + afterState)
}

//あるcs:CacheStateがtr.beforeに含まれる <=> cの時間にtr.reqが含まれる
//あるcs:CacheStateがtr.afterに含まれる <=> cの時間にtr.resが含まれる
fact CacheStateTime{
	all cs:CacheState |
		all tr:CacheTransaction |
			{
				cs in tr.beforeState iff tr.request.current in cs.current
				cs in tr.afterState iff tr.(response + re_res).current in cs.current
			}

	all t:Time |
		t in CacheState.current implies t in CacheTransaction.(request + response + re_res).current
}

//同じタイミングで同一のキャッシュに対するキャッシュ状態は存在しない
//同じキャッシュで同じ状態のキャッシュ状態は存在しない（統一する）
fact noMultipleCacheState{
	all tr:CacheTransaction |
		all disj cs,cs':CacheState |
			cs.cache = cs'.cache implies
				{
					cs in tr.beforeState implies cs' !in tr.beforeState
					cs in tr.afterState implies cs' !in tr.afterState
				}

	no disj cs,cs':CacheState |
		{
			cs.cache = cs'.cache
			cs.store = cs'.store
		}
}

fact flowCacheState{
	//for debug
	//all pre, post:CacheState |
		//pre in post.p iff (checkNewestCacheStateBefore[pre, post] or (post = pre and checkFirstCacheState[pre]))

	//初期状態のstoreをnullにする
	all cs:CacheState |
		checkFirstCacheState[cs] implies
			no cs.store

	//直前の状態のstoreを引き継ぐ
	all pre, post:CacheState |
		{
			post in CacheTransaction.beforeState implies
				checkNewestCacheStateBefore[pre, post] implies
					post.store in pre.store

			post in CacheTransaction.afterState implies
				all tr:CacheTransaction |
					checkNewestCacheStateAfter[pre, post, tr] implies
						post.store in pre.store + tr.response
		}
}

//preがpostの直前の状態か確認
pred checkNewestCacheStateBefore[pre:CacheState, post:CacheState]{
	pre.cache = post.cache

	some t,t' :Time |	//pre:t,  post:t'
		{
			t in pre.current
			t' in post.current
			t' in t.next.*next	//pre -> post
			no cs:CacheState |
				{
					cs != pre
					cs != post
					cs.cache = pre.cache
					some t'':Time |	//s:t''
						t'' in t.next.*next and t' in t''.next.*next	//pre -> cs -> post
				}
		}
}

//preがpostの直前の状態か確認 (postはtrのafterStateに存在)
pred checkNewestCacheStateAfter[pre:CacheState, post:CacheState, tr:CacheTransaction]{
	pre.cache = post.cache
	post in tr.afterState

	some t :Time |	//pre:t,  post:t'
		{
			t in pre.current
			tr.(response + re_res).current in t.next.*next	//pre -> post
			no cs:CacheState |
				{
					cs != pre
					cs != post
					cs.cache = pre.cache
					some t'':Time |	//s:t''
						t'' in t.next.*next and tr.(response + re_res).current in t''.next.*next	//pre -> cs -> post
				}
		}
}

pred checkFirstCacheState[cs:CacheState]{
	all cs':CacheState |
		cs.cache = cs'.cache implies
			cs'.current in cs.current.*next	//cs => cs'
}


/***********************

Token

************************/
sig Time {}

fact Traces{
	all t:Time | one e:Event | t = e.current
}

abstract sig Token {}

sig Uri{}

//使用されないURIは存在しない
fact noOrphanedUri{
	all u:Uri | some e:HTTPEvent | u = e.uri
}

abstract sig Method {}
one sig GET extends Method {}

//レスポンスの状態コード
abstract sig Status  {}
abstract sig RedirectionStatus extends Status {}
/*
lone sig c200,c401 extends Status{}
lone sig c301,c302,c303,c304,c305,c306,c307 extends RedirectionStatus {}
*/
//for simple model
lone sig c200 extends Status{}
lone sig c304 extends RedirectionStatus {}


/************************

HTTPTransaction

************************/
sig HTTPTransaction {
	request : one HTTPRequest,
	response : lone HTTPResponse,
	re_res : lone CacheReuse,
}{}

fact limitHTTPTransaction{
	all req:HTTPRequest | lone t:HTTPTransaction | t.request = req
	all reuse:CacheReuse | lone t:HTTPTransaction | t.re_res = reuse
	no t:HTTPTransaction |{
		some t.response and some t.re_res
	}
}

/****************************

Test Code

****************************/
//格納を観測
run test_store{
	#HTTPClient = 1
	#HTTPServer = 1

	#HTTPRequest = 1
	#HTTPResponse = 1

	#CacheTransaction = 1
	some CacheState.store
} for 2

//再利用を観測
run test_reuse{
	#HTTPClient = 1
	#HTTPServer = 1
	#Cache = 1
	#PrivateCache = 1

	#HTTPRequest = 2
	#HTTPResponse = 1
	#CacheReuse = 1

	#CacheTransaction = 2
} for 4

//"private"オプションの効果を確認
//No instance found で正常
run checkPrivateOption{
	all c:Cache | c in PublicCache

	some CacheState.store
	all res:HTTPResponse | one op:Private | op in res.headers.options
} for 6

//"no-store"オプションの効果を確認
//No instance found で正常
run checkNoStoreOption{
	some CacheState.store

	all res:HTTPResponse | one op:NoStore | op in res.headers.options
}

run{
	some cs:CacheState | #(cs.current) >= 2
	some CacheState.store
} for 4
