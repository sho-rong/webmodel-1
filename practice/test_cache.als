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

fact MoveOfIntermediary{
	all e:HTTPEvent |{
		e.from in HTTPIntermediary implies{	//e:中継者から送信されるイベント
			one original:HTTPEvent |{	//original:中継者に向けて送信されたイベント
				happensBefore[original, e]

				e.from = original.to
				e.uri = original.uri

				original in HTTPRequest implies {
					checkNotResponsed[original, e.current]
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
		checkNotResponsed[req, res.current]
		res.uri = req.uri
		res.from = req.to
		res.to = req.from

		//HTTPTransactionに登録
		one t:HTTPTransaction | t.request = req and t.response = res
	}
}

//CacheReuseの発生条件
fact happenCacheReuse{
	all reuse:CacheReuse | one req:HTTPRequest |{
		//応答するリクエストに対する条件
		happensBefore[req, reuse]
		checkNotResponsed[req, reuse.current]
		req.uri = reuse.target.uri
		req.from = reuse.to
		reuse.from in req.to + req.from

		//HTTPTransactionに登録 ＆ 再利用レスポンスが先にストアされている
		one t:HTTPTransaction | {
			t.request = req
			t.re_res = reuse
			one bs:CacheState | {
				bs in t.beforeState
				bs.cache = reuse.from.cache
				reuse.target in bs.store
			}
		}
	}
}

//firstがsecondよりも前に発生する
pred happensBefore[first:Event,second:Event]{
	second.current in first.current.next.*next
}

//ある時点(t)でリクエストに応答されていない
pred checkNotResponsed[req: HTTPRequest, t: Time]{
	/*no res:HTTPResponse |{
		req.uri = res.uri

		{
			//req -> ... -> res -> ... -> tの順でベントが発生
			res.current in req.current.*next
			t in res.current.next.*next

			res.to = req.from
			res.from = req.to
		}or{
			some reuse:CacheReuse|{
				//req -> ... -> reuse -> ... -> tの順でベントが発生
				reuse.current in req.current.*next
				t in reuse.current.next.*next

				reuse.to = req.from
				reuse.target = res

				one p:NetworkEndpoint |{
					p.cache = reuse.happen
					(p = req.from) or (p = req.to)
				}
			}
		}
	}*/
}

/***********************

Headers

************************/
abstract sig HTTPHeader {}
abstract sig HTTPResponseHeader extends HTTPHeader{}
abstract sig HTTPRequestHeader extends HTTPHeader{}
abstract sig HTTPGeneralHeader extends HTTPHeader{}
abstract sig HTTPEntityHeader extends HTTPHeader{}

/*
sig IfModifiedSinceHeader extends HTTPRequestHeader{}
sig IfNoneMatchHeader extends HTTPRequestHeader{}
sig ETagHeader extends HTTPResponseHeader{}
sig LastModifiedHeader extends HTTPResponseHeader{}
sig AgeHeader extends HTTPResponseHeader{}
*/
sig CacheControlHeader extends HTTPGeneralHeader{options : set CacheOption}
/*
sig DateHeader extends HTTPGeneralHeader{}
sig ExpiresHeader extends HTTPEntityHeader{}
*/

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

/*
//CacheControlHeaderのオプションに関する制限
fact CCHeaderOption{
	//for "no-cache"
	all reuse:CacheReuse |{
		(some op:NoCache | op in reuse.target.headers.options) implies {
			one veri:CacheVerification | {
				happensBefore[veri,reuse]
				veri.target = reuse.target
				veri.happen = reuse.happen
			}
		}
	}

	//for "no-store"
	no store:CacheStore | some op:NoStore | op in store.target.headers.options

	//for only-if-cached
	all req:HTTPRequest | (some op:OnlyIfCached | op in req.headers.options) implies {
		some reuse:CacheReuse | {
			happensBefore[req, reuse]
			reuse.target.uri = req.uri
			reuse.to = req.from
		}
	}

	//for "private"
	no op:Private | some store:CacheStore | {
		store.happen in PublicCache
		op in store.target.headers.options
	}
}
*/

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
	afterState.cache = request.from.cache + request.to.cache

	//HTTPResponseが存在するTransactionの場合
	some response implies {
		all before,after:CacheState | {
			before.cache = after.cache
			before in beforeState
			after in afterState
		}implies{
			after.store in before.store + response
		}
	}

	//CacheReuseが存在するTransactionの場合
	some re_res implies{
		all before,after:CacheState | {
			before.cache = after.cache
			before in beforeState
			after in afterState
		}implies{
			after.store = before.store
		}
	}
}

fact limitBeforeState{
	all tr:CacheTransaction |
	{
		all disj before,pre:CacheState |
		{
			before in tr.beforeState
			pre.cache = before.cache
			all tr':CacheTransaction |
				{
					pre in (tr'.afterState)
					tr.request.current in tr'.response.current.*next
				}implies
					checkNewestCacheState[pre, before] implies before.store in pre.store
		}

		all before:CacheState |
			before in tr.beforeState implies
				checkFirstCacheState[before] implies
					no res:HTTPResponse | res in before.store
	}
}

sig CacheState{
	cache: one Cache,
	store: set HTTPResponse
}

fact noOrphanedCacheState{
	all cs:CacheState | cs in CacheTransaction.beforeState + CacheTransaction.afterState
}

//同じタイミングで同一のキャッシュに対するキャッシュ状態は存在しない
fact noMultipleCacheState{
	all tr:CacheTransaction |
		all disj cs,cs':CacheState |
			cs.cache = cs'.cache implies
				{
					cs in tr.beforeState implies cs' !in tr.beforeState
					cs in tr.afterState implies cs' !in tr.afterState
				}
	/*no disj cs,cs':CacheState |
		all tr:CacheTransaction |
			{
				(cs in tr.beforeState and cs' in tr.beforeState) implies cs.cache = cs'.cache
				(cs in tr.afterState and cs' in tr.afterState) implies cs.cache = cs'.cache
			}*/
}

//時刻t_preのCacheState preが、時刻tにおいて最新か確認
pred checkNewestCacheState[pre:CacheState, post:CacheState]{
	pre in CacheTransaction.afterState
	post in CacheTransaction.beforeState
	pre.cache = post.cache

	one disj tr,tr':CacheTransaction |
		{
			pre in tr.afterState
			post in tr.beforeState
		}implies
			all cs:CacheState |
				{
					cs in CacheTransaction.afterState
					cs.cache = post.cache
				}implies
					all tr'':CacheTransaction |
						cs in tr''.afterState implies
							{
								tr.response.current in tr''.response.current.*next	//s => pre
								tr''.response.current in tr'.request.current.*next	//post => s
							}
}

pred checkFirstCacheState[cs:CacheState]{
	cs in CacheTransaction.beforeState

	all cs':CacheState |
		{
			cs' in CacheTransaction.afterState
			cs.cache = cs'.cache
		}implies
			all disj tr,tr':CacheTransaction |
				{
					cs in tr.beforeState
					cs' in tr.afterState
				}implies
					tr'.response.current in tr.request.current.*next	//cs => cs'
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

//時系列に従ったモデルの考察
// second.pre >= first.post

abstract sig Method {}
one sig GET extends Method {}

//レスポンスの状態コード
abstract sig Status  {}
abstract sig RedirectionStatus extends Status {}
lone sig c200 extends Status{}
lone sig c302 extends RedirectionStatus {}


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
	all reuse:CacheReuse | lone t:HTTPTransaction | t.re_res = reuse
	no t:HTTPTransaction |{
		some t.response and some t.re_res
	}
}

/****************************

Test Code

****************************/
run test_store{
	#HTTPClient = 1
	#HTTPServer = 1

	#HTTPRequest = 1
	#HTTPResponse = 1

	#CacheTransaction = 1
	#CacheState = 2
} for 2

run test_reuse{
	#HTTPClient = 1
	#HTTPServer = 1
	#Cache = 1
	#PrivateCache = 1

	#HTTPRequest = 2
	#HTTPResponse = 1
	#CacheReuse = 1

	#CacheTransaction = 2
	//#CacheState >= 2
} for 4
