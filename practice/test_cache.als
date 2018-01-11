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
					e in HTTPRequest
				}

				original in HTTPResponse implies {
					e in HTTPResponse
					e.statusCode = original.statusCode
				}
			}
		}
	}

	all tr:HTTPTransaction |{
		tr.request.to in HTTPIntermediary implies{
			one tr.response implies{
				one tr':HTTPTransaction |{
					tr'.request.current in tr.request.current.*next	//tr.req => tr'.req
					tr.response.current in tr'.response.current.*next	//tr'.res => tr.res

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

		//所属するTransactionはただ一つ
		one tr:HTTPTransaction | res = tr.response
	}
}

//CacheReuseの発生条件
fact happenCacheReuse{
	all reuse:CacheReuse | one tr:CacheTransaction |
		{
			happensBefore[reuse.target, reuse]

			tr.re_res = reuse
			reuse.to = tr.request.from
			reuse.from in tr.request.(from + to)

			all pre, post:CacheState |
				(post in tr.afterState and checkNewestCacheStateAfter[pre, post, tr]) implies
					{
						reuse.target in pre.store
						reuse.from.cache = pre.cache
					}

			reuse.target.uri = tr.request.uri
		}
}

//firstがsecondよりも前に発生しているか確認
pred happensBefore[first:Event,second:Event]{
	second.current in first.current.next.*next
}

//ある再利用を行うトランザクションでレスポンス時点で検証済みか判定
pred checkVerification[tr:CacheTransaction]{
	one tr.re_res	//再利用で応答している

	//検証を行っているトランザクションが成立している
	some tr':CacheTransaction |	//tr': 検証を行うトランザクション
	{
		tr' != tr
		one tr'.response	//検証のレスポンスが存在する

		tr'.request.current in tr.request.current.*next	//tr.request => tr'.request
		tr.re_res.current in tr'.response.current.*next	//tr'.response => tr.reuse

		tr'.request.from = tr.re_res.from
		tr'.request.to = tr.re_res.target.from
		tr'.request.uri = tr.request.uri

		//検証可能なレスポンスがtr.request時点で格納されている
		some tar_res:HTTPResponse |
		{
			tar_res.uri = tr.request.uri

			//検証対象のレスポンスがtr.request時点で格納されている
			one cs:CacheState |
			{
				cs in tr.beforeState
				cs.cache = tr.re_res.from.cache
				tar_res in cs.store
			}

			//検証対象のレスポンスに必要なヘッダが含まれている
			some h:HTTPHeader |
			{
				h in ETagHeader + LastModifiedHeader
				h in tar_res.headers
			}

			//格納レスポンスのヘッダに適した条件付きリクエストのヘッダを生成
			(some h:ETagHeader | h in tar_res.headers) implies	//格納レスポンスがETagHeaderを持っていた場合、IfNoneMatchHeaderを付けて送信
				(some h:IfNoneMatchHeader | h in tr'.request.headers)
			(some h:LastModifiedHeader | h in tar_res.headers) implies	//格納レスポンスがLastModifiedHeaderを持っていた場合、IfModifiedSinceHeaderを付けて送信
				(some h:IfModifiedSinceHeader | h in tr'.request.headers)
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
					res in cs.store
					cs.cache = tr.request.from.cache
					cs in tr.afterState
				}
			}

			//レスポンスの状態コード
			tr.response.statusCode in c200 + c304

			//再利用不可(c200)である場合、検証結果のレスポンスが格納される（既に格納済みであったレスポンスはすべて削除される）
			tr.response.statusCode = c200 implies
			{
				all cs:CacheState |
					(cs in tr.afterState and cs.cache = tr.response.to.cache) implies
						tr.response in cs.store
			}

			//再利用可(c304)である場合、検証結果のレスポンスは格納されない（既に格納済みであったレスポンスのうち一つが残る）
			tr.response.statusCode = c304 implies
			{
				all cs:CacheState |
					(cs in tr.afterState and cs.cache = tr.response.to.cache) implies
						tr.response !in cs.store
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
	all tr:CacheTransaction |
		(some op:NoCache | op in (tr.request.headers.options + tr.re_res.target.headers.options)) implies
			some tr.re_res implies
				checkVerification[tr]

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
	all ep:NetworkEndpoint | lone c:Cache | c in ep.cache
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
	p: set CacheState,
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

//キャッシュを持つ端末のTransactionは必ずCacheTransactionである
//キャッシュを持たない端末のTransactionは必ずCacheTransactionでない
fact {
	all tr:HTTPTransaction |
		some tr.request.(from + to).cache iff tr in CacheTransaction
}

fact flowCacheState{
	//初期状態のstoreをnullにする
	all cs:CacheState |
		checkFirstCacheState[cs] implies
			no cs.store

	//直前のキャッシュの状態を継承する（responseの場合は追加可能）
	all pre, post:CacheState, tr:CacheTransaction |
		{
			checkNewestCacheStateBefore[pre, post, tr] implies
				post.store in pre.store
			checkNewestCacheStateAfter[pre, post, tr] implies
				post.store in (pre.store + tr.response)
		}

	//for debug
	all pre, post:CacheState |
		(some tr:CacheTransaction | checkNewestCacheStateBefore[pre, post, tr] or checkNewestCacheStateAfter[pre, post, tr]) iff pre in post.p
}

//preがpostの直前の状態か確認(postがbeforeStateの場合)
pred checkNewestCacheStateBefore[pre:CacheState, post:CacheState, tr:CacheTransaction]{
	pre.cache = post.cache
	post in tr.beforeState

	some t,t':Time |
		{
			t in pre.current	//t:pre
			t' = tr.request.current	//t':post
			t' in t.next.*next	//pre -> post

			all cs:CacheState, t'':Time |
				(cs.cache = pre.cache and t'' in cs.current) implies	//t'':cs
						(t in t''.*next) or (t'' in t'.*next)	//cs => pre (or) post => cs
		}
}

//preがpostの直前の状態か確認(postがafterStateの場合)
pred checkNewestCacheStateAfter[pre:CacheState, post:CacheState, tr:CacheTransaction]{
	pre.cache = post.cache
	post in tr.afterState

	some t,t':Time |
		{
			t in pre.current	//t:pre
			t' = tr.(response + re_res).current	//t':post
			t' in t.next.*next	//pre -> post

			all cs:CacheState, t'':Time |
				(cs.cache = pre.cache and t'' in cs.current) implies	//t'':cs
						(t in t''.*next) or (t'' in t'.*next)	//cs => pre (or) post => cs
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
}{
	(response + re_res).current in request.current.*next
}

fact limitHTTPTransaction{
	all req:HTTPRequest | lone t:HTTPTransaction | t.request = req
	all reuse:CacheReuse | lone t:HTTPTransaction | t.re_res = reuse
	no t:HTTPTransaction |
		some t.response and some t.re_res
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

run test_store{
	#NetworkEndpoint = 2
	#HTTPClient = 1
	#HTTPServer = 1

	#HTTPRequest = 2
	#HTTPResponse = 2

	some cs:CacheState | #(cs.store) > 1
} for 4

//再利用を観測
run test_reuse{
	#HTTPClient = 1
	#HTTPServer = 1
	#Cache = 1

	#HTTPRequest = 2
	#HTTPResponse = 1
	#CacheReuse = 1

	#CacheTransaction = 2
} for 4

//検証を観測
run test_verification{
	#HTTPClient = 1
	#HTTPServer = 1
	#HTTPIntermediary = 0
	#Cache = 1
	#PrivateCache = 1

	some tr:CacheTransaction | checkVerification[tr]
} for 6

//"private"オプションの効果を確認
//No instance found で正常
run checkPrivateOption{
	all c:Cache | c in PublicCache
	some CacheState.store
	all res:HTTPResponse | one op:Private | op in res.headers.options
}

//"no-store"オプションの効果を確認
//No instance found で正常
run checkNoStoreOption{
	some CacheState.store
	all res:HTTPResponse | one op:NoStore | op in res.headers.options
}

//"no-cache"オプションの効果を確認
//No instance found で正常
run checkNoCacheOption{
	some tr:CacheTransaction |
	{
		some op:NoCache | op in tr.request.headers.options
		one tr.re_res
	}

	no tr:CacheTransaction | checkVerification[tr]
}

run{
	#NetworkEndpoint = 2
	#HTTPClient = 1
	#HTTPServer = 1
	#Cache = 1
	#PrivateCache = 1

	#HTTPRequest = 2
	#HTTPResponse = 2

	some CacheState.store
} for 4

assert checkState{
	/*all post:CacheState | some pre:CacheState, tr:CacheTransaction |
		checkNewestCacheStateBefore[pre, post, tr] or checkNewestCacheStateAfter[pre, post, tr] or checkFirstCacheState[post]*/

	one CacheReuse implies
		all reuse:CacheReuse | all res:HTTPResponse | reuse.current in res.current.*next
}
check checkState for 4
