open util/ordering[Time]

abstract sig Principal {
	servers : set NetworkEndpoint,
}

fact DNSIsDisjointAmongstPrincipals {
	all disj p1,p2 : Principal | no (p1.servers & p2.servers)
}

sig Time {}

//イベントが直後に発生する制限解除
pred happensBefore[first:Event,second:Event]{
	second.current in first.current.next.*next
}

//ある時点(t)でリクエストに応答されていない
pred checkNotResponsed[req: HTTPRequest, t: Time]{
	no res:HTTPResponse |{
		req.uri = res.uri

		{
			//req -> ... -> res -> ... -> tの順でベントが発生
			res.current in req.current.*next
			t in res.current.next.*next

			res.to = req.from
		}or{
			some reuse:CacheReuse|{
				//req -> ... -> reuse -> ... -> tの順でベントが発生
				reuse.current in req.current.*next
				t in reuse.current.next.*next

				reuse.to = req.from
				reuse.target = res
			}
		}

	}
}

fact Traces{
	all t:Time | one e:Event | t = e.current
}

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
		e.to in HTTPIntermediary implies {
			one copy:HTTPEvent |{
				happensBefore[e, copy]
				checkNotResponsed[e, copy.current]

				e.to = copy.from
				all h:HTTPHeader | {
					h in e.headers implies h in copy.headers
					h in copy.headers implies h in e.headers
				}
				e.uri = copy.uri

				e in HTTPRequest implies copy in HTTPRequest
				e in HTTPResponse implies {
					copy in HTTPResponse
					e.statusCode = copy.statusCode
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

//----- イベント記述 -----
abstract sig Event {
	current : one Time
}

abstract sig NetworkEvent extends Event {
	from: NetworkEndpoint,
	to: NetworkEndpoint
}

abstract sig HTTPEvent extends NetworkEvent {
	headers: set HTTPHeader,
	uri : one Uri
}
sig HTTPRequest extends HTTPEvent {}
sig HTTPResponse extends HTTPEvent {
	statusCode: one Status
}

fact happenResponse{
	all res:HTTPResponse | one req:HTTPRequest |{
		happensBefore[req, res]
		checkNotResponsed[req, res.current]
		res.uri = req.uri
		res.from = req.to
		res.to = req.from
	}
}

abstract sig CacheEvent extends Event {
	happen: one Cache,
	target: one HTTPResponse
}
sig CacheStore extends CacheEvent {}
sig CacheReuse extends CacheEvent {to:NetworkEndpoint}
sig CacheVerification extends CacheEvent {}

//CacheStoreの発生条件
fact happenCacheStore{
	all store:CacheStore | one res:HTTPResponse | {
		//レスポンスが以前にやりとりされている
		happensBefore[res, store]
		store.target = res
		store.happen = res.to.cache

		//レスポンスのヘッダ条件
		store.happen in PrivateCache implies {	//for PrivateCache
			(one op:Maxage | op in res.headers.options) or
			(one d:DateHeader, e:ExpiresHeader | d in res.headers and e in res.headers)
		}
		store.happen in PublicCache implies{	//for PublicCache
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
		checkNotResponsed[req, reuse.current]
		reuse.target.uri = req.uri

		//過去の格納イベントに対する条件
		happensBefore[store, reuse]
		reuse.target = store.target

		//格納レスポンスの送信先
		reuse.to = req.from
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
			checkNotResponsed[req, veri.current]
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
				happensBefore[req, res]
				res.from = req.to
				res.to = req.from
				(res.statusCode = c200) or (res.statusCode = c304)	//200:新しいレスポンスを使用, 304:レスポンスを再利用

				//検証結果に対する動作（再利用 or 新レスポンス）
				(res.statusCode = c200) implies
					one reuse:CacheReuse | {
						happensBefore[res, reuse]
						reuse.target = veri.target
					}

				(res.statusCode = c304) implies
					one res_result:HTTPResponse | {
						happensBefore[res, res_result]
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

//----- トークン記述 -----
sig Uri{}

//使用されないURIは存在しない
fact noOrphanedUri{
	all u:Uri | some e:HTTPEvent | u = e.uri
}

//レスポンスの状態コード
abstract sig Status  {}
abstract sig RedirectionStatus extends Status {}
lone sig c200 extends Status{}
lone sig c304 extends RedirectionStatus {}
/*
lone sig c200,c401 extends Status{}
lone sig c301,c302,c303,c304,c305,c306,c307 extends RedirectionStatus {}
*/

//----- HTTPヘッダ記述 -----
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

//どのリクエスト・レスポンスにも属さないヘッダは存在しない
//各ヘッダは適切なリクエスト・レスポンスに属する
//どのCacheControlヘッダにも属さないCacheOptiionは存在しない
fact noOrphanedHeaders {
	all h:HTTPRequestHeader|some req:HTTPRequest|h in req.headers
	all h:HTTPResponseHeader|some resp:HTTPResponse|h in resp.headers
	all h:HTTPGeneralHeader|some e:HTTPEvent | h in e.headers
	all h:HTTPEntityHeader|some e:HTTPEvent | h in e.headers
	all c:CacheOption | c in CacheControlHeader.options
}

/****************************

Cache Definitions

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
	all pub:PublicCache | pub in HTTPClient.cache
	all pri:PrivateCache | (pri in HTTPServer.cache) or (pri in HTTPIntermediary.cache)
}

run {
	#PrivateCache = 0
	#PublicCache = 1
	#CacheStore = 1
	#CacheReuse = 1
	//#CacheVerification = 1

	#IfModifiedSinceHeader = 0
	#LastModifiedHeader = 0
	//#IfNoneMatchHeader = 0
	//#ETagHeader = 0
	#DateHeader = 0
	#ExpiresHeader = 0

	no e:NetworkEvent |{
		e.from = e.to
	}

	all disj req1, req2:HTTPRequest |{
		req1.from = req2.from
		req1.to = req2.to
	}

} for 5
