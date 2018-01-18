open declarations

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
