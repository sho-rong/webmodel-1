open declarations

//レスポンスを格納
run test_store{
	#HTTPClient = 1
	#HTTPServer = 1

	#HTTPRequest = 1
	#HTTPResponse = 1

	some CacheState.store
} for 2

//2つのレスポンスを同時に格納
run test_store2{
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
