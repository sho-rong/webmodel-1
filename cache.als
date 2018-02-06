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

//Same-orgin BCP Attack
run Same_origin_BCP{
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

//Cross-origin BCP Attack
run Cross_origin_BCP{
	#HTTPRequest = 4
	#HTTPResponse = 3
	#CacheReuse = 1

	#Browser = 2
	#HTTPServer = 1
	#HTTPProxy = 2
	#Cache = 1

	#Principal = 5
	#Alice = 4

	//キャッシュはAliceの所有するプロキシの唯一存在
	all c:Cache | c in Alice.servers.cache and c in HTTPIntermediary.cache

	//端末の所有者を設定
	all p:Principal |	//全てのユーザは一つの端末しか管理しない
		one c:HTTPConformist |
			c in p.(servers + httpClients)
	all b:Browser | b in Alice.httpClients	//全てのBrowserはAliceに管理される
	all b:HTTPServer | b in Alice.servers	//全てのServerはAliceに管理される

	//通信イベントを作成
	one tr1,tr2,tr3,tr4:HTTPTransaction |{
		//tr1 client1 <-> proxy1
		tr1.request.from in HTTPClient
		(tr1.request.to in HTTPProxy and tr1.request.to in Alice.servers)

		//tr2 proxy1 <-> proxy2(Attacker's)
		(tr2.request.from in HTTPProxy and tr2.request.from in Alice.servers)
		(tr2.request.to in HTTPProxy and tr2.request.to !in Alice.servers)

		//tr3 proxy2 <-> Server
		(tr3.request.from in HTTPProxy and tr3.request.from !in Alice.servers)
		tr3.request.to in HTTPServer

		//tr4 client2 <-> proxy1
		tr4.request.from in HTTPClient
		(tr4.request.to in HTTPProxy and tr4.request.to in Alice.servers)
		tr4.request.from != tr1.request.from
		one tr4.re_res

		//トランザクションの発生順序
		tr2.request.current in tr1.request.current.*next
		tr3.request.current in tr2.request.current.*next
		tr2.response.current in tr3.response.current.*next
		tr1.response.current in tr2.response.current.*next
		tr4.request.current in tr1.response.current.*next

		//Attackerによるレスポンス改変
		tr2.response.body != tr3.response.body
	}
} for 8

//Cross Site Request Forgery
run CSRF{
	#HTTPRequest = 2
	#HTTPResponse = 2

	#HTTPClient = 1
	#HTTPServer = 2
	#HTTPIntermediary = 0

	#Principal = 3
	#Alice = 2

	all p:Principal |
		one c:HTTPConformist |
			c in p.(servers + httpClients)
	all b:Browser | b in Alice.httpClients

	one tr1,tr2:HTTPTransaction|{
		//トランザクションの発生順序
		tr2.request.current in tr1.response.current.*next

		//tr1 client <-> server1(Attacker's)
		//tr2 client <-> server2
		tr1.request.to !in Alice.servers
		tr2.request.to in Alice.servers

		//tr1によってtr2が発生
		tr2.cause = tr1

		tr1.request.uri != tr2.request.uri
	}
} for 4

//Web Cache Deception Attack
run Web_Cache_Deception{
	#HTTPRequest = 3
	#HTTPResponse = 2
	#CacheReuse = 1

	#HTTPClient = 2
	#HTTPServer = 1
	#HTTPProxy = 1
	#Cache = 1

	#Principal = 4
	#Alice = 3

	all c:Cache | c in HTTPProxy.cache

	all p:Principal |
		one c:HTTPConformist |
			c in p.(servers + httpClients)
	all i:HTTPProxy | i in Alice.servers
	all s:HTTPServer | s in Alice.servers

	one tr1,tr2,tr3:HTTPTransaction |{
		//tr1 client1 <-> proxy
		tr1.request.from in Alice.httpClients
		tr1.request.to in HTTPProxy

		//tr2 proxy <-> server
		tr2.request.from in HTTPProxy
		tr2.request.to in HTTPServer

		//tr3 client2(Attacker's) <-> proxy
		(tr3.request.from !in Alice.httpClients and tr3.request.from in HTTPClient)
		tr3.request.to in HTTPProxy

		one tr3.re_res
	}
} for 6