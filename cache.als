open declarations

lone abstract sig Cache{
	stored: set HTTPResponse,
	current: one Int
}

abstract sig PrivateCache extends Cache{}
abstract sig PublicCache extends Cache{}
sig BrowserCache extends PrivateCache{}	//private cache
sig ServerCache extends PublicCache{}	//public cache
sig ProxyCache extends PublicCache{}	//public cache
sig GatewayCache extends PublicCache{}	//public cache

//共有キャッシュ内のレスポンスには"private"の記述がない
fact ResponseInPrivate{
	no res:HTTPResponse | res in PublicCache.stored and NoStore in res.headers.options
}

//"no-store"がないこと
fact NostoreNotInResponse{
	no res:HTTPResponse | res in Cache.stored and NoStore in res.headers.options
}

//期限設定もしくはキャッシュの許可が存在
fact ExpiresAndPermit{
	//
	//
	//
}

//"no-cache"なし
fact ValidationCheck{
	//
	//
	//
}

//期限判定
fact ExpirationCheck{
	//
	//
	//
}

pred show{}
run show for 5
