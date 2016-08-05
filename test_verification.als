//
//	declarrations.als (exisiting)
//

abstract sig HTTPHeader {}
abstract sig HTTPResponseHeader extends HTTPHeader{}{
	all h:this | h in HTTPResponse.headers
}
abstract sig HTTPRequestHeader extends HTTPHeader{}{
	all h:this | h in HTTPRequest.headers
}
abstract sig HTTPGeneralHeader extends HTTPHeader{}
abstract sig HTTPEntityHeader extends HTTPHeader{}

abstract sig HTTPEvent{headers: set HTTPHeader}
lone sig HTTPResponse extends HTTPEvent {statusCode : Status}
one sig HTTPRequest extends HTTPEvent{}
abstract sig Status{}{all s:Status | s in HTTPResponse.statusCode}
abstract sig RedirectionStatus extends Status {}
lone sig c304 extends RedirectionStatus {}
lone sig c200 extends Status{}

//
//	cache.als
//
abstract sig CacheOption{}
abstract sig RequestCacheOption extends CacheOption{}
abstract sig ResponseCacheOption extends CacheOption{}
/*
lone sig NoCache,NoStore,NoTransform extends CacheOption{}
lone sig OnlyIfCached extends RequestCacheOption{}
lone sig MaxStale,MinStale extends RequestCacheOption{time: one Int}
lone sig MustRevalidate,Public,Private,ProxyRevalidate extends ResponseCacheOption{}
lone sig Maxage,SMaxage extends ResponseCacheOption{time: one Int}
*/

lone sig NoCache extends CacheOption{}
lone sig OnlyIfCached extends RequestCacheOption{}
lone sig MaxStale extends RequestCacheOption{time: one Int}{time > 0}
lone sig Private extends ResponseCacheOption{}
lone sig Maxage,SMaxage extends ResponseCacheOption{time: one Int}{time > 0}

sig PragmaHeader extends HTTPRequestHeader{}
sig IfModifiedSinceHeader extends HTTPRequestHeader{modified: one Int}
sig IfNoneMatchHeader extends HTTPRequestHeader{etag: one Int}
sig ETagHeader extends HTTPResponseHeader{etag: one Int}
sig LastModifiedHeader extends HTTPResponseHeader{modified: one Int}
sig AgeHeader extends HTTPResponseHeader{age : one Int}
{
	age > 0
	
	/*
	let apparent = Cache.restime.minus[HTTPResponse.headers.date]>0 implies Cache.restime.minus[HTTPResponse.headers.date] else 0 |
		let corrected = some HTTPResponse.headers.age implies HTTPResponse.headers.age.plus[Cache.restime.minus[Cache.reqtime]] else Cache.restime.minus[Cache.reqtime] |
			let visit = Cache.current.minus[Cache.restime] | 
				apparent > corrected implies age = apparent.plus[visit] else age = corrected.plus[visit]
	*/
}

sig CacheControlHeader extends HTTPGeneralHeader{options : set CacheOption}
sig DateHeader extends HTTPGeneralHeader{date : one Int}{date > 0}
sig ExpiresHeader extends HTTPGeneralHeader{expire : one Int}{expire > 0}

lone abstract sig Cache{
	stored: lone HTTPResponse,
	current: one Int,
	reqtime: one Int,
	restime: one Int
}{
	current > 0
	reqtime > 0
	restime > 0
	reqtime < restime
	restime < current
	
	#stored>0 implies no NoStore	//for NoStore
	#stored>0 implies #AgeHeader>0
}

sig PrivateCache extends Cache{}{
	#stored>0 implies	//for expiration date
		(some op:Maxage | op in HTTPResponse.headers.options) or 
		(some d:DateHeader, e:ExpiresHeader | d in HTTPResponse.headers and e in HTTPResponse.headers)

	#stored>0 and #(HTTPResponse -> Maxage)>0 implies	//for Maxage
		all n:Maxage.time | n > current.minus[restime]

	#stored>0 and #(HTTPResponse -> ExpiresHeader)>0 implies	//for ExpiresHeader and DateHeader
		all e:ExpiresHeader.expire, d:DateHeader.date | e.minus[d] > current.minus[restime]
}

sig PublicCache extends Cache{}{
	#stored>0 implies no Private	//for Private
	
	#stored>0 implies	//for expiration date
		(some op:SMaxage | op in HTTPResponse.headers.options) or
		(some op:Maxage | op in HTTPResponse.headers.options) or
		(some d:DateHeader, e:ExpiresHeader | d in HTTPResponse.headers and e in HTTPResponse.headers)
	
	#stored>0 and #(HTTPResponse -> SMaxage)>0 implies	//for SMaxage
		all n:SMaxage.time | n > current.minus[restime]
	
	#stored>0 and #(HTTPResponse -> Maxage)>0 implies	//for Maxage
		all n:Maxage.time | n > current.minus[restime]

	#stored>0 and #(HTTPResponse -> ExpiresHeader)>0 implies	//for ExpiresHeader and DateHeader
		all e:ExpiresHeader.expire, d:DateHeader.date | e.minus[d] > current.minus[restime]
}

fact LimitHeader{
	all h:HTTPHeader | h in HTTPResponse.headers or h in HTTPRequest.headers
	all c:CacheOption | c in CacheControlHeader.options
	no res:HTTPResponse, req:HTTPRequest | res.headers = req.headers
	no resoption:ResponseCacheOption | resoption in HTTPRequest.headers.options
	no reqoption:RequestCacheOption | reqoption in HTTPResponse.headers.options
	lone h:CacheControlHeader | h in HTTPRequest.headers
	lone h:CacheControlHeader | h in HTTPResponse.headers
	one h:DateHeader | h in HTTPRequest.headers
	one h:DateHeader | h in HTTPResponse.headers
	lone h:ExpiresHeader | h in HTTPRequest.headers
	lone h:ExpiresHeader | h in HTTPResponse.headers
	lone h:AgeHeader | h in HTTPRequest.headers
	lone h:AgeHeader | h in HTTPResponse.headers
}

pred show(){
	/*
	#NoTransform = 0
	#OnlyIfCached = 0
	#MaxStale = 0
	#MinStale = 0
	#MustRevalidate = 0
	#Public = 0
	#ProxyRevalidate = 0
	#SMaxage = 0
	*/
	
	#PrivateCache.stored = 1
	#Maxage = 0
}

run show for 5
