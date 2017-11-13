open util/ordering[Time]

sig Time{}

abstract sig Event{current: one Time}
sig Request extends Event{}
sig Response extends Event{}

sig Transaction{
	req: one Request,
	res: one Response,
	before: set State,
	after: set State
}

sig State{
	store: set Token,
	current: one Time,
	cache: one Cache,
	p: set State
}
sig Token{}
sig Cache{}

fact{
	all t:Time | one e:Event | e.current = t

	all c:Cache | some s:State | c = s.cache

	all r:Request | one tr:Transaction | r = tr.req
	all r:Response | one tr:Transaction | r = tr.res

	all tr:Transaction |{
		//request -> response の順で発生
		tr.res.current in tr.req.current.next.*next

		//beforeとafterのCacheStateに含まれるキャッシュの数は同じ
		tr.after.cache = tr.before.cache

		//beforeとafterにそれぞれ含まれるCacheStateは2個
		#(tr.before) <= 2
		#(tr.after) <= 2

		//同一のキャッシュのCacheStateはbefore/afterに重複しない
		all disj s,s':State |
			s.cache = s'.cache implies
				{
					s in tr.before implies s' !in tr.before
					s in tr.after implies s' !in tr.after
				}
	}

	all s:State |{
		//すべてのCacheStateはいずれかのTransactionに含まれる
		s in Transaction.(before+after)

		//あるc:CacheStateがtr.beforeに含まれる <=> cの時間にtr.reqが含まれる
		//あるc:CacheStateがtr.afterに含まれる <=> cの時間にtr.resが含まれる
		all tr:Transaction |
			{
				s in tr.before iff tr.req.current in s.current
				s in tr.after iff tr.res.current in s.current
			}
	}
}

run {
	no State.p
	no Token
	one Cache
} for 4
