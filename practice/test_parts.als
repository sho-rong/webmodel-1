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
	current: set Time,
	cache: one Cache,
	p: lone State
}
sig Token{}
sig Cache{}

fact{
	all t:Time | one e:Event | e.current = t

	all c:Cache | some s:State | c = s.cache

	all r:Request | one tr:Transaction | r = tr.req
	all r:Response | one tr:Transaction | r = tr.res

	all tr:Transaction |{
		tr.res.current in tr.req.current.*next
		tr.after.cache = tr.before.cache
		#(tr.before) <= 2
		#(tr.after) <= 2

		all disj s,s':State |
			s.cache = s'.cache implies
				{
					s in tr.before implies s' !in tr.before
					s in tr.after implies s' !in tr.after
				}
	}

	all s:State |{
		s in Transaction.after implies no s.p
		s in Transaction.(before+after)

		all tr:Transaction |
			{
				s in tr.before implies s.current = tr.req.current
				s in tr.after implies s.current = tr.res.current
			}
	}
}

run {
	no State.p
	no Token
	one Cache
} for 4
