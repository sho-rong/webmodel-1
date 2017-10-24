open util/ordering[Time]

sig Time{}
sig Event{current: one Time}
sig Transaction{
	req: one Event,
	res: one Event,
	before: set State,
	after: set State
}
sig State{
	//store: set Token,
	cache: one Cache,
	p: lone State
}
//sig Token{}
sig Cache{}

fact{
	all t:Time | one e:Event | e.current = t
	all tr:Transaction |{
		tr.after.cache = tr.before.cache
		#(tr.before) <= 2
		#(tr.after) <= 2
	}
	all s:State |{
		s in Transaction.after implies no s.p
		s in Transaction.(before+after)
	}

	all disj pre,post: State |
		justpre[pre, post] implies
			post.p = pre

//	firstTransaction[e, e.current] implies
//		no e.p

}

pred justpre[pre:State, post:State]{
	pre in Transaction.after
	post in Transaction.before
	pre.cache = post.cache

}

pred firstState[s:State]{

}


run {} for 3
