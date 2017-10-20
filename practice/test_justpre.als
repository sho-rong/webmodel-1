open util/ordering[Time]

sig Time{}
sig Event{
	p: lone Event,
	current: one Time
}

fact{
	all disj pre,post:Event |
		post.current in pre.current.next.*next implies
			justpre[pre, post.current] implies
				post.p = pre

	all t:Time | one e:Event | e.current = t
}

pred justpre[post:Event, t:Time]{
	all pre:Event |
		t in pre.current.next.*next implies
			post.current in pre.current.*next
}

run {
	#(Event.p) >= 2
}for 4
