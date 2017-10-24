open test_parts
open util/ordering[Time]

fact{
/*	all disj pre,post: State |
		justpre[pre, post] implies
			post.p = pre*/

	all s:State |
		firstState[s] implies
			s.p = s
}

pred justpre[pre:State, post:State]{
	pre in Transaction.after
	post in Transaction.before
	pre.cache = post.cache
	one disj tr, tr':Transaction |
		{
			pre in tr.after
			post in tr'.before
		}implies
			no s:State |
				{
					s in Transaction.after
					s.cache = post.cache
					all tr'':Transaction |
						s in tr''.after implies
							tr'.req.current in tr''.res.current.*next implies	// s => post
								tr''.res.current in tr.res.current.*next	//pre => s
				}
}

pred firstState[s:State]{
	s in Transaction.before

	all s':State |
		{
			s' in Transaction.after
			s.cache = s'.cache
		}implies
			all disj tr, tr':Transaction |
				{
					s in tr.before
					s' in tr'.after
				}implies
					tr'.req.current in tr.res.current.*next	//s => s'
}


run {
	one Cache
	no Token

	some State.p
	#State = 4
} for 4
