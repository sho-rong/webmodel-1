open test_parts
open util/ordering[Time]

fact{
	all disj pre,post: State |
		justpre[pre, post] implies
			{
				post.p = pre
				post.store in pre.store
			}

	all s:State |
		firstState[s] implies
			{
				s.p = s
				#(s.store) = 3
			}
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
			all s:State |
				{
					s in Transaction.after
					s.cache = post.cache
				}implies
					all tr'':Transaction |
						s in tr''.after implies
							{
								tr.res.current in tr''.res.current.*next	//s => pre
								tr''.res.current in tr'.req.current.*next	//post => s
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
					tr'.res.current in tr.req.current.*next	//s => s'
}

fact{
	all s:State | one tr:Transaction | s in tr.(before + after)
	all tr:Transaction | no s:State |
		{
			s in tr.before
			s in tr.after
		}
}

run {
	no Token
	one Cache
} for 6
