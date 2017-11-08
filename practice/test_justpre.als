open test_parts
open util/ordering[Time]

fact{
	all pre, post:State |
		pre in post.p iff (justpre[pre, post] or (post = pre and firstState[pre]))
}

pred justpre[pre:State, post:State]{
	pre.cache = post.cache

	some t,t' :Time|	//pre:t,  post:t'
		{
			t in pre.current
			t' in post.current
			t' in t.next.*next	//pre -> post
			no s:State |
				{
					s != pre
					s != post
					s.cache = pre.cache
					some t'':Time |	//s:t''
						t'' in t.next.*next and t' in t''.next.*next	//pre -> s -> post
				}
		}
}

pred firstState[s:State]{
	all s':State |
		s.cache = s'.cache implies
			s'.current in s.current.*next	//s => s'
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
	some Cache
} for 6
