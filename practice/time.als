open util/ordering[Time]

sig Token{}
sig Time{}
abstract sig Event {pre,post : Time}
sig HTTPRequest extends Event{}
sig HTTPResponse extends Event{}


run show{} for 5 Time
