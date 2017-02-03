havlak%cc: havlak%.cc
	g++ -O3 -o havlak$*cc havlak$*.cc

havlak%: havlak%.go
	6g havlak$*.go
	6l -o $@ havlak$*.6
	rm havlak$*.6

%.time: %
	xtime $*

havlak%.prof: havlak%
	havlak$* -cpuprofile=$@

havlak%.mprof: havlak%
	havlak$* -memprofile=$@
