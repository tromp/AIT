GHC = ghc

FILES = README Makefile Lambda.lhs AIT.lhs Main.lhs Bases.lhs arithmetic.lam delimit.lam pairup.lam uni.lam uni8.lam quine.lam bf.lam id.lam all.lam primes.lam none.lam thue-morse.lam even.lam odd.lam LC.pdf hw.bf blc.pl blc.js blc.py primes256.blc

.SUFFIXES : .lhs .lam .blc .Blc

%.blc: %.lam blc
	./blc blc $< > $*.blc

%.Blc: %.lam blc
	./blc Blc $< > $*.Blc

blc:	AIT.lhs Lambda.lhs Main.lhs
	$(GHC) -O2 -Wall --make Main.lhs -o blc

tar:	$(FILES)
	tar -zcf AIT.tgz $(FILES)

test:	blc.pl blc.js blc.py
	echo ' hi' | ./blc.py
	echo ' hi' | ./blc.js
	echo ' hi' | ./blc.pl
	echo ' hi' | ./blc.rb
	cat primes256.blc | ./blc.py -b
	cat primes256.blc | ./blc.js -b
	cat primes256.blc | ./blc.pl -b
	cat primes256.blc | ./blc.rb -b
	cat primes256.blc | ./UniObf
	cat bf.blc8 ait/hw.bf | ./blc.py
	cat bf.blc8 ait/hw.bf | ./blc.js
	cat bf.blc8 ait/hw.bf | ./blc.pl
	cat bf.blc8 ait/hw.bf | ./blc.rb
	(cat tromp/hilbert.Blc; echo '12') | ./blc.py
	(cat tromp/hilbert.Blc; echo '12') | ./blc.js
	(cat tromp/hilbert.Blc; echo '12') | ./blc.pl
	(cat tromp/hilbert.Blc; echo '12') | ./blc.rb

bases:	Bases.lhs
	$(GHC) -O2 -Wall --make Bases.lhs -o bases
	
baserun:	bases
	echo 'yo'

.PHONY:	clean
clean:
	rm -f *.hi *.o
