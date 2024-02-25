GHC = ghc

FILES = README Makefile Lambda.lhs AIT.lhs Main.lhs Bases.lhs arithmetic.lam delimit.lam pairup.lam uni.lam uni8.lam quine.lam bf.lam id.lam all.lam primes.lam none.lam thue-morse.lam even.lam odd.lam LC.pdf hw.bf uni.pl uni.js uni.py uni.rb primes256.blc

.SUFFIXES : .lhs .lam .blc .Blc

%.blc: %.lam blc
	./blc blc $< > $*.blc

%.Blc: %.lam blc
	./blc Blc $< > $*.Blc

blc:	AIT.lhs Lambda.lhs Main.lhs
	$(GHC) -O2 -Wall --make Main.lhs -o blc

tar:	$(FILES)
	tar -zcf AIT.tgz $(FILES)

test:	uni.pl uni.js uni.py
	echo ' hi' | ./uni.py
	echo ' hi' | ./uni.js
	echo ' hi' | ./uni.pl
	echo ' hi' | ./uni.rb
	./blc blc characteristic_sequences/primes256.lam | ./uni.py -b
	./blc blc characteristic_sequences/primes256.lam | ./uni.js -b
	./blc blc characteristic_sequences/primes256.lam | ./uni.pl -b
	./blc blc characteristic_sequences/primes256.lam | ./uni.rb -b
	./blc blc characteristic_sequences/primes256.lam | ./UniObf
	cat bf.blc8 ait/hw.bf | ./uni.py
	cat bf.blc8 ait/hw.bf | ./uni.js
	cat bf.blc8 ait/hw.bf | ./uni.pl
	cat bf.blc8 ait/hw.bf | ./uni.rb
	(cat hilbert; echo '12') | ./uni.py
	(cat hilbert; echo '12') | ./uni.js
	(cat hilbert; echo '12') | ./uni.pl
	(cat hilbert; echo '12') | ./uni.rb
	cat tromp/symbolic.Blc tromp/threetwo.blc | ./uni.py
	cat tromp/symbolic.Blc tromp/threetwo.blc | ./uni.js
	cat tromp/symbolic.Blc tromp/threetwo.blc | ./uni.pl
	cat tromp/symbolic.Blc tromp/threetwo.blc | ./uni.rb

bases:	Bases.lhs
	$(GHC) -O2 -Wall --make Bases.lhs -o bases
	
baserun:	bases
	echo 'yo'

.PHONY:	clean
clean:
	rm -f *.hi *.o
