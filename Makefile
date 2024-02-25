GHC = ghc
CC = cc

.SUFFIXES : .lhs .lam .blc .blc8

%.blc: %.lam blc
	./blc blc $< > $*.blc

%.blc8: %.blc uni
	./uni deflate $< > $*.blc8

blc:	AIT.lhs Lambda.lhs Main.lhs
	$(GHC) -O2 -Wall --make Main.lhs -o blc

uni:	uni.c
	$(CC) -O3 -Wall --make uni.c -o uni

test:	uni.pl uni.js uni.py
	echo ' hi' | ./uni.py
	echo ' hi' | ./uni.js
	echo ' hi' | ./uni.pl
	echo ' hi' | ./uni.rb
	./uni -b primes take256
	./blc blc characteristic_sequences/primes256.lam | ./uni.py -b
	./blc blc characteristic_sequences/primes256.lam | ./uni.js -b
	./blc blc characteristic_sequences/primes256.lam | ./uni.pl -b
	./blc blc characteristic_sequences/primes256.lam | ./uni.rb -b
	./blc blc characteristic_sequences/primes256.lam | ./UniObf
	cat ait/hw.bf | ./uni bf
	cat bin/bf.blc8 ait/hw.bf | ./uni.py
	cat bin/bf.blc8 ait/hw.bf | ./uni.js
	cat bin/bf.blc8 ait/hw.bf | ./uni.pl
	cat bin/bf.blc8 ait/hw.bf | ./uni.rb
	echo '12' | ./uni hilbert
	(cat hilbert; echo '12') | ./uni.py
	(cat hilbert; echo '12') | ./uni.py
	(cat hilbert; echo '12') | ./uni.js
	(cat hilbert; echo '12') | ./uni.pl
	(cat hilbert; echo '12') | ./uni.rb
	printf '%s' '(\f\x f(f(f x)))(\f\x f(f x))' | ./uni parse | ./uni symbolic
	cat bin/symbolic.blc8 bin/threetwo.blc | ./uni.py
	cat bin/symbolic.blc8 bin/threetwo.blc | ./uni.js
	cat bin/symbolic.blc8 bin/threetwo.blc | ./uni.pl
	cat bin/symbolic.blc8 bin/threetwo.blc | ./uni.rb

bases:	Bases.lhs
	$(GHC) -O2 -Wall --make Bases.lhs -o bases
	
baserun:	bases
	echo 'yo'

.PHONY:	clean
clean:
	rm -f *.hi *.o
