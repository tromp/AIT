GHC = ghc

FILES = README Makefile Lambda.lhs AIT.lhs Main.lhs arithmetic.lam delimit.lam pairup.lam uni.lam uni8.lam quine.lam bf.lam id.lam all.lam primes.lam none.lam thue-morse.lam even.lam odd.lam LC.pdf hw.bf

.SUFFIXES : .lhs .lam .blc .Blc

%.lam: %.blc blc
	./blc blc $< > $*.blc

%.lam: %.Blc blc
	./blc Blc $< > $*.Blc

blc:	AIT.lhs Lambda.lhs Main.lhs
	$(GHC) -O2 -Wall --make Main.lhs -o blc

tar:	$(FILES)
	tar -zcf AIT.tgz $(FILES)

.PHONY:	clean
clean:
	rm -f *.hi *.o
