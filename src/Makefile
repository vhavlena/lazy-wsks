#
# Makefile for WSkS decision procedure written in Haskell
# Author: Vojtech Havlena, 2018
#

all:
	ghc -odir obj -hidir obj --make Main.hs

debug:
	ghc -odir obj -hidir obj -prof -fprof-auto -rtsopts --make Main.hs

test:
	cd .. && python testcheck.py src/Main examples/

clean:
	rm obj/*.o obj/*.hi
