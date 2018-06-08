#
# Makefile for WSkS decision procedure written in Haskell
# Author: Vojtech Havlena, 2018
#

RELEASE_FLAGS=-O2 -odir obj -hidir obj
TEST_FLAGS=-odir obj -hidir obj
DEBUG_FLAGS=-odir obj -hidir obj -prof -fprof-auto -rtsopts

all:
	ghc $(TEST_FLAGS) --make Main.hs

debug:
	ghc $(DEBUG_FLAGS) --make Main.hs

release:
	ghc $(RELEASE_FLAGS) --make Main.hs

test:
	cd .. && python3 testcheck.py src/Main examples/

clean:
	rm obj/*.o obj/*.hi
