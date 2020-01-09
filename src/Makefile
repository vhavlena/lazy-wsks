#
# Makefile for WSkS decision procedure written in Haskell
# Author: Vojtech Havlena, 2019
#

RELEASE_FLAGS=-O2 -odir obj -hidir obj
TEST_FLAGS=-odir obj -hidir obj
DEBUG_FLAGS=-odir obj -hidir obj -prof -fprof-auto -rtsopts
DIR_FLAGS=-iautomata:aux:decision-procedure:formula-operation:graph:parser

all:
	ghc $(TEST_FLAGS) $(DIR_FLAGS) --make LazyWSkS.hs

debug:
	ghc $(DEBUG_FLAGS) $(DIR_FLAGS) --make LazyWSkS.hs

release:
	ghc $(RELEASE_FLAGS) $(DIR_FLAGS) --make LazyWSkS.hs

antiprenex:
	ghc $(DEBUG_FLAGS) $(DIR_FLAGS) --make Antiprenexor.hs

antiprenex-release:
	ghc $(RELEASE_FLAGS) $(DIR_FLAGS)--make Antiprenexor.hs

test:
	cd .. && python3 experimental/testcheck.py src/LazyWSkS examples/

clean:
	rm obj/*.o obj/*.hi
