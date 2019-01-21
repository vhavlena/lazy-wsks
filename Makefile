#
# Makefile for WSkS decision procedure written in Haskell
# Author: Vojtech Havlena, 2018
#

all:
	cd src && make

release:
	cd src && make release

test:
	cd src && make test
