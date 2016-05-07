# Makefile for DH for testing

all:	DH

DH1.O:	DH1.S
	armasm -cpu ARM7TM DH1.S

DH:	DH2.C DH1.O
	armcc -apcs /interwork -DDH_DEBUG -li -Otime DH2.C DH1.O

