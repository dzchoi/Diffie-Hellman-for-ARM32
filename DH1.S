; DH1.s
; 
;  99.09.06	dzchoi	Created
; 
;  To compile:
;  ARMASM -cpu ARM7TM DH1.s



;	r := 2^32 (base)
;	R := r^n
;	N < R should be odd.
;	R mod N = R - N if R/2 <= N < R

		AREA	FOR_DH, CODE



adc1		; uint32 adc1(uint32 x, uint32 *c)
; y = x + *c
; *c = y / r
; return y % r

		EXPORT	adc1

		MOV	ip, #0		; ip := RdHi, a1 := RdLo
		LDR	a3, [a2]
		ADDS	a1, a1, a3	;
		ADDCS	ip, ip, #1	; ip:a1 = x + *c ; or ADC  ip, ip, #0
		STR	ip, [a2]
		MOV	pc, lr



adc2		; uint32 adc3(uint32 x, uint32 a, uint32 *c)
; y = x + a + *c
; *c = y / r
; return y % r

		EXPORT	adc2

		MOV	ip, #0		; ip := RdHi, a1 := RdLo
		ADDS	a1, a1, a2	;
		ADDCS	ip, ip, #1	; ip:a1 = x + a ; or ADC  ip, ip, #0
		LDR	a2, [a3]
		ADDS	a1, a1, a2	;
		ADDCS	ip, ip, #1	; ip:a1 += *c	; or ADC  ip, ip, #0
		STR	ip, [a3]
		MOV	pc, lr



adc3		; uint32 adc3(uint32 x, uint32 a, uint32 b, uint32 *c)
; y = x + a*b + *c
; *c = y / r
; return y % r

		EXPORT	adc3

		MOV	ip, #0		; ip := RdHi, a1 := RdLo
		UMLAL	a1, ip, a2, a3	; ip:a1 = x + a*b
		LDR	a2, [a4]
		ADDS	a1, a1, a2	;
		ADDCS	ip, ip, #1	; ip:a1 += *c	; or ADC  ip, ip, #0
		STR	ip, [a4]
		MOV	pc, lr



ads		; uint32 ads(uint32 c, uint32 *h, uint32 *l, uint32 a)
; y = 2*((*h)*r+(*l)) + a*a + c
; *l = y % r
; *h = (y / r) % r
; return y / r^2  (note: y / r^2 == 0, 1 or 2)

		EXPORT	ads

		MOV	ip, #0
		UMLAL	a1, ip, a4, a4
		LDR	a4, [a3]
		MOVS	a4, a4, LSL #1
		ADDCS	ip, ip, #1
		ADDS	a4, a1, a4
		STR	a4, [a3]
		LDR	a4, [a2]
		ADCS	a4, a4, a4
		MOVCC	a1, #0
		MOVCS	a1, #1
		ADDS	a4, ip, a4
		STR	a4, [a2]
		ADDCS	a1, a1, #1
		MOV	pc, lr



sbb1		; uint32 sbb1(uint32 x, uint32 *c)
; y = x - *c
; *c = - (y / r)
; return y % r

		EXPORT	sbb1

		MOV	ip, #0		; ip := RdHi, a1 := RdLo
		LDR	a3, [a2]
		SUBS	a1, a1, a3	;
		ADDCC	ip, ip, #1	; ip:a1 = x - *c
		STR	ip, [a2]
		MOV	pc, lr



sbb2		; uint32 sbb2(uint32 x, uint32 a, uint32 *c)
; y = x - a - *c
; *c = - (y / r)
; return y % r

		EXPORT	sbb2

		MOV	ip, #0		; ip := RdHi, a1 := RdLo
		SUBS	a1, a1, a2	;
		ADDCC	ip, ip, #1	; ip:a1 = x - a
		LDR	a2, [a3]
		SUBS	a1, a1, a2	;
		ADDCC	ip, ip, #1	; ip:a1 -= *c
		STR	ip, [a3]
		MOV	pc, lr



sbb3		; uint32 sbb3(uint32 x, uint32 a, uint32 b, uint32 *c)
; y = x - a*b - *c
; *c = - (y / r)
; return y % r

		EXPORT	sbb3

		UMULL	a2, ip, a3, a2
		SUBS	a1, a1, a2
		ADDCC	ip, ip, #1	; ip:a1 = x - a*b
		LDR	a2, [a4]
		SUBS	a1, a1, a2
		ADDCC	ip, ip, #1	; ip:a1 -= *c
		STR	ip, [a4]
		MOV	pc, lr



div64		; uint32 div64(uint32 h, uint32 l, uint32 d)

; compute (h*r+l) / d
; not check for overflow or division by 0

		EXPORT	div64

		RSB	a3, a3, #0	; a3 := NEG divisor
		MOV	a4, #32		; a4 := loop counter

lb1021		ADDS	a2, a2, a2	; a2 := quotient
		ADCS	a1, a1, a1	; a1 := remainder
		CMNCC	a1, a3
		ADDCS	a1, a1, a3
		ADDCS	a2, a2, #1	; or ADC  a2, a2, #0
		SUBS	a4, a4, #1
		BNE	lb1021

		MOV	a1, a2
		MOV	pc, lr



dsr		; int dsr(const uint32 *A)

; scan for the nonzero msw and return it's offset or 0 (if not found)

		EXPORT	dsr

		LDR	a2, [a1]	; a2 := offset from A
		CMP	a2, #0
		BEQ	lb1036

lb1031		LDR	a3, [a1, a2, LSL #2]	; because sizeof(uint32) == 4
		CMP	a3, #0
		BNE	lb1036
		SUBS	a2, a2, #1
		BNE	lb1031

lb1036		MOV	a1, a2
		MOV	pc, lr



window		; int window(const uint32 *w, int *i) // of size w=3

; return:
;  -  ((*i)-=1, 0) if 0...
;  -  ((*i)-=1, 1) if 10...
;  -  ((*i)-=2, 3) if 110...
;  -  ((*i)-=3, 5) if 101...
;  -  ((*i)-=3, 7) if 111...

; requirements:
;  -  little endian configuration
;  -  ((byte *)w)[(*i)>>3-1] == 0
;  -  *i >= 0

; *i = b31 ... b5 b4 ... b0
;	    |	      |
;	    |	      +-> start bit #
;	    +-----------> dword index

		EXPORT	window

		LDR	a3, [a2]
		LDRB	a4, [a1, a3, LSR #3]!
		LDRB	a1, [a1, #-1]
		ORR	a4, a1, a4, LSL #8
		AND	a1, a3, #7
		RSB	a1, a1, #24
		MOVS	a4, a4, LSL a1	; X XX......

		MOV	a1, #0
		SUB	a3, a3, #1
		BCC	lb1041		; 0XX
		ADC	a1, a1, a1
		MOVS	a4, a4, LSL #1
		SUBMI	a3, a3, #1
		ADCMI	a1, a1, a1
		MOVMIS	a4, a4, LSL #1
		SUBCS	a3, a3, #1
		ADCCS	a1, a1, a1

lb1041		STR	a3, [a2]
		MOV	pc, lr



modinv		; uint32 modinv(uint32 x)

; compute (-x)^(-1) mod r for x odd

		EXPORT	modinv

		STMFD	sp!, {v2, lr}
		MOV	lr, #0		; lr := 0
		MOV	a2, #1		; a2 := y
		MOV	a3, #2		; a3 := 2^(i-1)
lb1011		MUL	a4, a2, a1
		SUB	v2, lr, a3, LSL #1 ; v2 := NEG 2^i
		BIC	a4, a4, v2	; a4 := x*y mod 2^i
		CMP	a4, a3		; if x*y < 2^(i-1) (mod 2^i),
		ADDCC	a2, a2, a3	; then y += 2^(i-1).
		MOVS	a3, a3, LSL #1	; i++
		BCC	lb1011		; i <= log2(r)?
		MOV	a1, a2		; return y
		LDMFD	sp!, {v2, pc}



		END
