// DH12.h
//
// 99.09.06	dzchoi	Created



#ifndef DH_DEBUG

#include "comdef.h"

#else // DH_DEBUG

#define LOCAL static
#define MSG_ERROR(format, code1, code2, code3)
#define ERR(format, code1, code2, code3)

typedef unsigned uint32; // unsigned 32 bit value
typedef enum { FALSE, TRUE } boolean;

#endif // DH_DEBUG



// Functions from "dh1.s"

uint32 adc1(uint32, uint32 *);
uint32 adc2(uint32, uint32, uint32 *);
uint32 adc3(uint32, uint32, uint32, uint32 *);

uint32 ads(uint32, uint32 *, uint32 *, uint32);

uint32 sbb1(uint32, uint32 *);
uint32 sbb2(uint32, uint32, uint32 *);
uint32 sbb3(uint32, uint32, uint32, uint32 *);

uint32 div64(uint32, uint32, uint32);
int dsr(const uint32 *);
int window(const uint32 *, int *);
uint32 modinv(uint32);



// Functions from "dh2.c"

uint32 *ModExp(uint32 *, const uint32 *, const uint32 *);

