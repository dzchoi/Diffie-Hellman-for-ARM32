// DH2.c
//
// 99.09.06	dzchoi	Created
//
// To compile:
// ARMCC -apcs /interwork -c -li -Otime DH2.c DH1.o


// r := 2^32 (base)
// R := r^n
// N < R should be odd.
// R mod N = R - N if R/2 <= N < R

#include "dh12.h"



LOCAL void Add(uint32 *A, const uint32 *B, uint32 b, int i)
// return A += B*b*r^i mod r^(*A) for i >= 0
{
uint32 c = 0;
register int j;

  if ( b == 1 )
    for ( j = i+1 ; j-i <= *B && j <= *A ; j++ )
      A[j] = adc2(A[j], B[j-i], &c);
  else
    for ( j = i+1 ; j-i <= *B && j <= *A ; j++ )
      A[j] = adc3(A[j], b, B[j-i], &c);
  while ( c && j <= *A ) { // carry propagation
    A[j] = adc1(A[j], &c);
    j++;
  }
  // return ( A );
}

LOCAL void Sub(uint32 *A, const uint32 *B, uint32 b, int i)
// return A -= B*b*r^i mod r^(*A) for i >= 0
{
uint32 c = 0;
register int j;

  if ( b == 1 )
    for ( j = i+1 ; j-i <= *B && j <= *A ; j++ )
      A[j] = sbb2(A[j], B[j-i], &c);
  else
    for ( j = i+1 ; j-i <= *B && j <= *A ; j++ )
      A[j] = sbb3(A[j], b, B[j-i], &c);
  while ( c && j <= *A ) { // carry propagation
    A[j] = sbb1(A[j], &c);
    j++;
  }
  // return ( A );
}

LOCAL boolean LessOrEqual(const uint32 *A, const uint32 *B)
// return A <= B
{
register int i = dsr(A);
register int j = dsr(B);

  if ( i < j )
    return ( TRUE );
  if ( i > j )
    return ( FALSE );
  for ( ; i > 0 ; i-- ) {
    if ( A[i] < B[i] )
      return ( TRUE );
    if ( A[i] > B[i] )
      return ( FALSE );
  }
  return ( TRUE ); // A == B
}

extern uint32 *T;

LOCAL uint32 *MonRes(uint32 *A, const uint32 *N)
// return A = (A*R mod N) mod r^(*A)
// using CLASSICAL algorithm, where R = r^(*N)
// *T >= (*A)+(*N) is required
{
int i, n, t;

  t = *T; // save *T

  // T = A*R
  *T = *A + *N;
  for ( i = 1 ; i <= *N ; i++ )
    T[i] = 0;
  for ( i = 1 ; i <= *A ; i++ )
    T[i+*N] = A[i];

  n = dsr(N);
  i = dsr(T);

  if ( N[n] == -1 )
    while ( i > n ) {
      Sub(T, N, T[i], i-n-1);
      if ( T[i] == 0 )
	i--;
    }
  else
    while ( i > n ) {
      if ( T[i] > N[n] )
	Sub(T, N, div64(0, T[i], N[n]), i-n);
      else
	Sub(T, N, div64(T[i], T[i-1], N[n]+1), i-n-1);
      if ( T[i] == 0 )
	i--;
    }

  while ( LessOrEqual(N, T) ) // N <= T
    Sub(T, N, 1, 0);

  // A = T mod r^(*A)
  for ( i = 1 ; i <= *A ; i++ )
    A[i] = T[i];

  *T = t; // recover *T

  return ( A );
}

extern uint32 *U;

LOCAL uint32 *MonPro(uint32 *A, const uint32 *B, const uint32 *N, uint32 np0)
// return A = (A*B*R^(-1) mod N) mod r^(*A) for A*B <= N*R
// using SOS algorithm, where R = r^(*N)
// *T > (*A)+(*B) and *T > 2*(*N) are required
// A == B is possible
{
int i, m;

  // clear T
  for ( i = 1 ; i <= *T ; i++ )
    T[i] = 0;

  // T += A*B
  for ( i = 1 ; i <= *A ; i++ )
    Add(T, B, A[i], i-1);

  // T += M*N
  for ( i = 1 ; i <= *N ; i++ )
    Add(T, N, T[i]*np0, i-1);

  // U = T / R
  *U = *T - *N;

  if ( LessOrEqual(N, U) ) // N <= U
    Sub(U, N, 1, 0);

  // A = U mod r^(*A)
  m = *A < *N ? *A : *N;
  for ( i = 1 ; i <= m ; i++ )
    A[i] = U[i];
  while ( i <= *A )
    A[i++] = 0;

  return ( A );
}

LOCAL uint32 *MonSqr(uint32 *A, const uint32 *N, uint32 np0)
// return A = (A^2*R^(-1) mod N) mod r^(*A) for A^2 <= N*R, where R = r^(*N)
// *T > 2*(*A) and *T > 2*(*N) are required
{
uint32 c;
int i, j, m;

  // clear T
  for ( i = 1 ; i <= *T ; i++ )
    T[i] = 0;

  // T += Sum{ x[i]*x[j]*r^(i+j) for i < j < n } mod r^(T.n)
  for ( i = 1 ; i <= *A ; i++ ) {
    c = 0;
    for ( j = i+1 ; j <= *A && i+j-1 <= *T ; j++ )
      T[i+j-1] = adc3(T[i+j-1], A[i], A[j], &c);
    while ( c && i+j-1 <= *T ) {
      T[i+j-1] = adc1(T[i+j-1], &c);
      j++;
    }
  }

  // T = 2*T + Sum{ (x[i]*r^i)^2 for i = 0 .. n-1 } mod r^(T.n)
  c = 0;
  for ( i = j = 1 ; i <= *A && j <= *T ; i++, j+=2 )
    c = ads(c, T+j+1, T+j, A[i]); // BUG! possibly j+1 == (*T)+1
  while ( c && j <= *T ) {
    T[j] = adc1(T[j], &c);
    j++;
  }

  // T += M*N
  for ( i = 1 ; i <= *N ; i++ )
    Add(T, N, T[i]*np0, i-1);

  // U = T / R
  *U = *T - *N;

  if ( LessOrEqual(N, U) ) // N <= U
    Sub(U, N, 1, 0);

  // A = U mod r^(*A)
  m = *A < *N ? *A : *N;
  for ( i = 1 ; i <= m ; i++ )
    A[i] = U[i];
  while ( i <= *A )
    A[i++] = 0;

  return ( A );
}

LOCAL uint32 *MonRed(uint32 *A, const uint32 *N, uint32 np0)
// return A = (A*R^(-1) mod N) mod r^(*A) for A <= N*R, where R = r^(*N)
// *T > *A and *T > 2*(*N) are required
{
int i, m;

  // T = A
  for ( i = 1 ; i <= *A ; i++ )
    T[i] = A[i];
  while ( i <= *T )
    T[i++] = 0;

  // T += M*N
  for ( i = 1 ; i <= *N ; i++ )
    Add(T, N, T[i]*np0, i-1);

  // U = T / R
  *U = *T - *N;

  if ( LessOrEqual(N, U) ) // N <= U
    Sub(U, N, 1, 0);

  // A = U mod r^(*A)
  m = *A < *N ? *A : *N;
  for ( i = 1 ; i <= m ; i++ )
    A[i] = U[i];
  while ( i <= *A )
    A[i++] = 0;

  return ( A );
}



// From here, it is assumed that n == 16

LOCAL uint32 A1[] = { 16, // n == 16
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};
LOCAL uint32 A3[] = { 16, // n == 16
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};
LOCAL uint32 A5[] = { 16, // n == 16
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};
LOCAL uint32 A7[] = { 16, // n == 16
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};
LOCAL uint32 TT[] = { 33, // 2*n+1 == 33
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};

uint32 *T = TT;
uint32 *U = TT+16; // n == 16

uint32 *ModExp(uint32 *A, const uint32 *E, const uint32 *N)
// return A = A^E mod N for E > 0
// using WINDOW method with size w=3
// *A == *N == n is required
{
static uint32 *S[] = { A1, A3, A5, A7 };
uint32 np0;
int i, j, e;

  if ( *A != 16 || *N != 16 )
    MSG_ERROR("Both A and N must be 512-bit wide", 0, 0, 0);

  np0 = modinv(N[1]);
  MonRes(A, N); // to the Montgomery field

  for ( j = 1 ; j <= *A ; j++ )
    A1[j] = A[j];

  MonSqr(A, N, np0); // MonPro(A, A, N, np0);
  for ( j = 1 ; j <= *A ; j++ )
    A3[j] = A5[j] = A7[j] = A[j];
  MonPro(A3, A1, N, np0);
  MonPro(A5, A3, N, np0);
  MonPro(A7, A5, N, np0);

  i = (dsr(E)<<5) + 31; // r == 2^32
  if ( i < 32 )
    ERR("E == 0 in ModExp()", 0, 0, 0);
  while ( (e = window(E, &i)) == 0 ); // E > 0 is required
  for ( j = 1 ; j <= *A ; j++ )
    A[j] = S[e>>1][j]; // needs loop optimization

  j = i;
  while ( i >= 32 )
    if ( e = window(E, &j) ) {
      while ( i > j ) {
	MonSqr(A, N, np0); // MonPro(A, A, N, np0);
	i--;
      }
      MonPro(A, S[e>>1], N, np0);
    } else {
      MonSqr(A, N, np0); // MonPro(A, A, N, np0);
      i = j;
    }

  MonRed(A, N, np0); // back to the Normal field
  return ( A );
}



#ifdef DH_DEBUG

#include <stdio.h>
#include <time.h>

void main()
{
/*
// TEST-0 (from 7000F)
uint32 G[] = { 16,
  0x4EB31BE3, 0xB07EBB2F, 0x82227426, 0x94608A39,
  0xB141C77B, 0xB4F20B58, 0xD018CEBB, 0x7B8AF731,
  0x4A1BCAC7, 0x23FC1D40, 0x3D98B53F, 0x8787048F,
  0x149FCCB3, 0xEEF0725F, 0xF0663862, 0x031AEFD1
};
uint32 X[] = { 5,
  0x2AAE17FE, 0x659DD510, 0x6FD1991A, 0x06EA2B61, 0x128B5460
};
uint32 P[] = { 16,
  0x3C0BF24B, 0xD8F57745, 0x76134F06, 0xDE8E415F,
  0x10BC51FF, 0xA701BAA5, 0xFBA1A629, 0x4B61ED24,
  0xC9758AC0, 0xAEAC1F98, 0x759B2718, 0x1BAE3A82,
  0x2854FCE8, 0xDF3B9F06, 0xA35F6806, 0xD3BBB33C
};
*/
// TEST-1 (from Lucent Lab)
uint32 G[] = { 16,
  0xfc364b74,  0x79536c2, 0xb029cd23, 0xb8728e05,
  0x5cbc0710,          0,          0,          0,
           0,          0,          0,          0,
           0,          0,          0,          0,
};
uint32 X[] = { 5,
  0x1E61DF06, 0x0EC68013, 0xA6500D54, 0x066E4DE5, 0xDC090780
};
uint32 P[] = { 16,
  0xca07a241, 0x80a3fa9f,  0x3c23590, 0x9096ab31,
  0xf1d652d5, 0x70932b65, 0x77ed4de2, 0x13518543,
  0xe1d94885, 0x731986be, 0x6dbed20b, 0xb74fcfdd,
  0x58263142, 0xd4c5b3f3, 0x25cfb358, 0xb728b1e8
};
clock_t start, finish;
int i;

  start = clock();
  //for ( i = 0 ; i < 100 ; i++ )
    ModExp(G, X, P);
  finish = clock();

  for ( i = dsr(G) ; i > 0 ; i-- )
    printf("G[%d] = %08x\n", i, G[i]);

  printf("\nTIME = %2.2f sec\n", (double)(finish-start)/CLOCKS_PER_SEC);
}

/*
// test for little endian
{
char a[] = { 'D', 'C', 'B', 'A', 'Z', 'Y' };
uint32 *b;

  b = (uint32*)(a+2);

  printf("msb='%c', '%c', '%c', '%c'=lsb\n",
    (char)(*b>>24),
    (char)((*b>>16)&0x000000ff),
    (char)((*b>>8)&0x000000ff),
    (char)(*b&0x000000ff));
}
*/

#endif // DH_DEBUG

