
/*-------------------------------------------------------------*/
/*--- Block sorting machinery                               ---*/
/*---                                           blocksort.c ---*/
/*-------------------------------------------------------------*/

/* ------------------------------------------------------------------
   This file is part of bzip2/libbzip2, a program and library for
   lossless, block-sorting data compression.

   bzip2/libbzip2 version 1.0.8 of 13 July 2019
   Copyright (C) 1996-2019 Julian Seward <jseward@acm.org>

   Please read the WARNING, DISCLAIMER and PATENTS sections in the 
   README file.

   This program is released under the terms of the license contained
   in the file LICENSE.
   ------------------------------------------------------------------ */


#include <stdlib.h>
#include "bzlib_private.h"

/*---------------------------------------------*/
/*--- Fallback O(N log(N)^2) sorting        ---*/
/*--- algorithm, for repetitive blocks      ---*/
/*---------------------------------------------*/

#define initFreqTab(nblock, ftab, count) \
do { \
   int __i = nblock; \
   memset(ftab, 0, sizeof(ftab[0]) * count); \
   while (__i >= 4) { \
      ftab[INDEX(__i - 1)]++; \
      ftab[INDEX(__i - 2)]++; \
      ftab[INDEX(__i - 3)]++; \
      ftab[INDEX(__i - 4)]++; \
      __i = __i - 4; \
   } \
   while (__i-- > 0) { \
      ftab[INDEX(__i)]++; \
   } \
} while (0)

static void countFreqTab(UInt32 *ftab, int count)
{
   UInt32 sum = ftab[0];
   int i;
   for (i = 0; i < count; i += 8) {
      ftab[i+1] = (sum += ftab[i+1]);
      ftab[i+2] = (sum += ftab[i+2]);
      ftab[i+3] = (sum += ftab[i+3]);
      ftab[i+4] = (sum += ftab[i+4]);
      ftab[i+5] = (sum += ftab[i+5]);
      ftab[i+6] = (sum += ftab[i+6]);
      ftab[i+7] = (sum += ftab[i+7]);
      ftab[i+8] = (sum += ftab[i+8]);
   }
}

#define sortFreqTab(nblock, ftab, fmap) \
do { \
   int __i = nblock; \
   while (__i >= 4) { \
      fmap[--ftab[INDEX(__i - 1)]] = __i - 1; \
      fmap[--ftab[INDEX(__i - 2)]] = __i - 2; \
      fmap[--ftab[INDEX(__i - 3)]] = __i - 3; \
      fmap[--ftab[INDEX(__i - 4)]] = __i - 4; \
      __i = __i - 4; \
   } \
   while (__i-- > 0) { \
      fmap[--ftab[INDEX(__i)]] = __i; \
   } \
} while (0)

#define bz_swap(zz1, zz2) \
   { Int32 zztmp = zz1; zz1 = zz2; zz2 = zztmp; }

#define bz_vswap(zzp1, zzp2, zzn)     \
{                                     \
   Int32 yyp1 = (zzp1);               \
   Int32 yyp2 = (zzp2);               \
   Int32 yyn  = (zzn);                \
   while (yyn-- > 0) {                \
      bz_swap(fmap[yyp1], fmap[yyp2]);\
      yyp1++; yyp2++;                 \
   }                                  \
}

#define bz_min(a,b) ((a) < (b)) ? (a) : (b)

/*---------------------------------------------*/
static 
__inline__
void fallbackSimpleSort ( UInt32* fmap, 
                          UInt32* eclass, 
                          Int32   lo, 
                          Int32   hi )
{
   Int32 i, j, tmp;
   UInt32 ec_tmp;

   if (lo == hi) return;

   if (hi - lo > 3) {
      for ( i = hi-4; i >= lo; i-- ) {
         tmp = fmap[i];
         ec_tmp = eclass[tmp];
         for ( j = i+4; j <= hi && ec_tmp > eclass[fmap[j]]; j += 4 )
            fmap[j-4] = fmap[j];
         fmap[j-4] = tmp;
      }
   }

   for ( i = hi-1; i >= lo; i-- ) {
      tmp = fmap[i];
      ec_tmp = eclass[tmp];
      for ( j = i+1; j <= hi && ec_tmp > eclass[fmap[j]]; j++ )
         fmap[j-1] = fmap[j];
      fmap[j-1] = tmp;
   }
}


/*---------------------------------------------*/
#define fpush(lz,hz) { stackLo[sp] = lz; \
                       stackHi[sp] = hz; \
                       sp++; }

#define fpop(lz,hz) { sp--;              \
                      lz = stackLo[sp];  \
                      hz = stackHi[sp]; }

#define FALLBACK_QSORT_SMALL_THRESH 10
#define FALLBACK_QSORT_STACK_SIZE   100


static
void fallbackQSort3 ( UInt32* fmap, 
                      UInt32* eclass,
                      Int32   loSt, 
                      Int32   hiSt )
{
   Int32 unLo, unHi, ltLo, gtHi, n, m;
   Int32 sp, lo, hi;
   UInt32 med, r, r3;
   Int32 stackLo[FALLBACK_QSORT_STACK_SIZE];
   Int32 stackHi[FALLBACK_QSORT_STACK_SIZE];

   r = 0;

   sp = 0;
   fpush ( loSt, hiSt );

   for (;;) {

      AssertH ( sp < FALLBACK_QSORT_STACK_SIZE - 1, 1004 );

      fpop ( lo, hi );
      if (hi - lo < FALLBACK_QSORT_SMALL_THRESH) {
         fallbackSimpleSort ( fmap, eclass, lo, hi );
         if (sp == 0) return;
         continue;
      }

      /* Random partitioning.  Median of 3 sometimes fails to
         avoid bad cases.  Median of 9 seems to help but 
         looks rather expensive.  This too seems to work but
         is cheaper.  Guidance for the magic constants 
         7621 and 32768 is taken from Sedgewick's algorithms
         book, chapter 35.
      */
      r = ((r * 7621) + 1) % 32768;
      r3 = r % 3;
      if (r3 == 0) med = eclass[fmap[ lo          ]]; else
      if (r3 == 1) med = eclass[fmap[(lo + hi) / 2]]; else
                   med = eclass[fmap[ hi          ]];

      unLo = ltLo = lo;
      unHi = gtHi = hi;

      do {
         for (;;) {
            n = (Int32)eclass[fmap[unLo]] - (Int32)med;
            if (n > 0) break;
            if (n == 0) { 
               bz_swap(fmap[unLo], fmap[ltLo]);
               ltLo++;
            }
            unLo++;
            if (unLo > unHi)
               goto out;
         }
         for (;;) {
            n = (Int32)eclass[fmap[unHi]] - (Int32)med;
            if (n < 0) break;
            if (n == 0) { 
               bz_swap(fmap[unHi], fmap[gtHi]);
               gtHi--;
            }
            unHi--;
            if (unLo > unHi)
               goto out;
         }
         bz_swap(fmap[unLo], fmap[unHi]); unLo++; unHi--;
      } while (unLo <= unHi);
out:
      AssertD ( unHi == unLo-1, "fallbackQSort3(2)" );

      if (gtHi < ltLo) {
          if (sp == 0) return;
          continue;
      }

      n = bz_min(ltLo - lo, unLo - ltLo); bz_vswap(lo, unLo - n, n);
      m = bz_min(hi - gtHi, gtHi - unHi); bz_vswap(unLo, hi - m + 1, m);

      n = lo + unLo - ltLo - 1;
      m = hi + unHi - gtHi + 1;

      if (n - lo > hi - m) {
         fpush ( lo, n );
         fpush ( m, hi );
      } else {
         fpush ( m, hi );
         fpush ( lo, n );
      }
   }
}

#undef fpush
#undef fpop
#undef FALLBACK_QSORT_SMALL_THRESH
#undef FALLBACK_QSORT_STACK_SIZE


/*---------------------------------------------*/
/* Pre:
      nblock > 0
      eclass exists for [0 .. nblock-1]
      ((UChar*)eclass) [0 .. nblock-1] holds block
      ptr exists for [0 .. nblock-1]

   Post:
      ((UChar*)eclass) [0 .. nblock-1] holds block
      All other areas of eclass destroyed
      fmap [0 .. nblock-1] holds sorted order
      bhtab [ 0 .. 2+(nblock/32) ] destroyed
*/

#define       SET_BH(zz)  bhtab[(zz) >> 5] |= ((UInt32)1 << ((zz) & 31))
#define     CLEAR_BH(zz)  bhtab[(zz) >> 5] &= ~((UInt32)1 << ((zz) & 31))
#define     ISSET_BH(zz)  (bhtab[(zz) >> 5] & ((UInt32)1 << ((zz) & 31)))
#define      WORD_BH(zz)  bhtab[(zz) >> 5]
#define UNALIGNED_BH(zz)  ((zz) & 31)

static
void fallbackSort ( UInt32* fmap, 
                    UInt32* eclass, 
                    UInt32* bhtab,
                    Int32   nblock,
                    Int32   verb )
{
   UInt32 ftab[257];
   UInt32 ftabCopy[256];
   Int32 H, i, j, k, l, r, cc, cc1;
   Int32 nNotDone;
   UChar* eclass8 = (UChar*)eclass;

   /*--
      Initial 1-char radix sort to generate
      initial fmap and initial BH bits.
   --*/
   if (verb >= 4)
      VPrintf0 ( "        bucket sorting ...\n" );

#define INDEX(i) eclass8[i]

   initFreqTab(nblock, ftab, 257);
   memcpy(ftabCopy, ftab, sizeof(ftabCopy));
   countFreqTab(ftab, 256);
   sortFreqTab(nblock, ftab, fmap);

#undef INDEX

   memset(bhtab, 0, sizeof(bhtab[0]) * ((nblock + 31) / 32));
   for (i = 0; i < 256; i += 8) {
      SET_BH(ftab[i + 0]);
      SET_BH(ftab[i + 1]);
      SET_BH(ftab[i + 2]);
      SET_BH(ftab[i + 3]);
      SET_BH(ftab[i + 4]);
      SET_BH(ftab[i + 5]);
      SET_BH(ftab[i + 6]);
      SET_BH(ftab[i + 7]);
  }

   /*--
      Inductively refine the buckets.  Kind-of an
      "exponential radix sort" (!), inspired by the
      Manber-Myers suffix array construction algorithm.
   --*/

   /*-- set sentinel bits for block-end detection --*/
   if (UNALIGNED_BH(nblock)) {
      bhtab[(nblock >> 5) + 0] |= 0x55555555 << (nblock & 31);
      bhtab[(nblock >> 5) + 1] = 0x55555555 << (nblock & 1);
      bhtab[(nblock >> 5) + 2] = 0x55555555 >> (32 - (nblock & 31));
   } else {
      bhtab[(nblock >> 5) + 0] = 0x55555555;
      bhtab[(nblock >> 5) + 1] = 0x55555555;
   }

   /*-- the log(N) loop --*/
   H = 1;
   do {

      if (verb >= 4) 
         VPrintf1 ( "        depth %6d has ", H );

      j = 0;
      for (i = 0; i < nblock; i++) {
         if (ISSET_BH(i)) j = i;
         k = fmap[i] - H; if (k < 0) k += nblock;
         eclass[k] = j;
      }

      nNotDone = 0;
      r = -1;
      while (1) {
         UInt32 curr;

	 /*-- find the next non-singleton bucket --*/
         k = r + 1;
         curr = WORD_BH(k);
         if (UNALIGNED_BH(k)) {
            curr |= (1 << (k & 31)) - 1;
            k -= k & 31;
         }
         while (!(curr + 1)) {
            k += 32;
            curr = WORD_BH(k);
         }
         k += 31 - __builtin_clz(~curr & (curr + 1));
         l = k - 1;
         if (l >= nblock) break;

         if (UNALIGNED_BH(k)) {
            curr &= curr + 1;
            k -= k & 31;
         }
         while (!curr) {
            k += 32;
            curr = WORD_BH(k);
         }
         k += 31 - __builtin_clz(curr & -curr);
         r = k - 1;
         if (r >= nblock) break;

         /*-- now [l, r] bracket current bucket --*/
         /*if (r > l)*/ {
            nNotDone += (r - l + 1);
            fallbackQSort3 ( fmap, eclass, l, r );

            /*-- scan bucket and generate header bits-- */
            cc = -1;
            for (i = l; i <= r; i++) {
               cc1 = eclass[fmap[i]];
               if (cc != cc1) { SET_BH(i); cc = cc1; };
            }
         }
      }

      if (verb >= 4) 
         VPrintf1 ( "%6d unresolved strings\n", nNotDone );

      H *= 2;
   } while (H <= nblock && nNotDone != 0);

   /*-- 
      Reconstruct the original block in
      eclass8 [0 .. nblock-1], since the
      previous phase destroyed it.
   --*/
   if (verb >= 4)
      VPrintf0 ( "        reconstructing block ...\n" );

   j = 0;
   for (i = 0; i < nblock; i++) {
      while (ftabCopy[j] == 0) j++;
      ftabCopy[j]--;
      eclass8[fmap[i]] = (UChar)j;
   }
   AssertH ( j < 256, 1005 );
}

#undef       SET_BH
#undef     CLEAR_BH
#undef     ISSET_BH
#undef      WORD_BH
#undef UNALIGNED_BH


/*---------------------------------------------*/
/*--- The main, O(N^2 log(N)) sorting       ---*/
/*--- algorithm.  Faster for "normal"       ---*/
/*--- non-repetitive blocks.                ---*/
/*---------------------------------------------*/

/*---------------------------------------------*/
static
__inline__
Bool mainGtU ( UInt32  i1, 
               UInt32  i2,
               UChar*  block, 
               UInt16* quadrant,
               UInt32  nblock,
               Int32*  budget )
{
   Int32 k;
   ULong c1, c2;
   ULong s1, s2;
   ULong chk, mask;

   AssertD ( i1 != i2, "mainGtU" );

#define NOT_EQU(x, y) (BZ_LITTLE_ENDIAN() ? (chk = x ^ y) : (x != y))

   c1 = ((una_ulong*)(block + i1))->x;
   c2 = ((una_ulong*)(block + i2))->x;
   if (NOT_EQU(c1, c2)) goto out1;
   if (sizeof(long) == 8) {
      c1 = ((una_u32*)(block + i1 + 8))->x;
      c2 = ((una_u32*)(block + i2 + 8))->x;
      if (NOT_EQU(c1, c2)) goto out1;
   } else {
      c1 = ((una_ulong*)(block + i1 + 4))->x;
      c2 = ((una_ulong*)(block + i2 + 4))->x;
      if (NOT_EQU(c1, c2)) goto out1;
      c1 = ((una_ulong*)(block + i1 + 8))->x;
      c2 = ((una_ulong*)(block + i2 + 8))->x;
      if (NOT_EQU(c1, c2)) goto out1;
   }

   i1 += 12;
   i2 += 12;
   k = nblock + 8;

   do {
      c1 = ((una_ulong*)(block + i1))->x;
      c2 = ((una_ulong*)(block + i2))->x;
      if ((chk = c1 ^ c2)) goto out2;
      s1 = ((una_ulong*)(quadrant + i1))->x;
      s2 = ((una_ulong*)(quadrant + i2))->x;
      if (NOT_EQU(s1, s2)) goto out3;
      s1 = ((una_ulong*)(quadrant + i1 + sizeof(long) / 2))->x;
      s2 = ((una_ulong*)(quadrant + i2 + sizeof(long) / 2))->x;
      if (NOT_EQU(s1, s2)) goto out3;
      if (sizeof(long) == 4) {
         c1 = ((una_ulong*)(block + i1 + 4))->x;
         c2 = ((una_ulong*)(block + i2 + 4))->x;
         if ((chk = c1 ^ c2)) goto out4;
         s1 = ((una_ulong*)(quadrant + i1 + 4))->x;
         s2 = ((una_ulong*)(quadrant + i2 + 4))->x;
         if (NOT_EQU(s1, s2)) goto out3;
         s1 = ((una_ulong*)(quadrant + i1 + 6))->x;
         s2 = ((una_ulong*)(quadrant + i2 + 6))->x;
         if (NOT_EQU(s1, s2)) goto out3;
      }

      i1 += 8;
      if (i1 >= nblock) i1 -= nblock;
      i2 += 8;
      if (i2 >= nblock) i2 -= nblock;

      (*budget)--;
      k -= 8;
   } while (k >= 0);

   return False;

out1:
   if (BZ_LITTLE_ENDIAN()) {
      mask = 0xFFUL << ((__builtin_ffsl(chk) - 1) & (BITS_PER_LONG - 8));
      c1 &= mask;
      c2 &= mask;
   }
   return (c1 > c2);

out4:
   if (sizeof(long) == 4) {
      i1 += 4;
      i2 += 4;
   }
out2:
   if (BZ_LITTLE_ENDIAN()) {
      k = (__builtin_ffsl(chk) - 1) / 8;
      if (k == 0)
         return ((c1 & 0xFF) > (c2 & 0xFF));
      mask = 0xFFUL << (k * 8);
   } else {
      k = __builtin_clzl(chk) / 8;
      if (k == 0)
         return (c1 > c2);
   }
   s1 = ((una_ulong*)(quadrant + i1))->x;
   s2 = ((una_ulong*)(quadrant + i2))->x;
   if (!(chk = s1 ^ s2)) {
      if (k < sizeof(long) / 2) {
         if (BZ_LITTLE_ENDIAN()) {
            c1 &= mask;
            c2 &= mask;
         }
         return (c1 > c2);
      }
      s1 = ((una_ulong*)(quadrant + i1 + sizeof(long) / 2))->x;
      s2 = ((una_ulong*)(quadrant + i2 + sizeof(long) / 2))->x;
      if (!(chk = s1 ^ s2)) {
         if (BZ_LITTLE_ENDIAN()) {
            c1 &= mask;
            c2 &= mask;
         }
         return (c1 > c2);
      }
      k -= sizeof(long) / 2;
   }
   if (BZ_LITTLE_ENDIAN()) {
      Int32 j = (__builtin_ffsl(chk) - 1) / 16;
      if (k <= j) {
         c1 &= mask;
         c2 &= mask;
         return (c1 > c2);
      }
      mask = 0xFFFFUL << (j * 16);
      s1 &= mask;
      s2 &= mask;
   } else {
      Int32 j = __builtin_clzl(chk) / 16;
      if (k <= j)
         return (c1 > c2);
   }
   return (s1 > s2);

out3:
   if (BZ_LITTLE_ENDIAN()) {
      mask = 0xFFFFUL << ((__builtin_ffsl(chk) - 1) & (BITS_PER_LONG - 16));
      s1 &= mask;
      s2 &= mask;
   }
   return (s1 > s2);
}


/*---------------------------------------------*/
/*--
   Knuth's increments seem to work better
   than Incerpi-Sedgewick here.  Possibly
   because the number of elems to sort is
   usually small, typically <= 20.
--*/
static const
Int32 incs[14] = { 1, 4, 13, 40, 121, 364, 1093, 3280,
                   9841, 29524, 88573, 265720,
                   797161, 2391484 };

static
Int32 mainSimpleSort ( UInt32* fmap,
                      UChar*  block,
                      UInt16* quadrant,
                      Int32   nblock,
                      Int32   lo, 
                      Int32   hi, 
                      Int32   d,
                      Int32   budget )
{
   Int32 i, j, h, bigN, hp;
   UInt32 v;

   bigN = hi - lo + 1;
   if (bigN < 2) return budget;

   hp = 0;
   while (incs[hp] < bigN) hp++;

   while (--hp >= 0) {
      h = incs[hp];

      i = lo + h;
      do {

         /*-- copy 1 --*/
         if (i > hi) break;
         v = fmap[i];
         j = i;
         while ( mainGtU ( 
                    fmap[j - h] + d, v + d, block, quadrant, nblock, &budget
                 ) ) {
            fmap[j] = fmap[j - h];
            j = j - h;
            if (j <= (lo + h - 1)) break;
         }
         fmap[j] = v;
         i++;

         /*-- copy 2 --*/
         if (i > hi) break;
         v = fmap[i];
         j = i;
         while ( mainGtU ( 
                    fmap[j - h] + d, v + d, block, quadrant, nblock, &budget
                 ) ) {
            fmap[j] = fmap[j - h];
            j = j - h;
            if (j <= (lo + h - 1)) break;
         }
         fmap[j] = v;
         i++;

         /*-- copy 3 --*/
         if (i > hi) break;
         v = fmap[i];
         j = i;
         while ( mainGtU ( 
                    fmap[j - h] + d, v + d, block, quadrant, nblock, &budget
                 ) ) {
            fmap[j] = fmap[j-h];
            j = j - h;
            if (j <= (lo + h - 1)) break;
         }
         fmap[j] = v;
         i++;

      } while (budget >= 0);
   }
	return budget;
}


/*---------------------------------------------*/
/*--
   The following is an implementation of
   an elegant 3-way quicksort for strings,
   described in a paper "Fast Algorithms for
   Sorting and Searching Strings", by Robert
   Sedgewick and Jon L. Bentley.
--*/

static 
__inline__
UChar mmed3 ( UChar a, UChar b, UChar c )
{
   UChar t;
   if (a > b) { t = a; a = b; b = t; };
   if (b > c) { 
      b = c;
      if (a > b) b = a;
   }
   return b;
}

#define mpush(lz,hz,dz) { stackLo[sp] = lz; \
                          stackHi[sp] = hz; \
                          stackD [sp] = dz; \
                          sp++; }

#define mpop(lz,hz,dz) { sp--;             \
                         lz = stackLo[sp]; \
                         hz = stackHi[sp]; \
                         dz = stackD [sp]; }


#define mnextsize(az) (nextHi[az] - nextLo[az])

#define mnextswap(az,bz)                                        \
   { Int32 tz;                                                  \
     tz = nextLo[az]; nextLo[az] = nextLo[bz]; nextLo[bz] = tz; \
     tz = nextHi[az]; nextHi[az] = nextHi[bz]; nextHi[bz] = tz; \
     tz = nextD [az]; nextD [az] = nextD [bz]; nextD [bz] = tz; }


#define MAIN_QSORT_SMALL_THRESH 20
#define MAIN_QSORT_DEPTH_THRESH (BZ_N_RADIX + BZ_N_QSORT)
#define MAIN_QSORT_STACK_SIZE 100

static
Int32 mainQSort3 ( UInt32* fmap,
                  UChar*  block,
                  UInt16* quadrant,
                  Int32   nblock,
                  Int32   loSt, 
                  Int32   hiSt, 
                  Int32   dSt,
                  Int32   budget )
{
   Int32 unLo, unHi, ltLo, gtHi, n, m, med;
   Int32 sp, lo, hi, d;

   Int32 stackLo[MAIN_QSORT_STACK_SIZE];
   Int32 stackHi[MAIN_QSORT_STACK_SIZE];
   Int32 stackD [MAIN_QSORT_STACK_SIZE];

   Int32 nextLo[3];
   Int32 nextHi[3];
   Int32 nextD [3];

   sp = 0;
   mpush ( loSt, hiSt, dSt );

   for (;;) {

      AssertH ( sp < MAIN_QSORT_STACK_SIZE - 2, 1001 );

      mpop ( lo, hi, d );
      if (hi - lo < MAIN_QSORT_SMALL_THRESH || 
          d > MAIN_QSORT_DEPTH_THRESH) {
         budget = mainSimpleSort ( fmap, block, quadrant, nblock, lo, hi, d, budget );
         if (budget < 0 || sp == 0) return budget;
         continue;
      }

      med = (Int32) 
            mmed3 ( block[fmap[ lo            ] + d],
                    block[fmap[ hi            ] + d],
                    block[fmap[ (lo + hi) / 2 ] + d] );

      unLo = ltLo = lo;
      unHi = gtHi = hi;

      do {
         for (;;) {
            n = ((Int32)block[fmap[unLo] + d]) - med;
            if (n >  0) break;
            if (n == 0) { 
               bz_swap(fmap[unLo], fmap[ltLo]);
               ltLo++;
            }
            unLo++;
            if (unLo > unHi)
               goto out;
         }
         for (;;) {
            n = ((Int32)block[fmap[unHi] + d]) - med;
            if (n <  0) break;
            if (n == 0) { 
               bz_swap(fmap[unHi], fmap[gtHi]);
               gtHi--;
            }
            unHi--;
            if (unLo > unHi)
               goto out;
         }
         bz_swap(fmap[unLo], fmap[unHi]); unLo++; unHi--;
      } while (unLo <= unHi);
out:
      AssertD ( unHi == unLo-1, "mainQSort3(2)" );

      if (gtHi < ltLo) {
         mpush(lo, hi, d+1 );
         continue;
      }

      n = bz_min(ltLo - lo, unLo - ltLo); bz_vswap(lo, unLo - n, n);
      m = bz_min(hi - gtHi, gtHi - unHi); bz_vswap(unLo, hi - m + 1, m);

      n = lo + unLo - ltLo - 1;
      m = hi + unHi - gtHi + 1;

      nextLo[0] = lo;  nextHi[0] = n;   nextD[0] = d;
      nextLo[1] = m;   nextHi[1] = hi;  nextD[1] = d;
      nextLo[2] = n+1; nextHi[2] = m-1; nextD[2] = d+1;

      if (mnextsize(0) < mnextsize(1)) mnextswap(0,1);
      if (mnextsize(1) < mnextsize(2)) mnextswap(1,2);
      if (mnextsize(0) < mnextsize(1)) mnextswap(0,1);

      AssertD (mnextsize(0) >= mnextsize(1), "mainQSort3(8)" );
      AssertD (mnextsize(1) >= mnextsize(2), "mainQSort3(9)" );

      mpush (nextLo[0], nextHi[0], nextD[0]);
      mpush (nextLo[1], nextHi[1], nextD[1]);
      mpush (nextLo[2], nextHi[2], nextD[2]);
   }
	return budget;
}

#undef mpush
#undef mpop
#undef mnextsize
#undef mnextswap
#undef MAIN_QSORT_SMALL_THRESH
#undef MAIN_QSORT_DEPTH_THRESH
#undef MAIN_QSORT_STACK_SIZE


/*---------------------------------------------*/
/* Pre:
      nblock > N_OVERSHOOT
      block32 exists for [0 .. nblock-1 +N_OVERSHOOT]
      ((UChar*)block32) [0 .. nblock-1] holds block
      ptr exists for [0 .. nblock-1]

   Post:
      ((UChar*)block32) [0 .. nblock-1] holds block
      All other areas of block32 destroyed
      ftab [0 .. 65536 ] destroyed
      ptr [0 .. nblock-1] holds sorted order
      if (*budget < 0), sorting was abandoned
*/

#define BIGFREQ(b) (ftab[((b)+1) << 8] - ftab[(b) << 8])
#define SETMASK (1 << 21)
#define CLEARMASK (~(SETMASK))

static
Int32 mainSort ( UInt32* fmap,
                UChar*  block,
                UInt16* quadrant, 
                UInt32* ftab,
                Int32   nblock,
                Int32   verb,
                Int32   budget )
{
   Int32  i, j, k, ss, sb;
   LOCAL_DECALRE_ALIGNED_ARRAY(UChar, runningOrder, 256, sizeof(long));
   Bool   bigDone[256];
   Int32  copyStart[256];
   Int32  copyEnd  [256];
   UChar  c1;
   Int32  numQSorted;

   if (verb >= 4) VPrintf0 ( "        main sort initialise ...\n" );

   /*-- set up the 2-byte frequency table --*/
#define INDEX(i) (j = (j >> 8) | ( ((UInt16)block[i]) << 8))

   j = block[0] << 8;
   initFreqTab(nblock, ftab, 65537);

   /*-- (emphasises close relationship of block & quadrant) --*/
   memcpy(block + nblock, block, sizeof(block[0]) * BZ_N_OVERSHOOT);
   memset(quadrant, 0, sizeof(quadrant[0]) * (nblock + BZ_N_OVERSHOOT));

   if (verb >= 4) VPrintf0 ( "        bucket sorting ...\n" );

   /*-- Complete the initial radix sort --*/
   countFreqTab(ftab, 65536);

   j = block[0] << 8;
   sortFreqTab(nblock, ftab, fmap);

#undef INDEX

   /*--
      Now ftab contains the first loc of every small bucket.
      Calculate the running order, from smallest to largest
      big bucket.
   --*/
   memset(bigDone, 0, sizeof(bigDone[0]) * 256);
   BZ2_IndexTableInit(runningOrder, 256);

   {
      Int32 h = 1;
      do h = 3 * h + 1; while (h <= 256);

      do {
         h = h / 3;
         for (i = h; i <= 255; i++) {
            UChar vv = runningOrder[i];
            j = i;
            while ( BIGFREQ(runningOrder[j - h]) > BIGFREQ(vv) ) {
               runningOrder[j] = runningOrder[j - h];
               j = j - h;
               if (j < h) break;
            }
            runningOrder[j] = vv;
         }
      } while (h != 1);
   }

   /*--
      The main sorting loop.
   --*/

   numQSorted = 0;

   for (i = 0; i <= 255; i++) {

      /*--
         Process big buckets, starting with the least full.
         Basically this is a 3-step process in which we call
         mainQSort3 to sort the small buckets [ss, j], but
         also make a big effort to avoid the calls if we can.
      --*/
      ss = runningOrder[i];

      /*--
         Step 1:
         Complete the big bucket [ss] by quicksorting
         any unsorted small buckets [ss, j], for j != ss.  
         Hopefully previous pointer-scanning phases have already
         completed many of the small buckets [ss, j], so
         we don't have to sort them at all.
      --*/
      for (j = 0; j <= 255; j++) {
         if (j != ss) {
            sb = (ss << 8) + j;
            if ( ! (ftab[sb] & SETMASK) ) {
               Int32 lo =  ftab[sb  ] & CLEARMASK;
               Int32 hi = (ftab[sb+1] & CLEARMASK) - 1;
               if (hi > lo) {
                  if (verb >= 4)
                     VPrintf4 ( "        qsort [0x%x, 0x%x]   "
                                "done %d   this %d\n",
                                ss, j, numQSorted, hi - lo + 1 );
                  budget = mainQSort3 (
                     fmap, block, quadrant, nblock,
                     lo, hi, BZ_N_RADIX, budget 
                  );
                  if (budget < 0) return budget;
                  numQSorted += (hi - lo + 1);
               }
            }
            ftab[sb] |= SETMASK;
         }
      }

      AssertH ( !bigDone[ss], 1006 );

      /*--
         Step 2:
         Now scan this big bucket [ss] so as to synthesise the
         sorted order for small buckets [t, ss] for all t,
         including, magically, the bucket [ss,ss] too.
         This will avoid doing Real Work in subsequent Step 1's.
      --*/
      {
         for (j = 0; j <= 255; j++) {
            copyStart[j] =  ftab[(j << 8) + ss    ] & CLEARMASK;
            copyEnd  [j] = (ftab[(j << 8) + ss + 1] & CLEARMASK) - 1;
         }
         for (j = ftab[ss << 8] & CLEARMASK; j < copyStart[ss]; j++) {
            k = fmap[j]-1; if (k < 0) k += nblock;
            c1 = block[k];
            if (!bigDone[c1])
               fmap[ copyStart[c1]++ ] = k;
         }
         for (j = (ftab[(ss << 8) + 256] & CLEARMASK) - 1; j > copyEnd[ss]; j--) {
            k = fmap[j]-1; if (k < 0) k += nblock;
            c1 = block[k];
            if (!bigDone[c1]) 
               fmap[ copyEnd[c1]-- ] = k;
         }
      }

      AssertH ( (copyStart[ss]-1 == copyEnd[ss])
                || 
                /* Extremely rare case missing in bzip2-1.0.0 and 1.0.1.
                   Necessity for this case is demonstrated by compressing 
                   a sequence of approximately 48.5 million of character 
                   251; 1.0.0/1.0.1 will then die here. */
                (copyStart[ss] == 0 && copyEnd[ss] == nblock-1),
                1007 )

      for (j = 0; j < 256; j += 8) {
         ftab[(j << 8) + ss + (0 << 8)] |= SETMASK;
         ftab[(j << 8) + ss + (1 << 8)] |= SETMASK;
         ftab[(j << 8) + ss + (2 << 8)] |= SETMASK;
         ftab[(j << 8) + ss + (3 << 8)] |= SETMASK;
         ftab[(j << 8) + ss + (4 << 8)] |= SETMASK;
         ftab[(j << 8) + ss + (5 << 8)] |= SETMASK;
         ftab[(j << 8) + ss + (6 << 8)] |= SETMASK;
         ftab[(j << 8) + ss + (7 << 8)] |= SETMASK;
      }

      /*--
         Step 3:
         The [ss] big bucket is now done.  Record this fact,
         and update the quadrant descriptors.  Remember to
         update quadrants in the overshoot area too, if
         necessary.  The "if (i < 255)" test merely skips
         this updating for the last bucket processed, since
         updating for the last bucket is pointless.

         The quadrant array provides a way to incrementally
         cache sort orderings, as they appear, so as to 
         make subsequent comparisons in fullGtU() complete
         faster.  For repetitive blocks this makes a big
         difference (but not big enough to be able to avoid
         the fallback sorting mechanism, exponential radix sort).

         The precise meaning is: at all times:

            for 0 <= i < nblock and 0 <= j <= nblock

            if block[i] != block[j], 

               then the relative values of quadrant[i] and 
                    quadrant[j] are meaningless.

               else {
                  if quadrant[i] < quadrant[j]
                     then the string starting at i lexicographically
                     precedes the string starting at j

                  else if quadrant[i] > quadrant[j]
                     then the string starting at j lexicographically
                     precedes the string starting at i

                  else
                     the relative ordering of the strings starting
                     at i and j has not yet been determined.
               }
      --*/
      bigDone[ss] = True;

      if (i < 255) {
         Int32 bbStart  =  ftab[ ss << 8       ] & CLEARMASK;
         Int32 bbSize   = (ftab[(ss << 8) + 256] & CLEARMASK) - bbStart;
         Int32 shifts   = 0;

         while ((bbSize >> shifts) > 65534) shifts++;

         for (j = bbSize-1; j >= 0; j--) {
            Int32 a2update     = fmap[bbStart + j];
            UInt16 qVal        = (UInt16)(j >> shifts);
            quadrant[a2update] = qVal;
            if (a2update < BZ_N_OVERSHOOT)
               quadrant[a2update + nblock] = qVal;
         }
         AssertH ( ((bbSize-1) >> shifts) <= 65535, 1002 );
      }

   }

   if (verb >= 4)
      VPrintf3 ( "        %d pointers, %d sorted, %d scanned\n",
                 nblock, numQSorted, nblock - numQSorted );
	return budget;
}

#undef BIGFREQ
#undef SETMASK
#undef CLEARMASK


/*---------------------------------------------*/
/* Pre:
      nblock > 0
      arr2 exists for [0 .. nblock-1 +N_OVERSHOOT]
      ((UChar*)arr2)  [0 .. nblock-1] holds block
      arr1 exists for [0 .. nblock-1]

   Post:
      ((UChar*)arr2) [0 .. nblock-1] holds block
      All other areas of block destroyed
      ftab [ 0 .. 65536 ] destroyed
      arr1 [0 .. nblock-1] holds sorted order
*/
void BZ2_blockSort ( EState* s )
{
   UInt32* ptr    = s->ptr; 
   UChar*  block  = s->block;
   UInt32* ftab   = s->ftab;
   Int32   nblock = s->nblock;
   Int32   verb   = s->verbosity;
   Int32   wfact  = s->workFactor;
   UInt16* quadrant;
   Int32   budget;
   Int32   budgetInit;
   Int32   i;

   if (nblock < 10000) {
      fallbackSort ( s->arr1, s->arr2, ftab, nblock, verb );
   } else {
      /* Calculate the location for quadrant, remembering to get
         the alignment right.  Assumes that &(block[0]) is at least
         2-byte aligned -- this should be ok since block is really
         the first section of arr2.
      */
      i = nblock+BZ_N_OVERSHOOT;
      i += (i & 1);
      quadrant = (UInt16*)(&(block[i]));

      /* (wfact-1) / 3 puts the default-factor-30
         transition point at very roughly the same place as 
         with v0.1 and v0.9.0.  
         Not that it particularly matters any more, since the
         resulting compressed stream is now the same regardless
         of whether or not we use the main sort or fallback sort.
      */
      if (wfact < 1  ) wfact = 1;
      if (wfact > 100) wfact = 100;
      budgetInit = nblock * ((wfact-1) / 3);

      budget = mainSort ( ptr, block, quadrant, ftab, nblock, verb, budgetInit );
      if (budget >= 0) {
         if (verb >= 3)
            VPrintf3 ( "      %d work, %d block, ratio %5.2f\n",
                       budgetInit - budget,
                       nblock,
                       (float)(budgetInit - budget) / (float)nblock );
      } else {
         if (verb >= 2) 
            VPrintf0 ( "    too repetitive; using fallback"
                       " sorting algorithm\n" );
         fallbackSort ( s->arr1, s->arr2, ftab, nblock, verb );
      }
   }

   s->origPtr = -1;
   for (i = 0; i < s->nblock; i++)
      if (ptr[i] == 0)
         { s->origPtr = i; break; };

   AssertH( s->origPtr != -1, 1003 );
}


/*-------------------------------------------------------------*/
/*--- end                                       blocksort.c ---*/
/*-------------------------------------------------------------*/
