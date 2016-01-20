
/*-------------------------------------------------------------*/
/*--- Compression machinery (not incl block sorting)        ---*/
/*---                                            compress.c ---*/
/*-------------------------------------------------------------*/

/* ------------------------------------------------------------------
   This file is part of bzip2/libbzip2, a program and library for
   lossless, block-sorting data compression.

   bzip2/libbzip2 version 1.0.6 of 6 September 2010
   Copyright (C) 1996-2010 Julian Seward <jseward@bzip.org>

   Please read the WARNING, DISCLAIMER and PATENTS sections in the 
   README file.

   This program is released under the terms of the license contained
   in the file LICENSE.
   ------------------------------------------------------------------ */


/* CHANGES
    0.9.0    -- original version.
    0.9.0a/b -- no changes in this file.
    0.9.0c   -- changed setting of nGroups in sendMTFValues() 
                so as to do a bit better on small files
*/

#include <stdlib.h>
#include "bzlib_private.h"


/*---------------------------------------------------*/
/*--- Bit stream I/O                              ---*/
/*---------------------------------------------------*/

/*---------------------------------------------------*/
void BZ2_bsInitWrite ( EState* s )
{
   s->bsLive = BITS_PER_LONG;
   s->bsBuff = 0;
}


/*---------------------------------------------------*/
static
void bsFinishWrite ( EState* s )
{
   while (s->bsLive < BITS_PER_LONG) {
      s->zbits[s->numZ] = (UChar)(s->bsBuff >> (BITS_PER_LONG - 8));
      s->numZ++;
      s->bsBuff <<= 8;
      s->bsLive += 8;
   }
}


/*---------------------------------------------------*/
static
__inline__
void bsW ( EState* s, Int32 n, ULong v )
{
   if (n < s->bsLive) {
      s->bsLive -= n;
      s->bsBuff |= (v << s->bsLive);
   } else {
      ULong tmp = s->bsBuff | (v >> (n - s->bsLive));
      ((una_ulong*)(s->zbits + s->numZ))->x = BZ_LITTLE_ENDIAN() ? bz_bswap_long(tmp) : tmp;
      s->numZ += sizeof(long);
      n = n - s->bsLive;
      s->bsLive = BITS_PER_LONG - n;
      if (n)
         s->bsBuff = (v << s->bsLive);
      else
         s->bsBuff = 0;
   }
}


/*---------------------------------------------------*/
static
__inline__
void bsW1 ( EState* s, ULong v )
{
   if (s->bsLive > 1) {
      s->bsLive--;
      s->bsBuff |= (v << s->bsLive);
   } else {
      ULong tmp = s->bsBuff | v;
      ((una_ulong*)(s->zbits + s->numZ))->x = BZ_LITTLE_ENDIAN() ? bz_bswap_long(tmp) : tmp;
      s->numZ += sizeof(long);
      s->bsLive = BITS_PER_LONG;
      s->bsBuff = 0;
   }
}


/*---------------------------------------------------*/
/*--- The back end proper                         ---*/
/*---------------------------------------------------*/

/*---------------------------------------------------*/
static
void makeMaps_e ( EState* s )
{
   Int32 i, j;

   s->nInUse = 0;
   for (i = 0; i < 16; i++) {
      Int16 inUse = s->inUse[i];
      for (j = i * 16; inUse; j++) {
         if (inUse < 0)
            s->unseqToSeq[j] = s->nInUse++;
         inUse <<= 1;
      }
   }
}

/*---------------------------------------------------*/
static
void BZ2_MtfEncodeInit( UChar *yy, Int32 nInUse )
{
   unsigned long curr;
   Int32 i;

   if (BZ_LITTLE_ENDIAN())
      curr = sizeof(long) == 8 ? 0x0706050403020100UL : 0x03020100UL;
   else
      curr = sizeof(long) == 8 ? 0x0001020304050607UL : 0x00010203UL;
   for (i = 0; i < nInUse; i += sizeof(long)) {
      *(unsigned long*)(yy + i) = curr;
      curr += sizeof(long) * (~0UL / 0xff);
   }
}

/*---------------------------------------------------*/
static inline
Int32 BZ2_MtfEncode( UChar *yy, UChar ll_i )
{
   const unsigned long one_bits = (~0UL / 0xff);
   const unsigned long low_bits = 0x7fUL * (~0UL / 0xff);
   register unsigned long pattern = ll_i * (~0UL / 0xff);
   unsigned long* pl = (unsigned long *)yy;
   register unsigned long prev = BZ_LITTLE_ENDIAN() ? ll_i : ((unsigned long)ll_i << (sizeof(long) * 8 - 8));
   register unsigned long curr, tmp;
   Int32 j;

   for (;;) {
      curr = *pl;
      tmp = curr ^ pattern;
      if ((tmp - one_bits) & ~(tmp | low_bits))
         break;
      if (BZ_LITTLE_ENDIAN()) {
         *pl++ = prev | (curr << 8);
         prev = (curr >> (sizeof(long) * 8 - 8));
      } else {
         *pl++ = prev | (curr >> 8);
         prev = (curr << (sizeof(long) * 8 - 8));
      }
   }

   j = (UChar*)pl - yy;
   tmp = ~((tmp & low_bits) + low_bits) & ~(tmp | low_bits);
   if (BZ_LITTLE_ENDIAN()) {
      tmp ^= (tmp - 1);
      j += sizeof(long) - __builtin_clzl(tmp) / 8;
      *pl = (curr & ~tmp) | (((curr << 8) | prev) & tmp);
   } else {
      j += (__builtin_clzl(tmp) + 8) / 8;
      tmp = ~0UL >> (__builtin_clzl(tmp) + 8);
      *pl = (curr & tmp) | (((curr >> 8) | prev) & ~tmp);
   }

   return j;
}


/*---------------------------------------------------*/
static
void generateMTFValues ( EState* s )
{
   LOCAL_DECALRE_ALIGNED_ARRAY(UChar, yy, 256, sizeof(long));
   Int32   i, j;
   UInt32  zPend;
   Int32   wr;
   Int32   EOB;

   /* 
      After sorting (eg, here),
         s->arr1 [ 0 .. s->nblock-1 ] holds sorted order,
         and
         ((UChar*)s->arr2) [ 0 .. s->nblock-1 ] 
         holds the original block data.

      The first thing to do is generate the MTF values,
      and put them in
         ((UInt16*)s->arr1) [ 0 .. s->nblock-1 ].
      Because there are strictly fewer or equal MTF values
      than block values, ptr values in this area are overwritten
      with MTF values only when they are no longer needed.

      The final compressed bitstream is generated into the
      area starting at
         (UChar*) (&((UChar*)s->arr2)[s->nblock])

      These storage aliases are set up in bzCompressInit(),
      except for the last one, which is arranged in 
      compressBlock().
   */
   UInt32* ptr   = s->ptr;
   UChar* block  = s->block;
   UInt16* mtfv  = s->mtfv;

   makeMaps_e ( s );
   EOB = s->nInUse+1;

   memset(s->mtfFreq, 0, sizeof(s->mtfFreq[0]) * (1 + EOB));
   BZ2_MtfEncodeInit(yy, s->nInUse);

   wr = 0;
   zPend = 0;
   for (i = 0; i < s->nblock; i++) {
      UChar ll_i;
      AssertD ( wr <= i, "generateMTFValues(1)" );
      j = ptr[i]-1; if (j < 0) j += s->nblock;
      ll_i = s->unseqToSeq[block[j]];
      AssertD ( ll_i < s->nInUse, "generateMTFValues(2a)" );

      if (yy[0] == ll_i) { 
         zPend++;
      } else {

         while (zPend > 0) {
               zPend--;
               if (zPend & 1) {
                  mtfv[wr] = BZ_RUNB; wr++; 
                  s->mtfFreq[BZ_RUNB]++; 
               } else {
                  mtfv[wr] = BZ_RUNA; wr++; 
                  s->mtfFreq[BZ_RUNA]++; 
               }
               zPend >>= 1;
         }

         j = BZ2_MtfEncode(yy, ll_i);
         mtfv[wr] = j; wr++; s->mtfFreq[j]++;
      }
   }

   while (zPend > 0) {
         zPend--;
         if (zPend & 1) {
            mtfv[wr] = BZ_RUNB; wr++; 
            s->mtfFreq[BZ_RUNB]++; 
         } else {
            mtfv[wr] = BZ_RUNA; wr++; 
            s->mtfFreq[BZ_RUNA]++; 
         }
         zPend >>= 1;
   }

   mtfv[wr] = EOB; wr++; s->mtfFreq[EOB]++;

   s->nMTF = wr;
}


/*---------------------------------------------------*/
#define BZ_LESSER_ICOST  0
#define BZ_GREATER_ICOST 15

static
void sendMTFValues ( EState* s )
{
   Int32 v, t, i, j, gs, ge, iter;
   Int32 nSelectors, alphaSize, minLen, maxLen, selCtr;
   Int32 nGroups, nBytes;

   /*--
   UChar  len [BZ_N_GROUPS][BZ_MAX_ALPHA_SIZE];
   is a global since the decoder also needs it.

   Int32  code[BZ_N_GROUPS][BZ_MAX_ALPHA_SIZE];
   Int32  rfreq[BZ_N_GROUPS][BZ_MAX_ALPHA_SIZE];
   are also globals only used in this proc.
   Made global to keep stack frame size small.
   --*/

   UInt16* mtfv = s->mtfv;

   if (s->verbosity >= 3)
      VPrintf3( "      %d in block, %d after MTF & 1-2 coding, "
                "%d+2 syms in use\n", 
                s->nblock, s->nMTF, s->nInUse );

   alphaSize = s->nInUse+2;
   for (t = 0; t < BZ_N_GROUPS; t++)
      memset(s->len[t], BZ_GREATER_ICOST, alphaSize);

   /*--- Decide how many coding tables to use ---*/
   AssertH ( s->nMTF > 0, 3001 );
   if (s->nMTF < 200)  nGroups = 2; else
   if (s->nMTF < 600)  nGroups = 3; else
   if (s->nMTF < 1200) nGroups = 4; else
   if (s->nMTF < 2400) nGroups = 5; else
                       nGroups = 6;

   /*--- Generate an initial set of coding tables ---*/
   { 
      Int32 nPart, remF, tFreq, aFreq;

      remF  = s->nMTF;
      gs = 0;
      for (nPart = nGroups; nPart > 0; nPart--) {
         tFreq = remF / nPart;
         ge = gs-1;
         aFreq = 0;
         do {
            ge++;
            aFreq += s->mtfFreq[ge];
         } while (aFreq < tFreq && ge < alphaSize-1);

         if (ge > gs 
             && nPart != nGroups && nPart != 1 
             && ((nGroups - nPart) & 1)) {
            aFreq -= s->mtfFreq[ge];
            ge--;
         }

         if (s->verbosity >= 3)
            VPrintf5( "      initial group %d, [%d .. %d], "
                      "has %d syms (%4.1f%%)\n",
                      nPart, gs, ge, aFreq, 
                      (100.0 * (float)aFreq) / (float)(s->nMTF) );

         memset(s->len[nPart-1], BZ_GREATER_ICOST, alphaSize);
         memset(&s->len[nPart-1][gs], BZ_LESSER_ICOST, ge + 1 - gs);

         gs = ge+1;
         remF -= aFreq;
      }
   }

   /*--- 
      Iterate up to BZ_N_ITERS times to improve the tables.
   ---*/
   for (iter = 0; iter < BZ_N_ITERS; iter++) {
      UInt16 cost[BZ_N_GROUPS];
      Int32  fave[BZ_N_GROUPS] = { 0 };
      Int32 totc = 0, bt, bc;

      for (t = 0; t < nGroups; t++) {
         memset(s->rfreq[t], 0, sizeof(s->rfreq[t][0]) * alphaSize);
#if ULONG_MAX == 4294967295UL
         if (t & 1) {
            for (v = 0; v < alphaSize; v++)
               s->len_pack[v][t / 2] = ((ULong)s->len[t][v] << 16) | s->len[t - 1][v];
         }
      }
#else
         if (t == 3) {
            for (v = 0; v < alphaSize; v++)
               s->len_pack[v][0] = ((ULong)s->len[3][v] << 48) | ((ULong)s->len[2][v] << 32) | ((ULong)s->len[1][v] << 16) | s->len[0][v];
         }
      }
      if ((t & 3) >= 2) {
         for (v = 0; v < alphaSize; v++) {
            ULong tmp = ((ULong)s->len[t - 1][v] << 16) | s->len[t - 2][v];
            if ((t & 3) == 3)
               tmp = (tmp << 16) | s->len[t - 3][v];
            s->len_pack[v][t / 4] = tmp;
         }
      }
#endif

      nSelectors = 0;
      for (gs = 0; gs < s->nMTF; gs = ge + 1) {
#if ULONG_MAX == 4294967295UL
         register unsigned long cost01, cost23, cost45;
#else
         register unsigned long cost0123, cost45;
#endif
         register UInt16 icv;

         /*--- Set group start & end marks. --*/
         ge = gs + BZ_G_SIZE - 1; 
         if (ge >= s->nMTF) ge = s->nMTF-1;

#define BZ_ITER_GROUP() \
            switch (ge - gs)  { \
            BZ_ITER(0);  BZ_ITER(1);  BZ_ITER(2);  BZ_ITER(3);  BZ_ITER(4); \
            BZ_ITER(5);  BZ_ITER(6);  BZ_ITER(7);  BZ_ITER(8);  BZ_ITER(9); \
            BZ_ITER(10); BZ_ITER(11); BZ_ITER(12); BZ_ITER(13); BZ_ITER(14); \
            BZ_ITER(15); BZ_ITER(16); BZ_ITER(17); BZ_ITER(18); BZ_ITER(19); \
            BZ_ITER(20); BZ_ITER(21); BZ_ITER(22); BZ_ITER(23); BZ_ITER(24); \
            BZ_ITER(25); BZ_ITER(26); BZ_ITER(27); BZ_ITER(28); BZ_ITER(29); \
            BZ_ITER(30); BZ_ITER(31); BZ_ITER(32); BZ_ITER(33); BZ_ITER(34); \
            BZ_ITER(35); BZ_ITER(36); BZ_ITER(37); BZ_ITER(38); BZ_ITER(39); \
            BZ_ITER(40); BZ_ITER(41); BZ_ITER(42); BZ_ITER(43); BZ_ITER(44); \
            BZ_ITER(45); BZ_ITER(46); BZ_ITER(47); BZ_ITER(48); BZ_ITER(49); \
            }

         /*-- 
            Calculate the cost of this group as coded
            by each of the coding tables.
         --*/
         switch (nGroups) {

#if ULONG_MAX == 4294967295UL

#define BZ_ITER(nn)                           \
            case 49 - (nn):                   \
               icv = mtfv[ge - (49 - (nn))];  \
               cost01 += s->len_pack[icv][0];

         case 2:
            cost01 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost01 & 0xffff;
            cost[1] = cost01 >> 16;
            break;

#undef BZ_ITER

#define BZ_ITER(nn)                           \
            case 49 - (nn):                   \
               icv = mtfv[ge - (49 - (nn))];  \
               cost01 += s->len_pack[icv][0]; \
               cost23 += s->len[2][icv];

         case 3:
            cost01 = 0;
            cost23 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost01 & 0xffff;
            cost[1] = cost01 >> 16;
            cost[2] = cost23;
            break;

#undef BZ_ITER

#define BZ_ITER(nn)                           \
            case 49 - (nn):                   \
               icv = mtfv[ge - (49 - (nn))];  \
               cost01 += s->len_pack[icv][0]; \
               cost23 += s->len_pack[icv][1];

         case 4:
            cost01 = cost23 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost01 & 0xffff;
            cost[1] = cost01 >> 16;
            cost[2] = cost23 & 0xffff;
            cost[3] = cost23 >> 16;
            break;

#undef BZ_ITER

#define BZ_ITER(nn)                           \
            case 49 - (nn):                   \
               icv = mtfv[ge - (49 - (nn))];  \
               cost01 += s->len_pack[icv][0]; \
               cost23 += s->len_pack[icv][1]; \
               cost45 += s->len[4][icv];

         case 5:
            cost01 = cost23 = cost45 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost01 & 0xffff;
            cost[1] = cost01 >> 16;
            cost[2] = cost23 & 0xffff;
            cost[3] = cost23 >> 16;
            cost[4] = cost45;
            break;

#undef BZ_ITER

#define BZ_ITER(nn)                           \
            case 49 - (nn):                   \
               icv = mtfv[ge - (49 - (nn))];  \
               cost01 += s->len_pack[icv][0]; \
               cost23 += s->len_pack[icv][1]; \
               cost45 += s->len_pack[icv][2];

         case 6:
            cost01 = cost23 = cost45 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost01 & 0xffff;
            cost[1] = cost01 >> 16;
            cost[2] = cost23 & 0xffff;
            cost[3] = cost23 >> 16;
            cost[4] = cost45 & 0xffff;
            cost[5] = cost45 >> 16;
            break;

#undef BZ_ITER

#else

#define BZ_ITER(nn)                            \
            case 49 - (nn):                    \
               icv = mtfv[ge - (49 - (nn))];   \
               cost0123 += s->len_pack[icv][0];

         case 2:
            cost0123 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost0123 & 0xffff;
            cost[1] = cost0123 >> 16;
            break;

#undef BZ_ITER

#define BZ_ITER(nn)                            \
            case 49 - (nn):                    \
               icv = mtfv[ge - (49 - (nn))];   \
               cost0123 += s->len_pack[icv][0];

         case 3:
            cost0123 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost0123 & 0xffff;
            cost[1] = (cost0123 >> 16) & 0xffff;
            cost[2] = cost0123 >> 32;
            break;

#undef BZ_ITER

#define BZ_ITER(nn)                            \
            case 49 - (nn):                    \
               icv = mtfv[ge - (49 - (nn))];   \
               cost0123 += s->len_pack[icv][0];

         case 4:
            cost0123 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost0123 & 0xffff;
            cost[1] = (cost0123 >> 16) & 0xffff;
            cost[2] = (cost0123 >> 32) & 0xffff;
            cost[3] = cost0123 >> 48;
            break;

#undef BZ_ITER

#define BZ_ITER(nn)                             \
            case 49 - (nn):                     \
               icv = mtfv[ge - (49 - (nn))];    \
               cost0123 += s->len_pack[icv][0]; \
               cost45   += s->len[4][icv];

         case 5:
            cost0123 = cost45 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost0123 & 0xffff;
            cost[1] = (cost0123 >> 16) & 0xffff;
            cost[2] = (cost0123 >> 32) & 0xffff;
            cost[3] = cost0123 >> 48;
            cost[4] = cost45;
            break;

#undef BZ_ITER

#define BZ_ITER(nn)                             \
            case 49 - (nn):                     \
               icv = mtfv[ge - (49 - (nn))];    \
               cost0123 += s->len_pack[icv][0]; \
               cost45   += s->len_pack[icv][1];

         case 6:
            cost0123 = cost45 = 0;
            BZ_ITER_GROUP()
            cost[0] = cost0123 & 0xffff;
            cost[1] = (cost0123 >> 16) & 0xffff;
            cost[2] = (cost0123 >> 32) & 0xffff;
            cost[3] = cost0123 >> 48;
            cost[4] = cost45 & 0xffff;
            cost[5] = cost45 >> 16;
            break;

#undef BZ_ITER

#endif
         }

#undef BZ_ITER_GROUP

         /*-- 
            Find the coding table which is best for this group,
            and record its identity in the selector table.
         --*/
         bc = 999999999; bt = -1;
         for (t = 0; t < nGroups; t++)
            if (cost[t] < bc) { bc = cost[t]; bt = t; };
         totc += bc;
         fave[bt]++;
         s->selector[nSelectors] = bt;
         nSelectors++;

         /*-- 
            Increment the symbol frequencies for the selected table.
          --*/
#define BZ_ITUR(nn) \
            case 49 - (nn): \
               s->rfreq[bt][ mtfv[ge - (49 - (nn))] ]++

            switch (ge - gs)  {
            BZ_ITUR(0);  BZ_ITUR(1);  BZ_ITUR(2);  BZ_ITUR(3);  BZ_ITUR(4);
            BZ_ITUR(5);  BZ_ITUR(6);  BZ_ITUR(7);  BZ_ITUR(8);  BZ_ITUR(9);
            BZ_ITUR(10); BZ_ITUR(11); BZ_ITUR(12); BZ_ITUR(13); BZ_ITUR(14);
            BZ_ITUR(15); BZ_ITUR(16); BZ_ITUR(17); BZ_ITUR(18); BZ_ITUR(19);
            BZ_ITUR(20); BZ_ITUR(21); BZ_ITUR(22); BZ_ITUR(23); BZ_ITUR(24);
            BZ_ITUR(25); BZ_ITUR(26); BZ_ITUR(27); BZ_ITUR(28); BZ_ITUR(29);
            BZ_ITUR(30); BZ_ITUR(31); BZ_ITUR(32); BZ_ITUR(33); BZ_ITUR(34);
            BZ_ITUR(35); BZ_ITUR(36); BZ_ITUR(37); BZ_ITUR(38); BZ_ITUR(39);
            BZ_ITUR(40); BZ_ITUR(41); BZ_ITUR(42); BZ_ITUR(43); BZ_ITUR(44);
            BZ_ITUR(45); BZ_ITUR(46); BZ_ITUR(47); BZ_ITUR(48); BZ_ITUR(49);
            }

#undef BZ_ITUR
      }
      if (s->verbosity >= 3) {
         VPrintf2 ( "      pass %d: size is %d, grp uses are ", 
                   iter+1, totc/8 );
         for (t = 0; t < nGroups; t++)
            VPrintf1 ( "%d ", fave[t] );
         VPrintf0 ( "\n" );
      }

      /*--
        Recompute the tables based on the accumulated frequencies.
      --*/
      /* maxLen was changed from 20 to 17 in bzip2-1.0.3.  See 
         comment in huffman.c for details. */
      for (t = 0; t < nGroups; t++)
         BZ2_hbMakeCodeLengths ( &(s->len[t][0]), &(s->rfreq[t][0]), 
                                 alphaSize, 17 /*20*/ );
   }


   AssertH( nGroups < 8, 3002 );
   AssertH( nSelectors < 32768 &&
            nSelectors <= (2 + (900000 / BZ_G_SIZE)),
            3003 );


   /*--- Compute MTF values for the selectors. ---*/
   {
      UChar pos[BZ_N_GROUPS], ll_i, tmp2, tmp;
      for (i = 0; i < nGroups; i++) pos[i] = i;
      for (i = 0; i < nSelectors; i++) {
         ll_i = s->selector[i];
         j = 0;
         tmp = pos[j];
         while ( ll_i != tmp ) {
            j++;
            tmp2 = tmp;
            tmp = pos[j];
            pos[j] = tmp2;
         };
         pos[0] = tmp;
         s->selectorMtf[i] = j;
      }
   };

   /*--- Assign actual codes for the tables. --*/
   for (t = 0; t < nGroups; t++) {
      minLen = 32;
      maxLen = 0;
      for (i = 0; i < alphaSize; i++) {
         if (s->len[t][i] > maxLen) maxLen = s->len[t][i];
         if (s->len[t][i] < minLen) minLen = s->len[t][i];
      }
      AssertH ( !(maxLen > 17 /*20*/ ), 3004 );
      AssertH ( !(minLen < 1),  3005 );
      BZ2_hbAssignCodes ( &(s->code[t][0]), &(s->len[t][0]), 
                          minLen, maxLen, alphaSize );
   }

   /*--- Transmit the mapping table. ---*/
   {
      UInt16 inUse16 = 0;
      nBytes = s->numZ;
      for (i = 0; i < 16; i++)
         if (s->inUse[i])
             inUse16 |= 0x8000U >> i;
      bsW(s,16,inUse16);

      for (i = 0; i < 16; i++)
         if (s->inUse[i])
            bsW(s,16,s->inUse[i]);

      if (s->verbosity >= 3) 
         VPrintf1( "      bytes: mapping %d, ", s->numZ-nBytes );
   }

   /*--- Now the selectors. ---*/
   nBytes = s->numZ;
   bsW ( s, 3, nGroups );
   bsW ( s, 15, nSelectors );
   for (i = 0; i < nSelectors; i++) {
      bsW(s, 1 + s->selectorMtf[i], (1U << (1 + s->selectorMtf[i])) - 2);
   }
   if (s->verbosity >= 3)
      VPrintf1( "selectors %d, ", s->numZ-nBytes );

   /*--- Now the coding tables. ---*/
   nBytes = s->numZ;

   for (t = 0; t < nGroups; t++) {
      Int32 curr = s->len[t][0];
      bsW ( s, 6, curr << 1 );
      for (i = 1; i < alphaSize; i++) {
         j = s->len[t][i] - curr;
         curr = s->len[t][i];
         if (j > 0) {
            if (j > 12) {
               bsW(s,24,0xaaaaaa);
               j -= 12;
            }
            j *= 2;
            bsW(s,j,0xaaaaaa & ((1 << j) - 1));
         }
         else if (j < 0) {
            if (j < -12) {
               bsW(s,24,0xffffff);
               j += 12;
            }
            j *= -2;
            bsW(s,j,((1 << j) - 1));
         }
         bsW1 ( s, 0 );
      }
   }

   if (s->verbosity >= 3)
      VPrintf1 ( "code lengths %d, ", s->numZ-nBytes );

   /*--- And finally, the block data proper ---*/
   nBytes = s->numZ;
   selCtr = 0;
   for (gs = 0; gs < s->nMTF; gs = ge+1) {
      ge = gs + BZ_G_SIZE - 1; 
      if (ge >= s->nMTF) ge = s->nMTF-1;
      AssertH ( s->selector[selCtr] < nGroups, 3006 );

      {
            UChar* s_len_sel_selCtr 
               = &(s->len[s->selector[selCtr]][0]);
            Int32* s_code_sel_selCtr
               = &(s->code[s->selector[selCtr]][0]);
            UInt16 icv;

#define BZ_ITAH(nn)                              \
         case 49 - (nn):                         \
            icv = mtfv[ge - (49 - (nn))];        \
            bsW ( s, s_len_sel_selCtr[icv], s_code_sel_selCtr[icv] )

         switch (ge - gs)  {
            BZ_ITAH(0);  BZ_ITAH(1);  BZ_ITAH(2);  BZ_ITAH(3);  BZ_ITAH(4);
            BZ_ITAH(5);  BZ_ITAH(6);  BZ_ITAH(7);  BZ_ITAH(8);  BZ_ITAH(9);
            BZ_ITAH(10); BZ_ITAH(11); BZ_ITAH(12); BZ_ITAH(13); BZ_ITAH(14);
            BZ_ITAH(15); BZ_ITAH(16); BZ_ITAH(17); BZ_ITAH(18); BZ_ITAH(19);
            BZ_ITAH(20); BZ_ITAH(21); BZ_ITAH(22); BZ_ITAH(23); BZ_ITAH(24);
            BZ_ITAH(25); BZ_ITAH(26); BZ_ITAH(27); BZ_ITAH(28); BZ_ITAH(29);
            BZ_ITAH(30); BZ_ITAH(31); BZ_ITAH(32); BZ_ITAH(33); BZ_ITAH(34);
            BZ_ITAH(35); BZ_ITAH(36); BZ_ITAH(37); BZ_ITAH(38); BZ_ITAH(39);
            BZ_ITAH(40); BZ_ITAH(41); BZ_ITAH(42); BZ_ITAH(43); BZ_ITAH(44);
            BZ_ITAH(45); BZ_ITAH(46); BZ_ITAH(47); BZ_ITAH(48); BZ_ITAH(49);
          }

#undef BZ_ITAH
      }

      selCtr++;
   }
   AssertH( selCtr == nSelectors, 3007 );

   if (s->verbosity >= 3)
      VPrintf1( "codes %d\n", s->numZ-nBytes );
}


/*---------------------------------------------------*/
void BZ2_compressBlock ( EState* s, Bool is_last_block )
{
   if (s->nblock > 0) {

      BZ_FINALISE_CRC ( s->blockCRC );
      s->combinedCRC = (s->combinedCRC << 1) | (s->combinedCRC >> 31);
      s->combinedCRC ^= s->blockCRC;
      if (s->blockNo > 1) s->numZ = 0;

      if (s->verbosity >= 2)
         VPrintf4( "    block %d: crc = 0x%08x, "
                   "combined CRC = 0x%08x, size = %d\n",
                   s->blockNo, s->blockCRC, s->combinedCRC, s->nblock );

      BZ2_blockSort ( s );
   }

   s->zbits = (UChar*) (&((UChar*)s->arr2)[s->nblock]);

   /*-- If this is the first block, create the stream header. --*/
   if (s->blockNo == 1) {
      BZ2_bsInitWrite ( s );
      bsW ( s, 32, BZ_HDR + s->blockSize100k );
   }

   if (s->nblock > 0) {

      bsW ( s, 32, 0x31415926 );
      bsW ( s, 16, 0x5359 );

      /*-- Now the block's CRC, so it is in a known place. --*/
      bsW ( s, 32, s->blockCRC );

      /*-- 
         Now a single bit indicating (non-)randomisation. 
         As of version 0.9.5, we use a better sorting algorithm
         which makes randomisation unnecessary.  So always set
         the randomised bit to 'no'.  Of course, the decoder
         still needs to be able to handle randomised blocks
         so as to maintain backwards compatibility with
         older versions of bzip2.
      --*/
      bsW1(s,0);

      bsW ( s, 24, s->origPtr );
      generateMTFValues ( s );
      sendMTFValues ( s );
   }


   /*-- If this is the last block, add the stream trailer. --*/
   if (is_last_block) {

      bsW ( s, 32, 0x17724538 );
      bsW ( s, 16, 0x5090 );
      bsW ( s, 32, s->combinedCRC );
      if (s->verbosity >= 2)
         VPrintf1( "    final combined CRC = 0x%08x\n   ", s->combinedCRC );
      bsFinishWrite ( s );
   }
}


/*-------------------------------------------------------------*/
/*--- end                                        compress.c ---*/
/*-------------------------------------------------------------*/
