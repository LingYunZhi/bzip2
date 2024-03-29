
/*-------------------------------------------------------------*/
/*--- Decompression machinery                               ---*/
/*---                                          decompress.c ---*/
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

static
void BZ2_MtfDecodeInit( DState* s )
{
   Int32 i;

   BZ2_IndexTableInit(&s->mtfa[MTFA_SIZE - 256], 256);

   for (i = 0; i < 256 / MTFL_SIZE; i++)
      s->mtfbase[i] = MTFA_SIZE - 256 + i * MTFL_SIZE;
}

static inline
UChar BZ2_MtfDecode( DState* s, Int32 nn )
{
    UChar uc;
    UChar *mtfa;

    if (nn < MTFL_SIZE) {
        /* avoid general-case expense */
        mtfa = &s->mtfa[s->mtfbase[0]];
        uc = mtfa[nn];
        while (nn-- > 0)
            mtfa[nn + 1] = mtfa[nn];
        mtfa[0] = uc;
    } else {
        Int32 lno, off;

        lno = nn / MTFL_SIZE;
        off = nn % MTFL_SIZE;

        if (s->mtfbase[0] > 0) {
            /* general case */
            Int32 pp = s->mtfbase[lno];
            mtfa = &s->mtfa[pp];
            uc = mtfa[off];
            while (off-- > 0)
                mtfa[off + 1] = mtfa[off];
            while (lno-- > 0) {
                Int32 tmp = s->mtfbase[lno] - 1;
                s->mtfa[pp] = s->mtfa[tmp + MTFL_SIZE];
                s->mtfbase[lno] = pp = tmp;
            }
            s->mtfa[pp] = uc;
        } else {
            unsigned long *mtfa;
            ua_ulong *src_mtfa;
            Int32 ii, jj;
            unsigned long luc;
            unsigned long val, tmp;

            mtfa = s->mtfa + MTFA_SIZE - sizeof(long);
            for (ii = 256 / MTFL_SIZE - 1; ii > lno; ii--) {
                src_mtfa = (ua_ulong *)(s->mtfa + s->mtfbase[ii] + MTFL_SIZE - sizeof(long));
                for (jj = MTFL_SIZE / sizeof(long) - 1; jj >= 0; jj--)
                    *mtfa-- = (src_mtfa--)->x;
                s->mtfbase[ii] = MTFA_SIZE - 256 + ii * MTFL_SIZE;
            }

            src_mtfa = (ua_ulong *)(s->mtfa + s->mtfbase[ii] + MTFL_SIZE - sizeof(long));
            for (jj = MTFL_SIZE / sizeof(long) - 1; jj > off / sizeof(long); jj--)
                *mtfa-- = (src_mtfa--)->x;
            val = (src_mtfa--)->x;
            off = (off % sizeof(long)) * 8;
            if (BZ_LITTLE_ENDIAN()) {
                luc = (val >> off) & 0xff;
                uc = luc;
                val = ((val & ((1UL << off) - 1)) << 8) |
                      (val & (~0xffUL << off));
            } else {
                luc = (val << off) & (0xffUL << (sizeof(long) * 8 - 8));
                uc = luc >> (sizeof(long) * 8 - 8);
                val = ((val & ~(~0UL >> off)) >> 8) |
                      (val & ((1UL << (sizeof(long) * 8 - 8 - off)) - 1));
            }
            while (--jj >= 0) {
                tmp = (src_mtfa--)->x;
                if (BZ_LITTLE_ENDIAN()) {
                    *mtfa-- = val | (tmp >> (sizeof(long) * 8 - 8));
                    val = tmp << 8;
                } else {
                    *mtfa-- = val | (tmp << (sizeof(long) * 8 - 8));
                    val = tmp >> 8;
                }
            }
            s->mtfbase[ii] = MTFA_SIZE - 256 + ii * MTFL_SIZE;

            while (--ii >= 0) {
                src_mtfa = (ua_ulong *)(s->mtfa + s->mtfbase[ii] + MTFL_SIZE - sizeof(long));
                for (jj = MTFL_SIZE / sizeof(long) - 1; jj >= 0; jj--) {
                    tmp = (src_mtfa--)->x;
                    if (BZ_LITTLE_ENDIAN()) {
                        *mtfa-- = val | (tmp >> (sizeof(long) * 8 - 8));
                        val = tmp << 8;
                    } else {
                        *mtfa-- = val | (tmp << (sizeof(long) * 8 - 8));
                        val = tmp >> 8;
                    }
                }
                s->mtfbase[ii] = MTFA_SIZE - 256 + ii * MTFL_SIZE;
            }
            *mtfa = val | luc;
        }
    }

    return uc;
}


/*---------------------------------------------------*/
#define RETURN(rrr)                               \
   { retVal = rrr; goto save_state_and_return; };

#define NEED_BITS(lll,nnn)                        \
   case lll: s->state = lll;                      \
   if (__builtin_constant_p(nnn) && nnn <= 8) {   \
     if (bsLive > 32 - nnn) {                     \
        if (inPtr == inEnd) RETURN(BZ_OK);        \
        bsLive -= 8;                              \
        bsBuff |= ((UInt32)(*inPtr)) << bsLive;   \
        inPtr++;                                  \
     }                                            \
   } else {                                       \
     while (bsLive > 32 - nnn) {                  \
        if (inPtr == inEnd) RETURN(BZ_OK);        \
        bsLive -= 8;                              \
        bsBuff |= ((UInt32)(*inPtr)) << bsLive;   \
        inPtr++;                                  \
     }                                            \
   }

#define DROP_BITS(nnn)                            \
   bsBuff <<= nnn;                                \
   bsLive += nnn;

#define GET_BITS(lll,vvv,nnn)                     \
   NEED_BITS(lll,nnn);                            \
   vvv = bsBuff >> (32 - nnn);                    \
   DROP_BITS(nnn)

#define GET_UCHAR(lll,uuu)                        \
   GET_BITS(lll,uuu,8)

#define GET_BIT(lll,uuu)                          \
   GET_BITS(lll,uuu,1)

/*---------------------------------------------------*/
#define GET_MTF_VAL(label1,label2,lval)           \
{                                                 \
   if (groupPos == 0) {                           \
      groupNo++;                                  \
      if (groupNo >= nSelectors)                  \
         RETURN(BZ_DATA_ERROR);                   \
      groupPos = BZ_G_SIZE;                       \
      gSel = s->selector[groupNo];                \
      gMinlen = s->minLens[gSel];                 \
      gLimit = &(s->limit[gSel][0]);              \
      gPerm = &(s->perm[gSel][0]);                \
      gBase = &(s->base[gSel][0]);                \
   }                                              \
   groupPos--;                                    \
   zn = gMinlen;                                  \
   GET_BITS(label1, zvec, zn);                    \
   while (1) {                                    \
      if (zn > 20 /* the longest code */)         \
         RETURN(BZ_DATA_ERROR);                   \
      if (zvec <= gLimit[zn]) break;              \
      zn++;                                       \
      GET_BIT(label2, zj);                        \
      zvec = (zvec << 1) | zj;                    \
   };                                             \
   if (zvec - gBase[zn] < 0                       \
       || zvec - gBase[zn] >= BZ_MAX_ALPHA_SIZE)  \
      RETURN(BZ_DATA_ERROR);                      \
   lval = gPerm[zvec - gBase[zn]];                \
}


/*---------------------------------------------------*/
Int32 BZ2_decompress ( DState* s )
{
   UChar      uc;
   Int32      retVal;
   Int32      minLen, maxLen;
   bz_stream* strm = s->strm;

   /* stuff that needs to be saved/restored */
   Int32  i;
   Int32  j;
   Int32  t;
   Int32  alphaSize;
   Int32  nGroups;
   Int32  nSelectors;
   Int32  EOB;
   Int32  groupNo;
   Int32  groupPos;
   Int32  nextSym;
   Int32  nblockMAX;
   Int32  nblock;
   Int32  es;
   Int32  N;
   Int32  curr;
   Int32  zt;
   Int32  zn; 
   Int32  zvec;
   Int32  zj;
   Int32  gSel;
   Int32  gMinlen;
   Int32* gLimit;
   Int32* gBase;
   Int32* gPerm;
   Int32 prev;
   UInt32 bsBuff = s->bsBuff;
   Int32 bsLive = s->bsLive;
   UChar *inPtr = (UChar*)s->strm->next_in;
   UChar *inEnd = (UChar*)s->strm->next_in + s->strm->avail_in;
   UInt32 consumed;

   if (s->state == BZ_X_MAGIC_1) {
      /*initialise the save area*/
      s->save_i           = 0;
      s->save_j           = 0;
      s->save_t           = 0;
      s->save_alphaSize   = 0;
      s->save_nGroups     = 0;
      s->save_nSelectors  = 0;
      s->save_EOB         = 0;
      s->save_groupNo     = 0;
      s->save_groupPos    = 0;
      s->save_nextSym     = 0;
      s->save_nblockMAX   = 0;
      s->save_nblock      = 0;
      s->save_es          = 0;
      s->save_N           = 0;
      s->save_curr        = 0;
      s->save_zt          = 0;
      s->save_zn          = 0;
      s->save_zvec        = 0;
      s->save_zj          = 0;
      s->save_gSel        = 0;
      s->save_gMinlen     = 0;
      s->save_gLimit      = NULL;
      s->save_gBase       = NULL;
      s->save_gPerm       = NULL;
   }

   /*restore from the save area*/
   i           = s->save_i;
   j           = s->save_j;
   t           = s->save_t;
   alphaSize   = s->save_alphaSize;
   nGroups     = s->save_nGroups;
   nSelectors  = s->save_nSelectors;
   EOB         = s->save_EOB;
   groupNo     = s->save_groupNo;
   groupPos    = s->save_groupPos;
   nextSym     = s->save_nextSym;
   nblockMAX   = s->save_nblockMAX;
   nblock      = s->save_nblock;
   es          = s->save_es;
   N           = s->save_N;
   curr        = s->save_curr;
   zt          = s->save_zt;
   zn          = s->save_zn; 
   zvec        = s->save_zvec;
   zj          = s->save_zj;
   gSel        = s->save_gSel;
   gMinlen     = s->save_gMinlen;
   gLimit      = s->save_gLimit;
   gBase       = s->save_gBase;
   gPerm       = s->save_gPerm;

   retVal = BZ_OK;

   switch (s->state) {

      GET_UCHAR(BZ_X_MAGIC_1, uc);
      if (uc != BZ_HDR_B) RETURN(BZ_DATA_ERROR_MAGIC);

      GET_UCHAR(BZ_X_MAGIC_2, uc);
      if (uc != BZ_HDR_Z) RETURN(BZ_DATA_ERROR_MAGIC);

      GET_UCHAR(BZ_X_MAGIC_3, uc)
      if (uc != BZ_HDR_h) RETURN(BZ_DATA_ERROR_MAGIC);

      GET_BITS(BZ_X_MAGIC_4, s->blockSize100k, 8)
      if (s->blockSize100k < (BZ_HDR_0 + 1) || 
          s->blockSize100k > (BZ_HDR_0 + 9)) RETURN(BZ_DATA_ERROR_MAGIC);
      s->blockSize100k -= BZ_HDR_0;

      if (s->smallDecompress) {
         s->ll16 = BZALLOC( s->blockSize100k * 100000 * sizeof(UInt16) );
         s->ll4  = BZALLOC( 
                      ((1 + s->blockSize100k * 100000) >> 1) * sizeof(UChar) 
                   );
         if (s->ll16 == NULL || s->ll4 == NULL) RETURN(BZ_MEM_ERROR);
      } else {
         s->tt  = BZALLOC( s->blockSize100k * 100000 * sizeof(Int32) );
         if (s->tt == NULL) RETURN(BZ_MEM_ERROR);
      }

      GET_UCHAR(BZ_X_BLKHDR_1, uc);

      if (uc == 0x17) goto endhdr_2;
      if (uc != 0x31) RETURN(BZ_DATA_ERROR);
      GET_UCHAR(BZ_X_BLKHDR_2, uc);
      if (uc != 0x41) RETURN(BZ_DATA_ERROR);
      GET_UCHAR(BZ_X_BLKHDR_3, uc);
      if (uc != 0x59) RETURN(BZ_DATA_ERROR);
      GET_UCHAR(BZ_X_BLKHDR_4, uc);
      if (uc != 0x26) RETURN(BZ_DATA_ERROR);
      GET_UCHAR(BZ_X_BLKHDR_5, uc);
      if (uc != 0x53) RETURN(BZ_DATA_ERROR);
      GET_UCHAR(BZ_X_BLKHDR_6, uc);
      if (uc != 0x59) RETURN(BZ_DATA_ERROR);

      s->currBlockNo++;
      if (s->verbosity >= 2)
         VPrintf1 ( "\n    [%d: huff+mtf ", s->currBlockNo );
 
      s->storedBlockCRC = 0;
      GET_UCHAR(BZ_X_BCRC_1, uc);
      s->storedBlockCRC = (s->storedBlockCRC << 8) | ((UInt32)uc);
      GET_UCHAR(BZ_X_BCRC_2, uc);
      s->storedBlockCRC = (s->storedBlockCRC << 8) | ((UInt32)uc);
      GET_UCHAR(BZ_X_BCRC_3, uc);
      s->storedBlockCRC = (s->storedBlockCRC << 8) | ((UInt32)uc);
      GET_UCHAR(BZ_X_BCRC_4, uc);
      s->storedBlockCRC = (s->storedBlockCRC << 8) | ((UInt32)uc);

      GET_BITS(BZ_X_RANDBIT, s->blockRandomised, 1);

      s->origPtr = 0;
      GET_UCHAR(BZ_X_ORIGPTR_1, uc);
      s->origPtr = (s->origPtr << 8) | ((Int32)uc);
      GET_UCHAR(BZ_X_ORIGPTR_2, uc);
      s->origPtr = (s->origPtr << 8) | ((Int32)uc);
      GET_UCHAR(BZ_X_ORIGPTR_3, uc);
      s->origPtr = (s->origPtr << 8) | ((Int32)uc);

      if (s->origPtr < 0)
         RETURN(BZ_DATA_ERROR);
      if (s->origPtr > 10 + 100000*s->blockSize100k) 
         RETURN(BZ_DATA_ERROR);

      /*--- Receive the mapping table ---*/
      GET_BITS(BZ_X_MAPPING_1, s->inUse16, 16);

      s->nInUse = 0;
      for (i = 0; s->inUse16; i++) {
         if (s->inUse16 < 0) {
            Int16 inUse;
            GET_BITS(BZ_X_MAPPING_2, inUse, 16);
            for (j = i * 16; inUse; j++) {
               if (inUse < 0)
                  s->seqToUnseq[s->nInUse++] = j;
               inUse <<= 1;
            }
         }
         s->inUse16 <<= 1;
      }
      if (s->nInUse == 0) RETURN(BZ_DATA_ERROR);
      alphaSize = s->nInUse+2;

      /*--- Now the selectors ---*/
      GET_BITS(BZ_X_SELECTOR_1, nGroups, 3);
      if (nGroups < 2 || nGroups > BZ_N_GROUPS) RETURN(BZ_DATA_ERROR);
      GET_BITS(BZ_X_SELECTOR_2, nSelectors, 15);
      if (nSelectors < 1) RETURN(BZ_DATA_ERROR);
      for (i = 0; i < nSelectors; i++) {
         NEED_BITS(BZ_X_SELECTOR_3, nGroups);
         j = __builtin_clz(~bsBuff);
         if (j >= nGroups) RETURN(BZ_DATA_ERROR);
         DROP_BITS(j + 1);
         /* Having more than BZ_MAX_SELECTORS doesn't make much sense
            since they will never be used, but some implementations might
            "round up" the number of selectors, so just ignore those. */
         if (i < BZ_MAX_SELECTORS)
           s->selectorMtf[i] = j;
      }
      if (nSelectors > BZ_MAX_SELECTORS)
        nSelectors = BZ_MAX_SELECTORS;

      /*--- Undo the MTF values for the selectors. ---*/
      {
         UChar pos[BZ_N_GROUPS], tmp, v;
         for (v = 0; v < nGroups; v++) pos[v] = v;
   
         for (i = 0; i < nSelectors; i++) {
            v = s->selectorMtf[i];
            tmp = pos[v];
            while (v-- > 0) pos[v + 1] = pos[v];
            pos[0] = tmp;
            s->selector[i] = tmp;
         }
      }

      /*--- Now the coding tables ---*/
      for (t = 0; t < nGroups; t++) {
         GET_BITS(BZ_X_CODING_1, curr, 5);
         for (i = 0; i < alphaSize; i++) {
            NEED_BITS(BZ_X_CODING_2, 24);
            if ((Int32)bsBuff < 0) {
               j = !(bsBuff & 0x40000000) ? 0 : 0x55555500;
               if ((bsBuff & 0xaaaaaa00) == 0xaaaaaa00) {
                  if ((bsBuff ^ j) & 0x55555500) RETURN(BZ_DATA_ERROR);
                  curr += !j ? 12 : -12;
                  DROP_BITS(24);
                  NEED_BITS(BZ_X_CODING_3, 24);
               }
               uc = __builtin_clz(~(bsBuff | 0x55555500));
               if (uc) {
                  if (((bsBuff ^ j) & 0x55555500) >> (32 - uc)) RETURN(BZ_DATA_ERROR);
                  curr += (!j ? uc : -uc) / 2;
                  DROP_BITS(uc);
               }
            }
            DROP_BITS(1);
            if (curr < 1 || curr > 20) RETURN(BZ_DATA_ERROR);
            s->len[t][i] = curr;
         }
      }

      /*--- Create the Huffman decoding tables ---*/
      for (t = 0; t < nGroups; t++) {
         minLen = 32;
         maxLen = 0;
         for (i = 0; i < alphaSize; i++) {
            if (s->len[t][i] > maxLen) maxLen = s->len[t][i];
            if (s->len[t][i] < minLen) minLen = s->len[t][i];
         }
         BZ2_hbCreateDecodeTables ( 
            &(s->limit[t][0]), 
            &(s->base[t][0]), 
            &(s->perm[t][0]), 
            &(s->len[t][0]),
            minLen, maxLen, alphaSize
         );
         s->minLens[t] = minLen;
      }

      /*--- Now the MTF values ---*/

      EOB      = s->nInUse+1;
      nblockMAX = 100000 * s->blockSize100k;
      groupNo  = -1;
      groupPos = 0;

      memset(s->unzftab, 0, sizeof(s->unzftab));
      BZ2_MtfDecodeInit(s);

      nblock = 0;
      while (True) {

         GET_MTF_VAL(BZ_X_MTF_1, BZ_X_MTF_2, nextSym);
         if (nextSym == BZ_RUNA || nextSym == BZ_RUNB) {
            es = 0;
            N = 1;
            do {
               /* Check that N doesn't get too big, so that es doesn't
                  go negative.  The maximum value that can be
                  RUNA/RUNB encoded is equal to the block size (post
                  the initial RLE), viz, 900k, so bounding N at 2
                  million should guard against overflow without
                  rejecting any legitimate inputs. */
               if (N >= 2*1024*1024) RETURN(BZ_DATA_ERROR);
               es += N << (nextSym - BZ_RUNA);
               N = N * 2;
               GET_MTF_VAL(BZ_X_MTF_3, BZ_X_MTF_4, nextSym);
            } while (nextSym == BZ_RUNA || nextSym == BZ_RUNB);

            uc = s->seqToUnseq[ s->mtfa[s->mtfbase[0]] ];
            s->unzftab[uc] += es;

            if (nblock + es > nblockMAX) RETURN(BZ_DATA_ERROR);

            if (s->smallDecompress)
               while (es-- > 0)
                  s->ll16[nblock++] = (UInt16)uc;
            else
               while (es-- > 0)
                  s->tt[nblock++] = (UInt32)uc;
         }

         if (nextSym == EOB) break;
         if (nblock >= nblockMAX) RETURN(BZ_DATA_ERROR);

         uc = BZ2_MtfDecode(s, nextSym - 1);
         s->unzftab[s->seqToUnseq[uc]]++;
         if (s->smallDecompress)
            s->ll16[nblock] = (UInt16)(s->seqToUnseq[uc]);
         else
            s->tt[nblock]   = (UInt32)(s->seqToUnseq[uc]);
         nblock++;
      }

      /* Now we know what nblock is, we can do a better sanity
         check on s->origPtr.
      */
      if (s->origPtr < 0 || s->origPtr >= nblock)
         RETURN(BZ_DATA_ERROR);

      /*-- Set up cftab to facilitate generation of T^(-1) --*/
      /* Actually generate cftab. */
      s->cftab[0] = prev = 0;
      for (i = 1; i <= 256; i++) {
         /* Check: unzftab entries in range. */
         if (s->unzftab[i - 1] < 0 || s->unzftab[i - 1] > nblock) {
            RETURN(BZ_DATA_ERROR);
         }
         s->cftab[i] = s->unzftab[i-1] + prev;
         /* Check: cftab entries in range. */
         if (s->cftab[i] < 0 || s->cftab[i] > nblock) {
            /* s->cftab[i] can legitimately be == nblock */
            RETURN(BZ_DATA_ERROR);
         }
         /* Check: cftab entries non-descending. */
         if (prev > s->cftab[i]) {
            RETURN(BZ_DATA_ERROR);
         }
         prev = s->cftab[i];
      }

      s->state_out_len = 0;
      s->state_out_ch  = 0;
      BZ_INITIALISE_CRC ( s->calculatedBlockCRC );
      s->state = BZ_X_OUTPUT;
      if (s->verbosity >= 2) VPrintf0 ( "rt+rld" );

      if (s->smallDecompress) {

         /*-- Make a copy of cftab, used in generation of T --*/
         memcpy(s->cftabCopy, s->cftab, sizeof(s->cftab));

         /*-- compute the T vector --*/
         for (i = 0; i < nblock; i++) {
            uc = (UChar)(s->ll16[i]);
            SET_LL(i, s->cftabCopy[uc]);
            s->cftabCopy[uc]++;
         }

         /*-- Compute T^(-1) by pointer reversal on T --*/
         i = s->origPtr;
         j = GET_LL(i);
         do {
            Int32 tmp = GET_LL(j);
            SET_LL(j, i);
            i = j;
            j = tmp;
         } while (i != s->origPtr);

         s->tPos = s->origPtr;
         s->nblock_used = 0;
         if (s->blockRandomised) {
            BZ_RAND_INIT_MASK;
            BZ_GET_SMALL(s->k0); s->nblock_used++;
            BZ_RAND_UPD_MASK; s->k0 ^= BZ_RAND_MASK; 
         } else {
            BZ_GET_SMALL(s->k0); s->nblock_used++;
         }

      } else {

         /*-- compute the T^(-1) vector --*/
         for (i = 0; i < nblock; i++) {
            uc = (UChar)(s->tt[i] & 0xff);
            s->tt[s->cftab[uc]] |= (i << 8);
            s->cftab[uc]++;
         }

         s->tPos = s->tt[s->origPtr] >> 8;
         s->nblock_used = 0;
         if (s->blockRandomised) {
            BZ_RAND_INIT_MASK;
            BZ_GET_FAST(s->k0); s->nblock_used++;
            BZ_RAND_UPD_MASK; s->k0 ^= BZ_RAND_MASK; 
         } else {
            BZ_GET_FAST(s->k0); s->nblock_used++;
         }
      }

      RETURN(BZ_OK);



    endhdr_2:

      GET_UCHAR(BZ_X_ENDHDR_2, uc);
      if (uc != 0x72) RETURN(BZ_DATA_ERROR);
      GET_UCHAR(BZ_X_ENDHDR_3, uc);
      if (uc != 0x45) RETURN(BZ_DATA_ERROR);
      GET_UCHAR(BZ_X_ENDHDR_4, uc);
      if (uc != 0x38) RETURN(BZ_DATA_ERROR);
      GET_UCHAR(BZ_X_ENDHDR_5, uc);
      if (uc != 0x50) RETURN(BZ_DATA_ERROR);
      GET_UCHAR(BZ_X_ENDHDR_6, uc);
      if (uc != 0x90) RETURN(BZ_DATA_ERROR);

      s->storedCombinedCRC = 0;
      GET_UCHAR(BZ_X_CCRC_1, uc);
      s->storedCombinedCRC = (s->storedCombinedCRC << 8) | ((UInt32)uc);
      GET_UCHAR(BZ_X_CCRC_2, uc);
      s->storedCombinedCRC = (s->storedCombinedCRC << 8) | ((UInt32)uc);
      GET_UCHAR(BZ_X_CCRC_3, uc);
      s->storedCombinedCRC = (s->storedCombinedCRC << 8) | ((UInt32)uc);
      GET_UCHAR(BZ_X_CCRC_4, uc);
      s->storedCombinedCRC = (s->storedCombinedCRC << 8) | ((UInt32)uc);

      s->state = BZ_X_IDLE;
      RETURN(BZ_STREAM_END);

      default: AssertH ( False, 4001 );
   }

   AssertH ( False, 4002 );

   save_state_and_return:

   s->save_i           = i;
   s->save_j           = j;
   s->save_t           = t;
   s->save_alphaSize   = alphaSize;
   s->save_nGroups     = nGroups;
   s->save_nSelectors  = nSelectors;
   s->save_EOB         = EOB;
   s->save_groupNo     = groupNo;
   s->save_groupPos    = groupPos;
   s->save_nextSym     = nextSym;
   s->save_nblockMAX   = nblockMAX;
   s->save_nblock      = nblock;
   s->save_es          = es;
   s->save_N           = N;
   s->save_curr        = curr;
   s->save_zt          = zt;
   s->save_zn          = zn;
   s->save_zvec        = zvec;
   s->save_zj          = zj;
   s->save_gSel        = gSel;
   s->save_gMinlen     = gMinlen;
   s->save_gLimit      = gLimit;
   s->save_gBase       = gBase;
   s->save_gPerm       = gPerm;

   s->bsBuff = bsBuff;
   s->bsLive = bsLive;

   consumed = (char*)inPtr - s->strm->next_in;
   s->strm->next_in = (char*)inPtr;
   s->strm->avail_in -= consumed;
   s->strm->total_in_lo32 += consumed;
   if (s->strm->total_in_lo32 < consumed)
      s->strm->total_in_hi32++;

   return retVal;
}


/*-------------------------------------------------------------*/
/*--- end                                      decompress.c ---*/
/*-------------------------------------------------------------*/
