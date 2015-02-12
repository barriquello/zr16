/*-------------------------------------------------------------------------

  SDCCralloc.h - header file register allocation

                Written By -  Sandeep Dutta . sandeep.dutta@usa.net (1998)

   This program is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by the
   Free Software Foundation; either version 2, or (at your option) any
   later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

   In other words, you are welcome to use, share and improve this program.
   You are forbidden to forbid anyone else to use, share and improve
   what you give them.   Help stamp out software-hoarding!
-------------------------------------------------------------------------*/
#include "SDCCicode.h"
#include "SDCCBBlock.h"
#ifndef SDCCRALLOC_H
#define SDCCRALLOC_H 1

enum
{
  R11_IDX = 0, R13_IDX , R14_IDX , R10_IDX , 
  R12_IDX, R9_IDX  , R8_IDX, 
  R7_IDX , R6_IDX, R5_IDX, R4_IDX,
  R3_IDX, R2_IDX, R1_IDX, R0_IDX, CND_IDX, END_IDX
};

#define DPL_IDX R8_IDX
#define DPH_IDX R9_IDX
#define A_IDX R11_IDX
#define B_IDX R12_IDX

#define REG_PTR 0x01
#define REG_GPR 0x02
#define REG_CND 0x04
#define REG_BIT 0x08
/* definition for the registers */
typedef struct reg_info
{
  short type;                   /* can have value
                                   REG_GPR, REG_PTR or REG_CND */
  short rIdx;                   /* index into register table */
  short otype;
  char *name;                   /* name */
  char *dname;                  /* name when direct access needed */
  char *base;                   /* base address */
  short offset;                 /* offset from the base */
  unsigned isFree:1;            /* is currently unassigned  */

  struct
  {
    unsigned valueKnown:1;
    unsigned char value;        /* only valid when valueKnown is set */
    char *symbol;               /* holds symbol if value is known by symbol */
  }
  rtrack;
}
reg_info;
extern reg_info regsZR16[];

reg_info *zr16_regWithIdx (int);

bitVect *zr16_rUmaskForOp (operand * op);
bitVect *zr16_allBitregs (void);
bitVect *zr16_allBankregs (void);

extern int zr16_ptrRegReq;
extern int zr16_nRegs;

#endif
