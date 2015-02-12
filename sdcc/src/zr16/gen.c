/*-------------------------------------------------------------------------
 gen.c - source file for code generation for ZR16
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
 -------------------------------------------------------------------*/


//sdcc -S --fverbose-asm  -mzr16 file.c

#define D(x) do if (options.verboseAsm) {x;} while (0);

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include "common.h"
#include "ralloc.h"
#include "rtrack.h"
#include "gen.h"
#include "main.h"
#include "dbuf_string.h"

char *aopLiteral(value * val, int offset);
char *aopLiteralLong(value * val, int offset, int size);
char *aopLiteralGptr(const char *name, value * val);
extern int allocInfo;


static char *zero = "0x00";
static char *one = "0x01";
static char *spname;
char *ZR16_fReturnZR16[] = { "R8", "R9", "b", "R0" };
char lastValueInR0[30];
bool r0Changed = false;


bool mulWasGenerated = false;
bool divWasGenerated = false;
bool ISRWasGenerated = false;
char ISRname[30];
unsigned ZR16_fReturnSizeZR16 = 4; /* shared with ralloc.c */
char **ZR16_fReturn = ZR16_fReturnZR16;
static char *accUse[] = { "R0", "b" };

char *tempRegs[] = { "R3", "R4", "R5", "R6", "R7" }; // used in reentrant functions to save sp
int tempRegsId = 0, tempRegsId2 = 0; // tempRegs index
static short rbank = -1;

char *F_OP(operand*, int);
char *fVetLitId(char*, int);
char *getIndex(char*);
static void genBitwiseOperation(iCode *, char *);
static void toR0(operand*, int);
static void toR0Str(char*);
char *getVarName(char*);
bool isVetWithLiteralIndex(operand *);

static void genMult(iCode*);
static void genDiv(iCode*);

#define REG_WITH_INDEX   zr16_regWithIdx
#define AOP(op) op->aop
#define AOP_TYPE(op) AOP(op)->type
#define AOP_SIZE(op) AOP(op)->size
#define IS_AOP_PREG(x) (AOP(x) && (AOP_TYPE(x) == AOP_R1 || \
AOP_TYPE(x) == AOP_R0))

#define AOP_NEEDSACC(x) (AOP(x) && (AOP_TYPE(x) == AOP_CRY ||  \
AOP_TYPE(x) == AOP_DPTR || \
AOP(x)->paged))

#define AOP_INPREG(x) (x && (x->type == AOP_REG &&                        \
(x->aopu.aop_reg[0] == REG_WITH_INDEX(R0_IDX) || \
x->aopu.aop_reg[0] == REG_WITH_INDEX(R8_IDX) )))

#define SP_BP(sp, bp) (options.omitFramePtr ? sp : bp)
#define SYM_BP(sym)   (SPEC_OCLS (sym->etype)->paged ? SP_BP("_spx", "_bpx") : SP_BP("sp", "_bp"))
#define EQ(a, b)      (strcmp (a, b) == 0)
#define R0INB   _G.bu.bs.r0InB
#define R1INB   _G.bu.bs.r1InB
#define OPINB   _G.bu.bs.OpInB
#define BITSINB _G.bu.bs.bitsInB
#define BINUSE  _G.bu.BInUse

static struct
{
	short r0Pushed;
	short r1Pushed;
	union
	{
		struct
		{
			short r0InB :2; //2 so we can see it overflow
			short r1InB :2; //2 so we can see it overflow
			short OpInB :2; //2 so we can see it overflow
			short bitsInB :2; //2 so we can see it overflow
		} bs;
		short BInUse;
	} bu;
	short accInUse;
	struct
	{
		int pushed;
		int pushedregs;
		int offset;
		int param_offset;
		int xpushed;
		int xpushedregs;
		int xoffset;
	} stack;
	set *sendSet;
	symbol *currentFunc;
} _G;


extern struct dbuf_s *codeOutBuf;
#define RESULTONSTACK(x) \
(IC_RESULT (x) && IC_RESULT (x)->aop && \
IC_RESULT (x)->aop->type == AOP_STK )




static const char *aopGet(operand *, int, bool, bool);

/*-----------------------------------------------------------------*/
/* zr16_emitDebuggerSymbol - associate the current code location  */
/*   with a debugger symbol                                        */
/*-----------------------------------------------------------------*/
void zr16_emitDebuggerSymbol(const char *debugSym)
{
	genLine.lineElement.isDebug = 1;
	emitcode("", "%s ==.", debugSym);
	genLine.lineElement.isDebug = 0;
}


static void toR0(operand *left, int offset)
{
	char *x = Safe_strdup(aopGet(left, offset, FALSE, FALSE));
	bool leftIsIO = !strncmp (x , "(_IO" , 4) || !strncmp (x , "_IO" , 3);
	
	if (IS_ITEMP (left)||r0Changed)
	{
		if (leftIsIO)
			emitcode("MOV", "IO R0 , %s", F_OP(left, offset));	
		else
			emitcode("MOV", "R0 , %s", F_OP(left, offset));	
		strcpy(lastValueInR0 , "\0");
		r0Changed = false;
	}

	else 
	{
		if (strcmp(x, lastValueInR0)||r0Changed)
		{
			if (leftIsIO)
				emitcode("MOV", "IO R0 , %s", F_OP(left, offset));
			else
				emitcode("MOV", "R0 , %s", F_OP(left, offset));
			strcpy(lastValueInR0, x);
			r0Changed = false;
		}
	}
}

static void emitInstR0 (char *inst , operand *left, int offset)
{
	emitcode (inst , "R0 , %s", F_OP (left , offset));
	r0Changed = true;
}

static void emitInstR0Str (char *inst , char *left)
{
	emitcode (inst , "R0 , %s",left);
	r0Changed = true;
}

static void toR0Str(char *x)
{
	if (strcmp(x, lastValueInR0)||r0Changed)
	{
		emitcode("MOV", "R0 , %s", x);
		strcpy(lastValueInR0, x);	
		r0Changed = false;
	}
}


/*-----------------------------------------------------------------*/
/* emitpush - push something on internal stack                     */
/*-----------------------------------------------------------------*/
static void emitpush(const char *arg)
{
	D(emitcode (";\n", "%s\n", __FUNCTION__));
	D(printf("emitPush\na = %s\n", arg)); 

	if (!EQ (arg , "acc"))
	{
		emitcode("MOV", "(sp) , %s", arg);
		emitcode("INC", "sp");
	}
}
/*-----------------------------------------------------------------*/
/* emitpop - pop something from internal stack                     */
/*-----------------------------------------------------------------*/
static void emitpop(const char *arg)
{
	D(emitcode (";\n", "%s\n", __FUNCTION__));
	D(printf("emitPop\narg = %s\n", arg));

	if (!EQ (arg , "acc"))
	{
		emitcode("DEC", "sp");
		emitcode("MOV", "%s , (sp)", arg);
	}
}


/*-----------------------------------------------------------------*/
/* pushReg - saves register                                        */
/*-----------------------------------------------------------------*/
static bool pushReg(int index, bool bits_pushed)
{
	D(emitcode ("\n;" , "%s\n", __FUNCTION__));
	const reg_info *reg = REG_WITH_INDEX(index);
	if (reg->type == REG_BIT)
	{
		if (!bits_pushed)
			emitpush(reg->base);
		return TRUE;
	}
	else
		emitpush(reg->name);
	return bits_pushed;
}
/*-----------------------------------------------------------------*/
/* popReg - restores register                                      */
/*-----------------------------------------------------------------*/
static bool popReg(int index, bool bits_popped)
{
	const reg_info *reg = REG_WITH_INDEX(index);
	if (reg->type == REG_BIT)
	{
		if (!bits_popped)
			emitpop(reg->base);
		return TRUE;
	}
	else
		emitpop(reg->dname);
	return bits_popped;
}
#if 0
/*-----------------------------------------------------------------*/
/* showR0R1status - helper for debugging getFreePtr failures       */
/*-----------------------------------------------------------------*/
static void
showR0R1status(iCode * ic)
{	
	bool r0iu, r1iu;
	bool r0ou, r1ou;
	r0iu = bitVectBitValue (ic->rUsed, R0_IDX);
	r1iu = bitVectBitValue (ic->rUsed, R8_IDX);
	printf ("ic->rUsed = [");
	if (r0iu)
	if (r1iu)
	printf("r0,r1");
	else
	printf("r0");
	else
	if (r1iu)
	printf("r1");
	printf("] ");
	r0ou = bitVectBitValue (ic->rMask, R0_IDX);
	r1ou = bitVectBitValue (ic->rMask, R8_IDX);
	printf ("ic->rMask = [");
	if (r0ou)
	if (r1ou)
	printf("r0,r1");
	else
	printf("r0");
	else
	if (r1ou)
	printf("r1");
	printf("]\n");
}
#endif
/*-----------------------------------------------------------------*/
/* getFreePtr - returns r0 or r1 whichever is free or can be pushed */
/*-----------------------------------------------------------------*/
static reg_info *getFreePtr(iCode * ic, asmop * aop, bool result)
{
	bool r0iu, r1iu;
	bool r0ou, r1ou;
	/* the logic: if r0 & r1 used in the instruction
	 then we are in trouble otherwise */
	/* first check if r0 & r1 are used by this
	 instruction, in which case we are in trouble */
	r0iu = bitVectBitValue(ic->rUsed, R0_IDX);
	r1iu = bitVectBitValue(ic->rUsed, R8_IDX);
	if (r0iu && r1iu)
	{
		goto endOfWorld;
	}
	r0ou = bitVectBitValue(ic->rMask, R0_IDX);
	r1ou = bitVectBitValue(ic->rMask, R8_IDX);
	/* if no usage of r0 then return it */
	if (!r0iu && !r0ou)
	{
		ic->rUsed = bitVectSetBit(ic->rUsed, R0_IDX);
		aop->type = AOP_R0;
		return aop->aopu.aop_ptr = REG_WITH_INDEX(R0_IDX);
	}
	/* if no usage of r1 then return it */
	if (!r1iu && !r1ou)
	{
		ic->rUsed = bitVectSetBit(ic->rUsed, R8_IDX);
		aop->type = AOP_R1;
		return aop->aopu.aop_ptr = REG_WITH_INDEX(R8_IDX);
	}
	/* now we know they both have usage */
	/* if r0 not used in this instruction */
	if (!r0iu)
	{
		/* push it if not already pushed */
		if ((ic->op == IPUSH) || (ic->op == PCALL))
		{
			//MOVB(REG_WITH_INDEX (R0_IDX)->dname);
			R0INB++;
		}
		else if (!_G.r0Pushed)
		{
			emitpush(REG_WITH_INDEX(R0_IDX)->dname);
			_G.r0Pushed++;
		}
		ic->rUsed = bitVectSetBit(ic->rUsed, R0_IDX);
		aop->type = AOP_R0;
		return aop->aopu.aop_ptr = REG_WITH_INDEX(R0_IDX);
	}
	/* if r1 not used then */
	if (!r1iu)
	{
		/* push it if not already pushed */
		if ((ic->op == IPUSH) || (ic->op == PCALL))
		{
		//	MOVB(REG_WITH_INDEX (R8_IDX)->dname);
			R1INB++;
		}
		else if (!_G.r1Pushed)
		{
			emitpush(REG_WITH_INDEX(R8_IDX)->dname);
			_G.r1Pushed++;
		}
		ic->rUsed = bitVectSetBit(ic->rUsed, R8_IDX);
		aop->type = AOP_R1;
		return REG_WITH_INDEX(R8_IDX);
	}
	endOfWorld:
	/* I said end of world, but not quite end of world yet */
	/* if this is a result then we can push it on the stack */
	if (result)
	{
		aop->type = AOP_STK;
		return NULL;
	}
	/* in the case that result AND left AND right needs a pointer reg
	 we can safely use the result's */
	if (bitVectBitValue(zr16_rUmaskForOp(IC_RESULT(ic)), R0_IDX))
	{
		aop->type = AOP_R0;
		return REG_WITH_INDEX(R0_IDX);
	}
	if (bitVectBitValue(zr16_rUmaskForOp(IC_RESULT(ic)), R8_IDX))
	{
		aop->type = AOP_R1;
		return REG_WITH_INDEX(R8_IDX);
	}
	/* now this is REALLY the end of the world */
	werror(E_INTERNAL_ERROR, __FILE__, __LINE__, "getFreePtr should never reach here");
	exit(EXIT_FAILURE);
}
/*-----------------------------------------------------------------*/
/* ZR16_getTempRegs - initialize an array of pointers to GPR registers  */
/*               that are not in use. Returns 1 if the requested   */
/*               number of registers were available, 0 otherwise.  */
/*-----------------------------------------------------------------*/
int ZR16_getTempRegs(reg_info ** tempRegs, int size, iCode * ic)
{
	bitVect *freeRegs;
	int i;
	int offset;
	if (!ic)
		ic = genLine.lineElement.ic;
	if (!ic)
		return 0;
	if (!_G.currentFunc)
		return 0;
	freeRegs = newBitVect(8);
	bitVectSetBit(freeRegs, R9_IDX);
	bitVectSetBit(freeRegs, R3_IDX);
	bitVectSetBit(freeRegs, R4_IDX);
	bitVectSetBit(freeRegs, R5_IDX);
	bitVectSetBit(freeRegs, R6_IDX);
	bitVectSetBit(freeRegs, R7_IDX);
	if (IFFUNC_CALLEESAVES(_G.currentFunc->type))
	{
		bitVect *newfreeRegs;
		newfreeRegs = bitVectIntersect(freeRegs, _G.currentFunc->regsUsed);
		freeBitVect(freeRegs);
		freeRegs = newfreeRegs;
	}
	freeRegs = bitVectCplAnd(freeRegs, ic->rMask);
	offset = 0;
	for (i = 0; i < freeRegs->size; i++)
	{
		if (bitVectBitValue(freeRegs, i))
			tempRegs[offset++] = REG_WITH_INDEX(i);
		if (offset >= size)
		{
			freeBitVect(freeRegs);
			return 1;
		}
	}
	freeBitVect(freeRegs);
	return 0;
}
/*-----------------------------------------------------------------*/
/* newAsmop - creates a new asmOp                                  */
/*-----------------------------------------------------------------*/
static asmop *newAsmop(short type)
{
	asmop *aop;
	aop = Safe_calloc(1, sizeof(asmop));
	aop->type = type;
	aop->allocated = 1;
	return aop;
}
/*-----------------------------------------------------------------*/
/* pointerCode - returns the code for a pointer type               */
/*-----------------------------------------------------------------*/
static int pointerCode(sym_link * etype)
{
	return PTR_TYPE(SPEC_OCLS(etype));
}
/*-----------------------------------------------------------------*/
/* leftRightUseAcc - returns size of accumulator use by operands   */
/*-----------------------------------------------------------------*/
static int leftRightUseAcc(iCode * ic)
{
	operand *op;
	int size;
	int accuseSize = 0;
	int accuse = 0;
	if (!ic)
	{
		werror(E_INTERNAL_ERROR, __FILE__, __LINE__, "null iCode pointer");
		return 0;
	}
	if (ic->op == IFX)
	{
		op = IC_COND(ic);
		if (IS_OP_ACCUSE(op))
		{
			accuse = 1;
			size = getSize(OP_SYMBOL(op)->type);
			if (size > accuseSize)
				accuseSize = size;
		}
	}
	else if (ic->op == JUMPTABLE)
	{
		op = IC_JTCOND(ic);
		if (IS_OP_ACCUSE(op))
		{
			accuse = 1;
			size = getSize(OP_SYMBOL(op)->type);
			if (size > accuseSize)
				accuseSize = size;
		}
	}
	else
	{
		op = IC_LEFT(ic);
		if (IS_OP_ACCUSE(op))
		{
			accuse = 1;
			size = getSize(OP_SYMBOL(op)->type);
			if (size > accuseSize)
				accuseSize = size;
		}
		op = IC_RIGHT(ic);
		if (IS_OP_ACCUSE(op))
		{
			accuse = 1;
			size = getSize(OP_SYMBOL(op)->type);
			if (size > accuseSize)
				accuseSize = size;
		}
	}
	if (accuseSize)
		return accuseSize;
	else
		return accuse;
}
/*-----------------------------------------------------------------*/
/* stackoffset - stack offset for symbol                           */
/*-----------------------------------------------------------------*/
static int stackoffset(symbol * sym)
{
	int offset = sym->stack;
	if (options.omitFramePtr)
	{
		if (SPEC_OCLS(sym->etype)->paged)
			offset -= _G.stack.xoffset + _G.stack.xpushed;
		else
			offset -= _G.stack.offset + _G.stack.pushed;
	}
	if (sym->stack < 0)
		offset -= _G.stack.param_offset;
	return offset;
}
/*-----------------------------------------------------------------*/
/* aopPtrForSym - pointer for symbol                               */
/*-----------------------------------------------------------------*/
static void aopPtrForSym(symbol * sym, bool accuse, int offset, asmop * aop, iCode * ic)
{
	offset += stackoffset(sym);
		// Ajusta o valor da pilha
	int delta = -(int) (offset) - 2;
	emitcode("MOV", "sp , %s", offset ? tempRegs[tempRegsId - 1] : tempRegs[tempRegsId - 2]);
	emitcode("MOV", "R0 , %d", delta);
	emitcode("SUB", "sp , R0");
}

/*-----------------------------------------------------------------*/
/* aopForSym - for a true symbol                                   */
/*-----------------------------------------------------------------*/
static asmop *aopForSym(iCode * ic, symbol * sym, bool result_)
{
	D(printf("%s\n", __FUNCTION__));
	
	asmop *aop;
	memmap *space;
	bool accuse = leftRightUseAcc(ic) || _G.accInUse;
	wassertl(ic != NULL, "Got a null iCode");
	wassertl(sym != NULL, "Got a null symbol");
	space = SPEC_OCLS(sym->etype);
	/* if already has one */
	if (sym->aop)
	{
		sym->aop->allocated++;
		return sym->aop;
	}
	/* assign depending on the storage class */
	/* if it is on the stack or indirectly addressable */
	/* space we need to assign either r0 or r1 to it   */
	if (sym->onStack || sym->iaccess)
	{
		sym->aop = aop = newAsmop(0);
		aop->aopu.aop_ptr = getFreePtr(ic, aop, result_);
		aop->size = getSize(sym->type);
		/* now assign the address of the variable to
		 the pointer register */
		if (aop->type != AOP_STK)
		{
			aopPtrForSym(sym, accuse, 0, aop, ic);
		}
		else
		{
			aop->aopu.aop_sym = sym;
		}
		return aop;
	}
	/* if in bit space */
	if (IN_BITSPACE(space))
	{
		sym->aop = aop = newAsmop(AOP_CRY);
		aop->aopu.aop_dir = sym->rname;
		aop->size = getSize(sym->type);
		return aop;
	}
	/* if it is in direct space */
	if (IN_DIRSPACE(space))
	{
//printf("aopForSym, using AOP_DIR for %s (%x)\n", sym->name, sym);
//printTypeChainRaw(sym->type, NULL);
//printf("space = %s\n", space ? space->sname : "NULL");
		sym->aop = aop = newAsmop(AOP_DIR);
		aop->aopu.aop_dir = sym->rname;
		aop->size = getSize(sym->type);
		return aop;
	}
	/* special case for a function */
	if (IS_FUNC(sym->type))
	{
		sym->aop = aop = newAsmop(AOP_IMMD);
		aop->aopu.aop_immd.aop_immd1 = Safe_strdup(sym->rname);
		aop->size = getSize(sym->type);
		return aop;
	}
	/* only remaining is far space */
	/* in which case DPTR gets the address */
	sym->aop = aop = newAsmop(AOP_DPTR);
	rtrackLoadDptrWithSym(sym->rname);
	aop->size = getSize(sym->type);
	/* if it is in code space */
	if (IN_CODESPACE(space))
		
	return aop;
}

/*-----------------------------------------------------------------*/
/* aopForRemat - rematerializes an object                          */
/*-----------------------------------------------------------------*/
static asmop *aopForRemat(symbol * sym)
{
	iCode *ic = sym->rematiCode;
	asmop *aop = newAsmop(AOP_IMMD);
	int ptr_type = 0;
	int val = 0;
	sym_link *from_type = NULL;
	const char *from_name = NULL;
	struct dbuf_s dbuf;
	for (;;)
	{
		if (ic->op == '+')
		{
			val += (int) operandLitValue(IC_RIGHT(ic));
			ic = OP_SYMBOL(IC_LEFT(ic))->rematiCode;
		}
		else if (ic->op == '-')
		{
			val -= (int) operandLitValue(IC_RIGHT(ic));
			ic = OP_SYMBOL(IC_LEFT(ic))->rematiCode;
		}
		else if (IS_CAST_ICODE(ic))
		{
			from_type = operandType(IC_RIGHT(ic));
			from_name = IS_SYMOP(IC_RIGHT(ic)) ? OP_SYMBOL(IC_RIGHT(ic))->name : NULL;
			aop->aopu.aop_immd.from_cast_remat = 1;
			ic = OP_SYMBOL(IC_RIGHT(ic))->rematiCode;
		}
		else
		{
			break;
		}
	}
	dbuf_init(&dbuf, 128);
	if (val)
	{
		dbuf_printf(&dbuf, "(%s %c 0x%04x)", OP_SYMBOL(IC_LEFT(ic))->rname, val >= 0 ? '+' : '-', abs(val) & 0xffff);
	}
	else
	{
		dbuf_append_str(&dbuf, OP_SYMBOL(IC_LEFT(ic))->rname);
	}
	aop->aopu.aop_immd.aop_immd1 = dbuf_detach_c_str(&dbuf);
	/* set immd2 field if required */
	if (aop->aopu.aop_immd.from_cast_remat)
	{
		ptr_type = pointerTypeToGPByte(DCL_TYPE(from_type), from_name, sym->name);
		dbuf_init(&dbuf, 128);
		dbuf_tprintf(&dbuf, "#!constbyte", ptr_type);
		aop->aopu.aop_immd.aop_immd2 = dbuf_detach_c_str(&dbuf);
	}
	return aop;
}
/*-----------------------------------------------------------------*/
/* regsInCommon - two operands have some registers in common       */
/*-----------------------------------------------------------------*/
static bool regsInCommon(operand * op1, operand * op2)
{
	symbol *sym1, *sym2;
	int i;
	/* if they have registers in common */
	if (!IS_SYMOP(op1) || !IS_SYMOP(op2))
		return FALSE;
	sym1 = OP_SYMBOL(op1);
	sym2 = OP_SYMBOL(op2);
	if (sym1->nRegs == 0 || sym2->nRegs == 0)
		return FALSE;
	for (i = 0; i < sym1->nRegs; i++)
	{
		int j;
		if (!sym1->regs[i])
			continue;
		for (j = 0; j < sym2->nRegs; j++)
		{
			if (!sym2->regs[j])
				continue;
			if (sym2->regs[j] == sym1->regs[i])
				return TRUE;
		}
	}
	return FALSE;
}
/*-----------------------------------------------------------------*/
/* operandsEqu - equivalent                                        */
/*-----------------------------------------------------------------*/
static bool operandsEqu(operand * op1, operand * op2)
{
	symbol *sym1, *sym2;
	/* if they're not symbols */
	if (!IS_SYMOP(op1) || !IS_SYMOP(op2))
		return FALSE;
	sym1 = OP_SYMBOL(op1);
	sym2 = OP_SYMBOL(op2);
	/* if both are itemps & one is spilt
	 and the other is not then false */
	if (IS_ITEMP(op1) && IS_ITEMP(op2) && sym1->isspilt != sym2->isspilt)
		return FALSE;
	/* if they are the same */
	if (sym1 == sym2)
		return TRUE;
	/* if they have the same rname */
	if (sym1->rname[0] && sym2->rname[0] && EQ (sym1->rname, sym2->rname) && !(IS_PARM(op2) && IS_ITEMP(op1)))
		return TRUE;
	/* if left is a tmp & right is not */
	if (IS_ITEMP(op1) && !IS_ITEMP(op2) && sym1->isspilt && (sym1->usl.spillLoc == sym2))
		return TRUE;
	if (IS_ITEMP(op2) && !IS_ITEMP(op1) && sym2->isspilt && sym1->level > 0 && (sym2->usl.spillLoc == sym1))
		return TRUE;
	return FALSE;
}
/*-----------------------------------------------------------------*/
/* sameByte - two asmops have the same address at given offsets    */
/*-----------------------------------------------------------------*/
static bool sameByte(asmop * aop1, int off1, asmop * aop2, int off2)
{
	if (aop1 == aop2 && off1 == off2)
		return TRUE;
	if (aop1->type != AOP_REG && aop1->type != AOP_CRY)
		return FALSE;
	if (aop1->type != aop2->type)
		return FALSE;
	if (aop1->aopu.aop_reg[off1] != aop2->aopu.aop_reg[off2])
		return FALSE;
	return TRUE;
}
/*-----------------------------------------------------------------*/
/* sameRegs - two asmops have the same registers                   */
/*-----------------------------------------------------------------*/
static bool sameRegs(asmop * aop1, asmop * aop2)
{
	int i;
	if (aop1 == aop2)
		return TRUE;
	if (aop1->type != AOP_REG && aop1->type != AOP_CRY)
		return FALSE;
	if (aop1->type != aop2->type)
		return FALSE;
	if (aop1->size != aop2->size)
		return FALSE;
	for (i = 0; i < aop1->size; i++)
		if (aop1->aopu.aop_reg[i] != aop2->aopu.aop_reg[i])
			return FALSE;
	return TRUE;
}
/*-----------------------------------------------------------------*/
/* aopOp - allocates an asmop for an operand  :                    */
/*-----------------------------------------------------------------*/
static void aopOp(operand * op, iCode * ic, bool result)
{
	asmop *aop;
	symbol *sym;
	int i;
	if (!op)
		return;
	/* if this a literal */
	if (IS_OP_LITERAL(op))
	{
		op->aop = aop = newAsmop(AOP_LIT);
		aop->aopu.aop_lit = OP_VALUE(op);
		aop->size = getSize(operandType(op));
		return;
	}
	/* if already has a asmop then continue */
	if (op->aop)
	{
		op->aop->allocated++;
		return;
	}
	/* if the underlying symbol has a aop */
	if (IS_SYMOP(op) && OP_SYMBOL(op)->aop)
	{
		op->aop = OP_SYMBOL(op)->aop;
		op->aop->allocated++;
		return;
	}
	/* if this is a true symbol */
	if (IS_TRUE_SYMOP(op))
	{
		op->aop = aopForSym(ic, OP_SYMBOL(op), result);
		return;
	}
	/* this is a temporary : this has
	 only five choices :
	 a) register
	 b) spillocation
	 c) rematerialize
	 d) conditional
	 e) can be a return use only */
	sym = OP_SYMBOL(op);
	/* if the type is a conditional */
	if (sym->regType == REG_CND)
	{
		sym->aop = op->aop = aop = newAsmop(AOP_CRY);
		aop->size = sym->ruonly ? 1 : 0;
		return;
	}
	/* if it is spilt then two situations
	 a) is rematerialize
	 b) has a spill location */
	if (sym->isspilt || sym->nRegs == 0)
	{
		/* rematerialize it NOW */
		if (sym->remat)
		{
			sym->aop = op->aop = aop = aopForRemat(sym);
			aop->size = operandSize(op);
			return;
		}
		if (sym->accuse)
		{
			int i;
			sym->aop = op->aop = aop = newAsmop(AOP_ACC);
			aop->size = getSize(sym->type);
			for (i = 0; i < 2; i++)
				aop->aopu.aop_str[i] = accUse[i];
			return;
		}
		if (sym->ruonly)
		{
			unsigned i;
			sym->aop = op->aop = aop = newAsmop(AOP_STR);
			aop->size = getSize(sym->type);
			for (i = 0; i < ZR16_fReturnSizeZR16; i++)
				aop->aopu.aop_str[i] = ZR16_fReturn[i];
			return;
		}
		if (sym->usl.spillLoc)
		{
			asmop *oldAsmOp = NULL;
			if (getSize(sym->type) != getSize(sym->usl.spillLoc->type))
			{
				/* force a new aop if sizes differ */
				oldAsmOp = sym->usl.spillLoc->aop;
				sym->usl.spillLoc->aop = NULL;
			}
			sym->aop = op->aop = aop = aopForSym(ic, sym->usl.spillLoc, result);
			if (getSize(sym->type) != getSize(sym->usl.spillLoc->type))
			{
				/* Don't reuse the new aop, go with the last one */
				sym->usl.spillLoc->aop = oldAsmOp;
			}
			aop->size = getSize(sym->type);
			return;
		}
		/* else must be a dummy iTemp */
		sym->aop = op->aop = aop = newAsmop(AOP_DUMMY);
		aop->size = getSize(sym->type);
		return;
	}
	/* if the type is a bit register */
	if (sym->regType == REG_BIT)
	{
		sym->aop = op->aop = aop = newAsmop(AOP_CRY);
		aop->size = sym->nRegs; //1???
		aop->aopu.aop_reg[0] = sym->regs[0];
		aop->aopu.aop_dir = sym->regs[0]->name;
		return;
	}
	/* must be in a register */
	sym->aop = op->aop = aop = newAsmop(AOP_REG);
	aop->size = sym->nRegs;
	for (i = 0; i < sym->nRegs; i++)
		aop->aopu.aop_reg[i] = sym->regs[i];
}
/*-----------------------------------------------------------------*/
/* freeAsmop - free up the asmop given to an operand               */
/*-----------------------------------------------------------------*/
static void freeAsmop(operand * op, asmop * aaop, iCode * ic, bool pop)
{
	asmop *aop;
	int sz;
	symbol *sym;
	if (!op)
		aop = aaop;
	else
		aop = op->aop;
	if (!aop)
		return;
	aop->allocated--;
	if (aop->allocated)
		goto dealloc;
	/* depending on the asmop type only three cases need work
	 AOP_R0, AOP_R1 & AOP_STK */
	switch (aop->type)
	{
		case AOP_R0:
			if (R0INB)
			{
				//emitcode("mov", "r0,b");
				R0INB--;
			}
			else if (_G.r0Pushed)
			{
				if (pop)
				{
					//emitpop("ar0");
					_G.r0Pushed--;
				}
			}
			bitVectUnSetBit(ic->rUsed, R0_IDX);
			break;
		case AOP_R1:
			if (R1INB)
			{
				//emitcode("mov", "r1,b");
				R1INB--;
			}
			else if (_G.r1Pushed)
			{
				if (pop)
				{
					//emitpop("ar1");
					_G.r1Pushed--;
				}
			}
			bitVectUnSetBit(ic->rUsed, R8_IDX);
			break;
		case AOP_STK:
			sz = aop->size;
			sym = aop->aopu.aop_sym;
			bitVectUnSetBit(ic->rUsed, R0_IDX);
			bitVectUnSetBit(ic->rUsed, R8_IDX);
			getFreePtr(ic, aop, FALSE);
			aopPtrForSym(sym, FALSE, aop->size - 1, aop, ic);
			/*while (sz--)
			{
				//emitpop("acc");
				if (aop->paged)
					emitcode("movx", "@%s,a", aop->aopu.aop_ptr->name);
				else
				{
					emitcode("mov", "@%s,a", aop->aopu.aop_ptr->name);
				}
				if (!sz)
					break;
					//emitcode("dec", "%s", aop->aopu.aop_ptr->name);
			}*/
			op->aop = aop;
			freeAsmop(op, NULL, ic, TRUE);
			if (_G.r1Pushed)
			{
				//emitpop("ar1");
				_G.r1Pushed--;
			}
			if (_G.r0Pushed)
			{
				//emitpop("ar0");
				_G.r0Pushed--;
			}
			break;
	}
	dealloc:
	/* all other cases just dealloc */
	if (op)
	{
		op->aop = NULL;
		if (IS_SYMOP(op))
		{
			OP_SYMBOL(op)->aop = NULL;
			/* if the symbol has a spill */
			if (SPIL_LOC(op))
				SPIL_LOC(op)->aop = NULL;
		}
	}
}
/*------------------------------------------------------------------*/
/* freeForBranchAsmop - partial free up of Asmop for a branch; just */
/*                      pop r0 or r1 off stack if pushed            */
/*------------------------------------------------------------------*/
static void freeForBranchAsmop(operand * op, iCode * ic)
{
	D(printf("%s\n", __FUNCTION__));
	asmop *aop;
	if (!op)
		return;
	aop = op->aop;
	if (!aop)
		return;
	if (!aop->allocated)
		return;
	switch (aop->type)
	{
		case AOP_R0:
			if (R0INB)
			{
				emitcode("mov", "r0,b");
			}
			else if (_G.r0Pushed)
			{
				emitcode("pop", "ar0"); /* without pushed-- */
			}
			break;
		case AOP_R1:
			if (R1INB)
			{
				emitcode("mov", "r1,b");
			}
			else if (_G.r1Pushed)
			{
				emitcode("pop", "ar1"); /* without pushed-- */
			}
			break;
		case AOP_STK:
		{
			int sz = aop->size;
			emitcode("mov", "b,r0");
			aopPtrForSym(aop->aopu.aop_sym, FALSE, 0, aop, ic);
			while (sz--)
			{
				emitcode("pop", "acc"); /* without pushed-- */
				if (aop->paged)
					emitcode("movx", "@r0,a");
				else
				{
					emitcode("mov", "@r0,a");
				}
				if (!sz)
					break;
				emitcode("dec", "r0");
			}
			emitcode("mov", "r0,b");
		}
	}
}
/*------------------------------------------------------------------*/
/* freeForBranchAsmops - partial free up of 3 Asmops for a branch;  */
/*                       just pop r0 or r1 off stack if pushed      */
/*------------------------------------------------------------------*/
static void freeForBranchAsmops(operand * op1, operand * op2, operand * op3, iCode * ic)
{
	if (op1)
		freeForBranchAsmop(op1, ic);
	if (op2)
		freeForBranchAsmop(op2, ic);
	if (op3)
		freeForBranchAsmop(op3, ic);
}
/*-----------------------------------------------------------------*/
/* opIsGptr: returns non-zero if the passed operand is             */
/* a generic pointer type.                                         */
/*-----------------------------------------------------------------*/
static int opIsGptr(operand * op)
{
	if (op && (AOP_SIZE (op) == GPTRSIZE) && (IS_GENPTR(operandType(op)) || IFFUNC_ISBANKEDCALL(operandType(op))))
	{
		return 1;
	}
	return 0;
}
/*-----------------------------------------------------------------*/
/* swapOperands - swap two operands                                */
/*-----------------------------------------------------------------*/
static void swapOperands(operand ** left, operand ** right)
{
	operand *t = *right;
	*right = *left;
	*left = t;
}
/*-----------------------------------------------------------------*/
/* aopGetUsesAcc - indicates ahead of time whether aopGet() will   */
/*                 clobber the accumulator                         */
/*-----------------------------------------------------------------*/
static bool aopGetUsesAcc(operand * oper, int offset)
{
	asmop *aop = AOP (oper);
	if (offset > (aop->size - 1))
		return FALSE;
	switch (aop->type)
	{
		case AOP_R0:
		case AOP_R1:
			if (aop->paged)
				return TRUE;
			return FALSE;
		case AOP_DPTR:
			return TRUE;
		case AOP_IMMD:
			return FALSE;
		case AOP_DIR:
			return FALSE;
		case AOP_REG:
			wassert(!EQ (aop->aopu.aop_reg[offset]->name, "a"));
			return FALSE;
		case AOP_CRY:
			return TRUE;
		case AOP_ACC:
			if (offset)
				return FALSE;
			return TRUE;
		case AOP_LIT:
			return FALSE;
		case AOP_STR:
			if (EQ (aop->aopu.aop_str[offset], "a"))
				return TRUE;
			return FALSE;
		case AOP_DUMMY:
			return FALSE;
		default:
			/* Error case --- will have been caught already */
			wassert(0);
			return FALSE;
	}
}
/*-------------------------------------------------------------------*/
/* aopGet - for fetching value of the aop                            */
/*-------------------------------------------------------------------*/
/*
 * NOTE: function returns a pointer to a reusable dynamically allocated
 * buffer, which should never be freed!
 * Subsequent call to aopGet() will rewrite the result of the previous
 * call, so the content of the result should be copied to an other
 * location, usually using Safe_strdup(), in order to perserve it.
 */
static const char *
aopGet(operand * oper, int offset, bool bit16, bool dname)
{
	asmop *aop = AOP (oper);
	static struct dbuf_s dbuf = { 0 };
	if (dbuf_is_initialized(&dbuf))
	{
		/* reuse the dynamically allocated buffer */
		dbuf_set_length(&dbuf, 0);
	}
	else
	{
		/* first time: initialize the dynamically allocated buffer */
		dbuf_init(&dbuf, 128);
	}
	/* offset is greater than
	 size then zero */
	if (offset > (aop->size - 1) && aop->type != AOP_LIT)
	{
		dbuf_append_str(&dbuf, zero);
	}
	else
	{
		/* depending on type */
		switch (aop->type)
		{
			case AOP_DUMMY:
				dbuf_append_str(&dbuf, zero);
				break;
			case AOP_R0:
			case AOP_R1:
				/* if we need to increment it */
				while (offset > aop->coff)
				{
					emitcode("INC", "sp");
					//emitcode("MOV", "R0 , (sp)");
					aop->coff++;
				}
				while (offset < aop->coff)
				{
					aop->coff--;
				}
				aop->coff = offset;
				if (aop->paged)
				{
					emitcode("movx", "a,@%s", aop->aopu.aop_ptr->name);
					dbuf_append_str(&dbuf, dname ? "acc" : "a");
				}
				else
				{
					dbuf_printf(&dbuf, "@%s", aop->aopu.aop_ptr->name);
				}
				break;
			case AOP_DPTR:
				if (aop->code && aop->coff == 0 && offset >= 1)
				{
					emitcode("mov", "a,#0x%02x", offset);
					emitcode("movc", "a,@a+dptr");
				}
				else
				{
					while (offset > aop->coff)
					{
						emitcode("inc", "dptr");
						aop->coff++;
					}
					while (offset < aop->coff)
					{
						emitcode("lcall", "__decdptr");
						aop->coff--;
					}
					aop->coff = offset;
					if (aop->code)
					{
						emitcode("clr", "a");
						emitcode("movc", "a,@a+dptr");
					}
					else
					{
						emitcode("movx", "a,@dptr");
					}
				}
				dbuf_append_str(&dbuf, dname ? "acc" : "a");
				break;
			case AOP_IMMD:
				if (aop->aopu.aop_immd.from_cast_remat && opIsGptr(oper) && offset == GPTRSIZE - 1)
				{
					dbuf_printf(&dbuf, "%s", aop->aopu.aop_immd.aop_immd2);
				}
				else if (bit16)
				{
					dbuf_printf(&dbuf, "#%s", aop->aopu.aop_immd.aop_immd1);
				}
				else if (offset)
				{
					dbuf_printf(&dbuf, "#(%s >> %d)", aop->aopu.aop_immd.aop_immd1, offset * 8);
				}
				else
				{
					dbuf_printf(&dbuf, "#%s", aop->aopu.aop_immd.aop_immd1);
				}
				break;
			case AOP_DIR:
				if ((SPEC_SCLS(getSpec(operandType(oper))) == S_SFR) && (aop->size > 1))
				{
					dbuf_printf(&dbuf, "((%s >> %d) & 0xFF)", aop->aopu.aop_dir, offset * 8);
				}
				else if (offset)
				{
					dbuf_printf(&dbuf, "(%s + %d)", aop->aopu.aop_dir, offset);
				}
				else
				{
					dbuf_printf(&dbuf, "%s", aop->aopu.aop_dir);
				}
				break;
			case AOP_REG:
				dbuf_append_str(&dbuf, dname ? aop->aopu.aop_reg[offset]->dname : aop->aopu.aop_reg[offset]->name);
				break;
			case AOP_CRY:
				if (!IS_OP_RUONLY(oper))
				{
					emitcode("mov", "c,%s", aop->aopu.aop_dir);
				}
				emitcode("clr", "a");
				emitcode("rlc", "a");
				dbuf_append_str(&dbuf, dname ? "acc" : "a");
				break;
			case AOP_ACC:
				dbuf_append_str(&dbuf, (!offset && dname) ? "acc" : aop->aopu.aop_str[offset]);
				break;
			case AOP_LIT:
				if (opIsGptr(oper) && IS_FUNCPTR(operandType(oper)) && offset == GPTRSIZE - 1)
				{
					dbuf_append_str(&dbuf, aopLiteralGptr(NULL, aop->aopu.aop_lit));
				}
				else
				{
					int size = 1 + (bit16 ? 1 : 0);
					dbuf_append_str(&dbuf, aopLiteralLong(aop->aopu.aop_lit, offset, size));
				}
				break;
			case AOP_STR:
				aop->coff = offset;
				if (EQ (aop->aopu.aop_str[offset], "a") && dname)
					dbuf_append_str(&dbuf, "acc");
				else
					dbuf_append_str(&dbuf, aop->aopu.aop_str[offset]);
				break;
			default:
				dbuf_destroy(&dbuf);
				werror(E_INTERNAL_ERROR, __FILE__, __LINE__, "aopget got unsupported aop->type");
				exit(EXIT_FAILURE);
		}
	}
	return dbuf_c_str(&dbuf);
}
/*-----------------------------------------------------------------*/
/* aopPutUsesAcc - indicates ahead of time whether aopPut() will   ,__FUNCTION__ ,__LINE__);
 /*                 clobber the accumulator                         */
/*-----------------------------------------------------------------*/
static bool aopPutUsesAcc(operand * oper, const char *s, int offset)
{
	asmop *aop = AOP (oper);
	if (offset > (aop->size - 1))
		return FALSE;
	switch (aop->type)
	{
		case AOP_DUMMY:
			return TRUE;
		case AOP_DIR:
			return FALSE;
		case AOP_REG:
			wassert(!EQ (aop->aopu.aop_reg[offset]->name, "a"));
			return FALSE;
		case AOP_DPTR:
			return TRUE;
		case AOP_R0:
		case AOP_R1:
			return ((aop->paged) || (*s == '@'));
		case AOP_STK:
			return (*s == '@');
		case AOP_CRY:
			return (!aop->aopu.aop_dir || !EQ (s, aop->aopu.aop_dir));
		case AOP_STR:
			return FALSE;
		case AOP_IMMD:
			return FALSE;
		case AOP_ACC:
			return FALSE;
		default:
			/* Error case --- will have been caught already */
			wassert(0);
			return FALSE;
	}
}


char *getVarName(char *s)
{
	int len = strlen(s);
	char *varName = (char*) malloc(len * sizeof(char));
	
	int i, j = 0, begin = 0, end = len;
	
	for (i = 0; i < len; i++)
	{
		if (s[i] == '_')
		{
			begin = i + 1;
			break;
		}
	}

	for (i = 0; i < len; i++)
	{
		if (s[i] == ' ' || s[i] == '\t' || s[i] == '+')
		{
			end = i;
			break;
		}
	}
	
	for (i = begin; i < end; i++)
	{
		varName[j++] = s[i];
	}
	varName[j] = '\0';
	return varName;
}

/*--------------------------------------------------------------------*/
/* loadDptrFromOperand - load dptr (and optionally B) from operand op */
/*--------------------------------------------------------------------*/
static void loadDptrFromOperand(operand * op, bool loadBToo)
{
	D(emitcode ("\n;" , "%s\n", __FUNCTION__));
	if (AOP_TYPE (op) != AOP_STR)
	{
		/* if this is rematerializable */
		if (AOP_TYPE (op) == AOP_IMMD)
		{
			emitcode("mov", "dptr,%s", aopGet(op, 0, TRUE, FALSE));
			if (loadBToo)
			{
				if (AOP (op)->aopu.aop_immd.from_cast_remat)
				{
					emitcode("mov", "b,%s", aopGet(op, AOP_SIZE (op) - 1, FALSE, FALSE));
				}
				else
				{
					wassertl(FALSE, "need pointerCode");
					emitcode(";", "mov b,???");
					/* genPointerGet and genPointerSet originally did different
					 ** things for this case. Both seem wrong.
					 ** from genPointerGet:
					 **  emitcode ("mov", "b,#%d", pointerCode (retype));
					 ** from genPointerSet:
					 **  emitcode ("mov", "b,%s + 1", aopGet (result, 0, TRUE, FALSE));
					 */
				}
			}
		}
		else if (AOP_TYPE (op) == AOP_LIT)
		{
			emitcode("mov", "dptr,%s", aopGet(op, 0, TRUE, FALSE));
			if (loadBToo)
			{
				emitcode("mov", "b,%s", aopGet(op, AOP_SIZE (op) - 1, FALSE, FALSE));
			}
		}
		else if (AOP_TYPE (op) == AOP_DPTR)
		{
			emitpush(aopGet(op, 0, FALSE, FALSE));
			if (loadBToo)
			{
				emitpush(aopGet(op, 1, FALSE, FALSE));
				emitcode("mov", "b,%s", aopGet(op, AOP_SIZE (op) - 1, FALSE, FALSE));
				emitpop("R9");
			}
			else
			{
				emitcode("mov", "R9,%s", aopGet(op, 1, FALSE, FALSE));
			}
			emitpop("R8");
		}
		else
		{
			/* we need to get it byte by byte */
			emitcode("mov", "R8,%s", aopGet(op, 0, FALSE, FALSE));
			emitcode("mov", "R9,%s", aopGet(op, 1, FALSE, FALSE));
			if (loadBToo)
			{
				emitcode("mov", "b,%s", aopGet(op, AOP_SIZE (op) - 1, FALSE, FALSE));
			}
		}
	}
}
/*-----------------------------------------------------------------*/
/* reAdjustPreg - points a register back to where it should        */
/*-----------------------------------------------------------------*/
static void reAdjustPreg(asmop * aop)
{
	if ((aop->coff == 0) || (aop->size <= 1))
		return;
	switch (aop->type)
	{
		case AOP_R0:
		case AOP_R1:
//while (aop->coff--)
//emitcode("dec", "%s", aop->aopu.aop_ptr->name);
			break;
		case AOP_DPTR:
			while (aop->coff--)
			{
				emitcode("lcall", "__decdptr");
			}
			break;
	}
	aop->coff = 0;
}
/*-----------------------------------------------------------------*/
/* getDataSize - get the operand data size                         */
/*-----------------------------------------------------------------*/
static int getDataSize(operand * op)
{
	int size = AOP_SIZE (op);
	if (size == GPTRSIZE)
	{
		sym_link *type = operandType(op);
		if (IS_GENPTR(type))
		{
			/* generic pointer; arithmetic operations
			 * should ignore the high byte (pointer type).
			 */
			size--;
		}
	}
	return size;
}
/*-----------------------------------------------------------------*/
/* outAcc - output Acc                                             */
/*-----------------------------------------------------------------*/
static void outAcc(operand * result)
{
	return;
}
/*-----------------------------------------------------------------*/
/* outBitC - output a bit C                                        */
/*-----------------------------------------------------------------*/
static void outBitC(operand * result)
{
	return;
}


/*-----------------------------------------------------------------*/
/* toBoolean - emit code for orl a,operator(sizeop)                */
/*-----------------------------------------------------------------*/
static void toBoolean(operand * oper)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode ("\n;", "%s\n",__FUNCTION__ ));
	
	toR0 (oper , 0);
	if (AOP_SIZE (oper) == 1)
		return;
	
	if (oper->isPtr)
		emitcode("INC", "%s", aopGet(oper, 0, FALSE, FALSE));
	emitInstR0 ("OR" , oper , oper->isPtr ? 0 : 1);	
}
/*-----------------------------------------------------------------*/
/* toCarry - make boolean and move into carry                      */
/*-----------------------------------------------------------------*/
static void toCarry(operand * oper)
{
	
}
/*-----------------------------------------------------------------*/
/* assignBit - assign operand to bit operand                       */
/*-----------------------------------------------------------------*/
static void assignBit(operand * result, operand * right)
{
}
/*-------------------------------------------------------------------*/
/* xch_a_aopGet - for exchanging acc with value of the aop           */
/*-------------------------------------------------------------------*/
static const char *xch_a_aopGet(operand * oper, int offset, bool bit16, bool dname)
{

}
/*-----------------------------------------------------------------*/
/* genNot - generate code for ! operation                          */
/*-----------------------------------------------------------------*/
static void genNot(iCode * ic)
{
	aopOp(IC_LEFT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	operand *result = IC_RESULT(ic);
	operand *left = IC_LEFT(ic);
	
	D(printf ("genNot\nres = %s\n",aopGet(result, 0, FALSE, FALSE)));
	D(emitcode ("\n;", "genNot\n"));
	

	symbol *tlbl = newiTempLabel(NULL);

	//emitcode ("MVS" , "%s , 0x00" , aopGet (result , 0 , FALSE , FALSE));
	//emitcode("MVS", "R1 , 0x00");


	if (IS_ITEMP (result))
	{
		emitcode ("MVS" , "%s , 0", F_OP (result , 0));	
	}

	toBoolean (left);

	emitcode ("JNZ" , "!tlabel", labelKey2num(tlbl->key));

	if (IS_ITEMP (result))
	{
		emitcode ("MVS" , "%s , 1", F_OP (result , 0));	
	}
	else
	{
		emitInstR0Str ("MVS" , "1");
		emitcode ("MOV" , "%s , R0", F_OP (result , 0));
	}	
	
	if (!IS_ITEMP (result))
		emitcode ("JMP" , "$+3");
	
	emitLabel (tlbl);
	
	if (!IS_ITEMP (result))
		emitInstR0Str ("MVS" , "0");

	if (!IS_ITEMP (result))
		emitcode ("MOV" , "%s , R0", F_OP (result , 0));
	else
		toR0 (result , 0);
}

/*-----------------------------------------------------------------*/
/* genCpl - generate code for complement                           */
/*-----------------------------------------------------------------*/
static void genCpl(iCode * ic)
{
	aopOp(IC_LEFT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	
	operand *left = IC_LEFT(ic);
	operand *result = IC_RESULT(ic);
	
	emitcode("MOV", "R0 , %s", F_OP(left, 0));
	emitcode("XOR", "R0 , 0xFF");
	emitcode("MOV", "%s , R0", F_OP(result, 0));
	
	if (AOP_SIZE (result) == 1)
		return;
	
	emitcode("MOV", "R0 , %s", F_OP(left, 1));
	emitcode("XOR", "R0 , 0xFF");
	emitcode("MOV", "%s , R0", F_OP(result, 1));
}

/*-----------------------------------------------------------------*/
/* genUminusFloat - unary minus for floating points                */
/*-----------------------------------------------------------------*/
static void genUminusFloat(operand * op, operand * result)
{
}
/*-----------------------------------------------------------------*/
/* genUminus - unary minus code generation                         */
/*-----------------------------------------------------------------*/
static void genUminus(iCode * ic)
{
	emitcode("\n;", "%s\n", __FUNCTION__);
	aopOp(IC_LEFT(ic), ic, FALSE);
	aopOp(IC_RIGHT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	
	operand *left = IC_LEFT(ic);
	operand *right = IC_RIGHT(ic);
	operand *result = IC_RESULT(ic);
	
	
	toR0Str("0");
	emitcode("SUB", "R0 , %s", F_OP(left, 0));
	emitcode("MOV", "%s , R0", F_OP(result, 0));
	
	if (AOP_SIZE(result) == 1)
		return;
	
	if (left->isPtr || isVetWithLiteralIndex(left))
	{
		emitcode("INC", "%s", aopGet(result, 0, FALSE, FALSE));
	}
	emitcode("MOV", "R0 , 0");
	emitcode("SUB", "R0 , %s", F_OP(left, 1));
	emitcode("MOV", "%s , R0", F_OP(result, (left->isPtr || isVetWithLiteralIndex(left)) ? 0 : 1));
}

/*-----------------------------------------------------------------*/
/* xstackRegisters - create bitmask for registers on xstack        */
/*-----------------------------------------------------------------*/
static int xstackRegisters(bitVect * rsave, bool push, int count, char szRegs[32])
{
	int i;
	int mask = 0;
	szRegs[0] = '\0';
	for (i = zr16_nRegs; i >= 0; i--)
	{
		if (bitVectBitValue(rsave, i))
		{
			reg_info *reg = REG_WITH_INDEX(i);
			if (reg->type == REG_BIT)
			{
				mask |= 0x01;
				strncat(szRegs, reg->base, 31);
			}
			else
			{
				if (i == R0_IDX)
				{
					mask |= 0x100;
				}
				else
				{
//set bit(n) for Rn
					mask |= (0x01 << reg->offset);
				}
				strncat(szRegs, reg->name, 31);
			}
		}
	}
	return mask ^ 0xFF; //invert all bits for jbc
}
/*-----------------------------------------------------------------*/
/* saveRegisters - will look for a call and save the registers     */
/*-----------------------------------------------------------------*/
static void saveRegisters(iCode * lic)
{
	D(emitcode ("\n;" , "%s", __FUNCTION__));
	int i;
	iCode *ic;
	bitVect *rsave;
	/* look for call */
	for (ic = lic; ic; ic = ic->next)
		if (ic->op == CALL || ic->op == PCALL)
			break;
	if (!ic)
	{
		fprintf(stderr, "found parameter push with no function call\n");
		return;
	}
	/* if the registers have been saved already or don't need to be then
	 do nothing */
	if (ic->regsSaved)
		return;
	if (IS_SYMOP(IC_LEFT(ic)))
	{
		sym_link *type = OP_SYM_TYPE(IC_LEFT(ic));
		if (IFFUNC_ISNAKED(type) && !IFFUNC_ISBANKEDCALL(type))
			return;
		if (IFFUNC_CALLEESAVES(type))
			return;
	}
	/* save the registers in use at this time but skip the
	 ones for the result */
	rsave = bitVectCplAnd(bitVectCopy(ic->rMask), zr16_rUmaskForOp(IC_RESULT(ic)));
	ic->regsSaved = 1;
	if (options.useXstack)
	{
		bitVect *rsavebits = bitVectIntersect(bitVectCopy(zr16_allBitregs()), rsave);
		int nBits = bitVectnBitsOn(rsavebits);
		int count = bitVectnBitsOn(rsave);
		if (nBits != 0)
		{
			count = count - nBits + 1;
			/* remove all but the first bits as they are pushed all at once */
			rsave = bitVectCplAnd(rsave, rsavebits);
			rsave = bitVectSetBit(rsave, bitVectFirstBit(rsavebits));
		}
		freeBitVect(rsavebits);
		if (count == 1)
		{
			reg_info *reg = REG_WITH_INDEX(bitVectFirstBit(rsave));
			emitpush(REG_WITH_INDEX(R0_IDX)->dname);
			if (reg->type == REG_BIT)
			{
				emitcode("mov", "a,%s", reg->base);
			}
			else
			{
				emitcode("mov", "a,%s", reg->name);
			}
			emitcode("mov", "r0,%s", spname);
			emitcode("inc", "%s", spname); // allocate before use
			emitcode("movx", "@r0,a");
			_G.stack.xpushed++;
			emitpop(REG_WITH_INDEX(R0_IDX)->dname);
		}
		else if (count != 0)
		{
			if ((FUNC_REGBANK(currFunc->type) == 0) && optimize.codeSize)
			{
				char szRegs[32];
				int mask = xstackRegisters(rsave, TRUE, count, szRegs);
				if (BINUSE)
					emitpush("b");
				printf("%d\n", __LINE__);
				emitcode("mov", "a,#0x%02x", count);
				emitcode("mov", "b,#0x%02x", mask & 0xFF);
				if (mask & 0x100)
					emitcode("lcall", "___sdcc_xpush_regs_r0\t;(%s)", szRegs);
				else
					emitcode("lcall", "___sdcc_xpush_regs\t;(%s)", szRegs);
				genLine.lineCurr->isInline = 1;
				if (BINUSE)
					emitpop("b");
				_G.stack.xpushed += count;
			}
			else
			{
				emitpush(REG_WITH_INDEX(R0_IDX)->dname);
				emitcode("mov", "r0,%s", spname);
			//	MOVA("r0");
				emitcode("add", "a,#0x%02x", count);
				emitcode("mov", "%s,a", spname);
				for (i = 0; i < zr16_nRegs; i++)
				{
					if (bitVectBitValue(rsave, i))
					{
						reg_info *reg = REG_WITH_INDEX(i);
						if (i == R0_IDX)
						{
							emitpop("acc");
							emitpush("acc");
						}
						else if (reg->type == REG_BIT)
						{
							emitcode("mov", "a,%s", reg->base);
						}
						else
						{
							emitcode("mov", "a,%s", reg->name);
						}
						emitcode("movx", "@r0,a");
						_G.stack.xpushed++;
						if (--count)
						{
							emitcode("inc", "r0");
						}
					}
				}
				emitpop(REG_WITH_INDEX(R0_IDX)->dname);
			}
		}
	}
	else
	{
		bool bits_pushed = FALSE;
		for (i = 0; i < zr16_nRegs; i++)
		{
			if (bitVectBitValue(rsave, i))
			{
				bits_pushed = pushReg(i, bits_pushed);
			}
		}
	}
	freeBitVect(rsave);
}
/*-----------------------------------------------------------------*/
/* unsaveRegisters - pop the pushed registers                      */
/*-----------------------------------------------------------------*/
static void unsaveRegisters(iCode * ic)
{
	int i;
	bitVect *rsave;
	/* restore the registers in use at this time but skip the
	 ones for the result */
	rsave = bitVectCplAnd(bitVectCopy(ic->rMask), zr16_rUmaskForOp(IC_RESULT(ic)));
	if (options.useXstack)
	{
		bitVect *rsavebits = bitVectIntersect(bitVectCopy(zr16_allBitregs()), rsave);
		int nBits = bitVectnBitsOn(rsavebits);
		int count = bitVectnBitsOn(rsave);
		if (nBits != 0)
		{
			count = count - nBits + 1;
			/* remove all but the first bits as they are popped all at once */
			rsave = bitVectCplAnd(rsave, rsavebits);
			rsave = bitVectSetBit(rsave, bitVectFirstBit(rsavebits));
		}
		freeBitVect(rsavebits);
		if (count == 1)
		{
			reg_info *reg = REG_WITH_INDEX(bitVectFirstBit(rsave));
			emitcode("mov", "r0,%s", spname);
			emitcode("dec", "r0");
			emitcode("movx", "a,@r0");
			_G.stack.xpushed--;
			if (reg->type == REG_BIT)
			{
				emitcode("mov", "%s,a", reg->base);
			}
			else
			{
				emitcode("mov", "%s,a", reg->name);
			}
//emitcode("dec", "%s", spname);
		}
		else if (count != 0)
		{
			if ((FUNC_REGBANK(currFunc->type) == 0) && optimize.codeSize)
			{
				char szRegs[32];
				int mask = xstackRegisters(rsave, FALSE, count, szRegs);
				emitcode("mov", "b,#0x%02x", mask & 0xFF);
				if (mask & 0x100)
					emitcode("lcall", "___sdcc_xpop_regs_r0\t;(%s)", szRegs);
				else
					emitcode("lcall", "___sdcc_xpop_regs\t;(%s)", szRegs);
				genLine.lineCurr->isInline = 1;
				_G.stack.xpushed -= count;
			}
			else
			{
				bool resultInR0 = bitVectBitValue(zr16_rUmaskForOp(IC_RESULT(ic)), R0_IDX);
				if (resultInR0)
				{
					emitpush(REG_WITH_INDEX(R0_IDX)->dname);
				}
				emitcode("mov", "r0,%s", spname);
				for (i = zr16_nRegs; i >= 0; i--)
				{
					if (bitVectBitValue(rsave, i))
					{
						reg_info *reg = REG_WITH_INDEX(i);
						emitcode("dec", "r0");
						emitcode("movx", "a,@r0");
						_G.stack.xpushed--;
						if (i == R0_IDX)
						{
							emitpush("acc");
						}
						else if (reg->type == REG_BIT)
						{
							emitcode("mov", "%s,a", reg->base);
						}
						else
						{
							emitcode("mov", "%s,a", reg->name);
						}
					}
				}
				emitcode("mov", "%s,r0", spname);
				if (bitVectBitValue(rsave, R0_IDX) || resultInR0)
				{
					emitpop(REG_WITH_INDEX(R0_IDX)->dname);
				}
			}
		}
	}
	else
	{
		bool bits_popped = FALSE;
		for (i = zr16_nRegs; i >= 0; i--)
		{
			if (bitVectBitValue(rsave, i))
			{
				bits_popped = popReg(i, bits_popped);
			}
		}
	}
	freeBitVect(rsave);
}
/*-----------------------------------------------------------------*/
/* pushSide -                                                      */
/*-----------------------------------------------------------------*/
static void pushSide(operand * oper, int size, iCode * ic)
{
	D(emitcode ("\n;" , "%s\n", __FUNCTION__));
	int offset = 0;
	int nPushed = _G.r0Pushed + _G.r1Pushed;
	aopOp(oper, ic, FALSE);
	if (nPushed != _G.r0Pushed + _G.r1Pushed)
	{
		while (offset < size)
		{
			const char *l = aopGet(oper, offset, FALSE, TRUE);
			emitcode("mov", "%s,%s", ZR16_fReturn[offset++], l);
		}
		freeAsmop(oper, NULL, ic, TRUE);
		offset = 0;
		while (offset < size)
		{
			emitpush(ZR16_fReturn[offset++]);
		}
		return;
	}
	while (size--)
	{
		const char *l = aopGet(oper, offset++, FALSE, TRUE);
		if (AOP_TYPE (oper) != AOP_REG && AOP_TYPE (oper) != AOP_DIR)
		{
			//MOVA(l);
			emitpush("acc");
		}
		else
		{
			emitpush(l);
		}
	}
	freeAsmop(oper, NULL, ic, TRUE);
}

static bool assignResultValue(operand * oper, operand * func)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode ("\n;", "assignResultValue\n"));


	if (IS_ITEMP(oper) && !EQ (F_OP(oper , 1) , "0x00"))
	{
		//emitcode ("###MOV" , "%s , %s", F_OP(oper , 0), F_OP(oper , 1));
		return;
	}
	
	toR0Str("R8");//  AOP_SIZE (oper) == 1 ? "R9":"R8");
	emitcode("MOV", "%s , R0",F_OP(oper , 0));
	
	if (AOP_SIZE (oper) == 1)
	{
		return;
	}
	
	toR0Str("R9");
	emitcode("MOV", "%s , R0", F_OP(oper , 1));
}
/*-----------------------------------------------------------------*/
/* genXpush - pushes onto the external stack                       */
/*-----------------------------------------------------------------*/
static void genXpush(iCode * ic)
{

}
/*-----------------------------------------------------------------*/
/* genIpush - generate code for pushing this gets a little complex */
/*-----------------------------------------------------------------*/
static void genIpush(iCode * ic)
{
	D(printf("genIpush\n"));
	D(emitcode ("\n;" , "%s\n", __FUNCTION__));
	operand *left;
	aopOp((left = IC_LEFT(ic)), ic, FALSE);
	
// empilha parametros: func. reentrante

	emitcode("MOV", "R0 , %s", F_OP (left , 0));
	emitcode("MOV", "(sp) , R0");
	emitcode("INC", "sp");

	if (AOP_SIZE (left) == 1) return;

	emitcode("MOV", "R0 , %s", F_OP (left , 1));
	emitcode("MOV", "(sp) , R0");
	emitcode("INC", "sp");
}
/*-----------------------------------------------------------------*/
/* genIpop - recover the registers: can happen only for spilling   */
/*-----------------------------------------------------------------*/
static void genIpop(iCode * ic)
{
	int size, offset;
	D(emitcode (";", "genIpop"));
	/* if the temp was not pushed then */
	if (OP_SYMBOL(IC_LEFT(ic))->isspilt)
		return;
	aopOp(IC_LEFT(ic), ic, FALSE);
	size = AOP_SIZE (IC_LEFT (ic));
	offset = size - 1;
	while (size--)
	{
		emitpop(aopGet(IC_LEFT(ic), offset--, FALSE, TRUE));
	}
	freeAsmop(IC_LEFT(ic), NULL, ic, TRUE);
}
/*-----------------------------------------------------------------*/
/* popForBranch - recover the spilt registers for a branch         */
/*-----------------------------------------------------------------*/
static void popForBranch(iCode * ic, bool markGenerated)
{
	while (ic && ic->op == IPOP)
	{
		int pushed = _G.stack.pushed;
		genIpop(ic);
		if (markGenerated)
			ic->generated = 1; /* mark the icode as generated */
		else
			_G.stack.pushed = pushed;
		ic = ic->next;
	}
}
/*-----------------------------------------------------------------*/
/* emitDummyCall - emit a dummy call for --no-ret-without-call     */
/*-----------------------------------------------------------------*/
static void emitDummyCall(void)
{
	symbol *dummyLabel;
	if (!options.no_ret_without_call)
		return;
	dummyLabel = newiTempLabel(NULL);

	emitLabel(dummyLabel);
}
/*-----------------------------------------------------------------*/
/* saveRBank - saves an entire register bank on the stack          */
/*-----------------------------------------------------------------*/
static void saveRBank(int bank, iCode * ic, bool pushPsw)
{
	D(emitcode ("\n;" , "%s" , __FUNCTION__));
	int i;
	int count = 8 + (pushPsw ? 1 : 0);
	asmop *aop = NULL;
	reg_info *r = NULL;
	if (options.useXstack)
	{
		if (!ic)
		{
			/* Assume r0 is available for use. */
			r = REG_WITH_INDEX(R0_IDX);
		}
		else
		{
			aop = newAsmop(0);
			r = getFreePtr(ic, aop, FALSE);
		}

	}
	for (i = 0; i < 8; i++)
	{
		if (options.useXstack)
		{
			_G.stack.xpushed++;
			if (--count)
			{}
		
		}
		else
		{
			char buf[16] = "";
			SNPRINTF(buf, 16, "(%s+%d)", regsZR16[i].base, 8 * bank + regsZR16[i].offset);
			emitpush(buf);
		}
	}
	if (pushPsw)
	{
		if (options.useXstack)
		{
			_G.stack.xpushed++;
		}
		else
		{
		}
	}
	if (aop)
	{
		freeAsmop(NULL, aop, ic, TRUE);
	}
	if (ic)
	{
		ic->bankSaved = 1;
	}
}
/*-----------------------------------------------------------------*/
/* unsaveRBank - restores the register bank from stack             */
/*-----------------------------------------------------------------*/
static void unsaveRBank(int bank, iCode * ic, bool popPsw)
{
	int i;
	asmop *aop = NULL;
	reg_info *r = NULL;
	if (options.useXstack)
	{
		if (!ic)
		{
			/* Assume r0 is available for use. */
			r = REG_WITH_INDEX(R0_IDX);
		}
		else
		{
			aop = newAsmop(0);
			r = getFreePtr(ic, aop, FALSE);
		}
	}
	if (popPsw)
	{
		if (options.useXstack)
		{
			_G.stack.xpushed--;
		}
		else
		{
		}
	}
	for (i = 7; i >= 0; i--)
	{
		if (options.useXstack)
		{
			_G.stack.xpushed--;
		}
		else
		{
			char buf[16] = "";
			SNPRINTF(buf, 16, "(%s+%d)", regsZR16[i].base, 8 * bank + regsZR16[i].offset);
			emitpop(buf);
		}
	}
	if (options.useXstack)
	{
	}
	if (aop)
	{
		freeAsmop(NULL, aop, ic, TRUE);
	}
}
/*-----------------------------------------------------------------*/
/* genSend - gen code for SEND                                     */
/*-----------------------------------------------------------------*/
static void genSend(set * sendSet)
{
	D(printf("genSend\n"));
	D(emitcode("\n;", "genSend\n"));
	
	iCode *sic = setFirstItem(sendSet);

	operand *left;
	aopOp((left = IC_LEFT(sic)), sic, FALSE);

	//metodo para empilhar o primeiro parametro
	

	// se for vetor
	if (isVetWithLiteralIndex(left))
	{	
		char *vName = aopGet (left , 0 , FALSE , FALSE) + 2;
		toR0Str (vName);//toR0 (left , 0);
		emitcode ("MOV" , "R8 , R0");
	}

	else if (IS_OP_LITERAL(left))
	{
		//emitcode("MVS", "%s , %s"AOP_SIZE (left) == 1 ? "R9" : "R8", aopGet(IC_LEFT(sic), 0, FALSE, FALSE));
		emitcode("MVS", "R8 , %s", aopGet(IC_LEFT(sic), 0, FALSE, FALSE));
		if (AOP_SIZE (left) == 2)
			emitcode("MVS", "R9 , %s", aopGet(IC_LEFT(sic), 1, FALSE, FALSE));
	}
	else if (IS_ITEMP(left))
	{
		//emitcode("MOV", "%s , %s", AOP_SIZE (left) == 1 ? "R9" : "R8", aopGet(left, 0, FALSE, FALSE));
		
		emitcode("MOV", "R8 , %s", aopGet(IC_LEFT(sic), 0, FALSE, FALSE));
		if (AOP_SIZE (left) == 2)
			emitcode("MOV", "R9 , %s", aopGet(left, 1, FALSE, FALSE));
	}
	else // parametro nao literal
	{
		emitcode("MOV", "R0 , (%s_L)", aopGet(IC_LEFT(sic), 0, FALSE, FALSE) + 1);
		emitcode("MOV", "%s , R0", AOP_SIZE (left) == 1 ? "R9" : "R8");
		if (AOP_SIZE (left) == 2)
		{
			emitcode("MOV", "R0 , (%s_H)", aopGet(IC_LEFT(sic), 0, FALSE, FALSE) + 1);
			emitcode("MOV", "R9 , R0");
		}
	}
}
/*-----------------------------------------------------------------*/
/* selectRegBank - emit code to select the register bank           */
/*-----------------------------------------------------------------*/
static void selectRegBank(short bank, bool keepFlags)
{

}
/*-----------------------------------------------------------------*/
/* genCall - generates a call statement                            */
/*-----------------------------------------------------------------*/
static void genCall(iCode * ic)
{
	sym_link *dtype;
	sym_link *etype;
	bool swapBanks = FALSE;
	bool accuse = FALSE;
	bool accPushed = FALSE;
	bool resultInF0 = FALSE;
	bool assignResultGenerated = FALSE;
	D(emitcode (";", "genCall"));
	dtype = operandType(IC_LEFT(ic));
	etype = getSpec(dtype);
	/* if send set is not empty then assign */
	if (_G.sendSet)
	{
		if (IFFUNC_ISREENT(dtype))
		{
			/* need to reverse the send set */
			genSend(reverseSet(_G.sendSet));
		}
		else
		{
			genSend(_G.sendSet);
		}
		_G.sendSet = NULL;
	}
	/* if we are calling a not _naked function that is not using
	 the same register bank then we need to save the
	 destination registers on the stack */
	if (currFunc && dtype && !IFFUNC_ISNAKED(dtype) && (FUNC_REGBANK(currFunc->type) != FUNC_REGBANK(dtype))
			&& !IFFUNC_ISISR(dtype))
	{
		swapBanks = TRUE;
	}
	/* if caller saves & we have not saved then */
	if (!ic->regsSaved)
		saveRegisters(ic);
	if (swapBanks)
	{

	}
	/* make the call */
	if (IFFUNC_ISBANKEDCALL(dtype))
	{
		if (IFFUNC_CALLEESAVES(dtype))
		{
			werror(E_BANKED_WITH_CALLEESAVES);
		}
		else
		{
			if (IS_LITERAL(etype))
			{

			}
			else
			{

			}
			emitcode("lcall", "__sdcc_banked_call");
		}
	}
	else
	{
		if (IS_LITERAL(etype))
		{
			emitcode("CALL", "0x%04X", ulFromVal(OP_VALUE(IC_LEFT(ic))));
		}
		else
		{
			emitcode("CALL", "%s",
					(OP_SYMBOL(IC_LEFT(ic))->name[0] ? OP_SYMBOL(IC_LEFT(ic))->name : OP_SYMBOL(IC_LEFT(ic))->name));
		}
	}
	if (swapBanks)
	{
		selectRegBank(FUNC_REGBANK(currFunc->type), IS_BIT(etype));
	}
	/* if we need assign a result value */
	if ((IS_ITEMP(IC_RESULT(ic)) && !IS_BIT(OP_SYM_ETYPE(IC_RESULT(ic)))
			&& (OP_SYMBOL(IC_RESULT(ic))->nRegs || OP_SYMBOL(IC_RESULT(ic))->accuse || OP_SYMBOL(IC_RESULT(ic))->spildir
					|| IS_BIT(etype))) || IS_TRUE_SYMOP(IC_RESULT(ic)))
	{
		_G.accInUse++;
		aopOp(IC_RESULT(ic), ic, FALSE);
		_G.accInUse--;
		accuse = assignResultValue(IC_RESULT(ic), IC_LEFT(ic));
		assignResultGenerated = TRUE;
		freeAsmop(IC_RESULT(ic), NULL, ic, TRUE);
	}
	/* adjust the stack for parameters if required */
	if (ic->parmBytes)
	{
		int i;
		if (ic->parmBytes > 3)
		{
			if (accuse)
			{
				accPushed = TRUE;
			}
			if (IS_BIT(etype) && IS_BIT(OP_SYM_ETYPE(IC_RESULT(ic))) && !assignResultGenerated)
			{
				resultInF0 = TRUE;
			}


			if (options.useXstack)
				_G.stack.xpushed -= ic->parmBytes;
			else
				_G.stack.pushed -= ic->parmBytes;
			/* unsaveRegisters from xstack needs acc, but */
			/* unsaveRegisters from stack needs this popped */
			if (accPushed && !options.useXstack)
			{
				accPushed = FALSE;
			}
		}
		else
		{
//	for (i = 0; i < ic->parmBytes; i++)
//	emitcode("dec", "%s", spname);
			if (options.useXstack)
				_G.stack.xpushed -= ic->parmBytes;
			else
				_G.stack.pushed -= ic->parmBytes;
		}
	}
	/* if we had saved some registers then unsave them */
	if (ic->regsSaved && !IFFUNC_CALLEESAVES(dtype))
	{
		if (accuse && !accPushed && options.useXstack)
		{
			/* xstack needs acc, but doesn't touch normal stack */
			accPushed = TRUE;
		}
		unsaveRegisters(ic);
	}
	if (IS_BIT(OP_SYM_ETYPE(IC_RESULT(ic))) && !assignResultGenerated)
	{
		if (resultInF0)
		{
		}
		aopOp(IC_RESULT(ic), ic, FALSE);
		assignResultValue(IC_RESULT(ic), IC_LEFT(ic));
		freeAsmop(IC_RESULT(ic), NULL, ic, TRUE);
	}
	if (accPushed)
	{}
	if (strstr(OP_SYMBOL(IC_LEFT(ic))->name, "_mulint"))
	{
		genMult(ic);
	}
}
/*-----------------------------------------------------------------*/
/* genPcall - generates a call by pointer statement                */
/*-----------------------------------------------------------------*/
static void genPcall(iCode * ic)
{
	D(printf("%s\n", __FUNCTION__));
	sym_link *dtype;
	sym_link *etype;
	bool swapBanks = FALSE;
	bool resultInF0 = FALSE;
	D(emitcode (";", "genPcall"));
	dtype = operandType(IC_LEFT(ic))->next;
	etype = getSpec(dtype);
	/* if caller saves & we have not saved then */
	if (!ic->regsSaved)
		saveRegisters(ic);
	/* if we are calling a not _naked function that is not using
	 the same register bank then we need to save the
	 destination registers on the stack */
	if (currFunc && dtype && !IFFUNC_ISNAKED(dtype) && (FUNC_REGBANK(currFunc->type) != FUNC_REGBANK(dtype))
			&& !IFFUNC_ISISR(dtype))
	{
		swapBanks = TRUE;
// need caution message to user here
	}
	if (IS_LITERAL(etype))
	{
		/* if send set is not empty then assign */
		if (_G.sendSet)
		{
			genSend(reverseSet(_G.sendSet));
			_G.sendSet = NULL;
		}
		if (swapBanks)
		{
		}
		if (IFFUNC_ISBANKEDCALL(dtype))
		{
			if (IFFUNC_CALLEESAVES(dtype))
			{
				werror(E_BANKED_WITH_CALLEESAVES);
			}
			else
			{
			}
		}
		else
		{
		}
	}
	else
	{
		if (IFFUNC_ISBANKEDCALL(dtype))
		{
			if (IFFUNC_CALLEESAVES(dtype))
			{
				werror(E_BANKED_WITH_CALLEESAVES);
			}
			else
			{
				aopOp(IC_LEFT(ic), ic, FALSE);
				emitpush(aopGet(IC_LEFT(ic), 0, FALSE, TRUE));
				emitpush(aopGet(IC_LEFT(ic), 1, FALSE, TRUE));
				emitpush(aopGet(IC_LEFT(ic), 2, FALSE, TRUE));
				freeAsmop(IC_LEFT(ic), NULL, ic, TRUE);
				/* if send set is not empty then assign */
				if (_G.sendSet)
				{
					genSend(reverseSet(_G.sendSet));
					_G.sendSet = NULL;
				}
				if (swapBanks)
				{
		
				}
				else
				{
				}
				/* make the call */
				emitcode("lcall", "__sdcc_banked_call");
			}
		}
		else if (_G.sendSet) /* the send set is not empty */
		{
			symbol *callLabel = newiTempLabel(NULL);
			symbol *returnLabel = newiTempLabel(NULL);
			_G.stack.pushed += 2;
			emitDummyCall();
			/* now push the function address */
			pushSide(IC_LEFT(ic), FPTRSIZE, ic);
			/* send set is not empty: assign */
			genSend(reverseSet(_G.sendSet));
			_G.sendSet = NULL;
			if (swapBanks)
			{
			}
			/* make the call */
			emitcode("ret", "");
			_G.stack.pushed -= 4;
			emitLabel(returnLabel);
		}
		else /* the send set is empty */
		{
			/* now get the called address into dptr */
			aopOp(IC_LEFT(ic), ic, FALSE);
			if (AOP_TYPE (IC_LEFT (ic)) == AOP_DPTR)
			{
			}
			else
			{
			}
			freeAsmop(IC_LEFT(ic), NULL, ic, TRUE);
			if (swapBanks)
			{
			}
		}
	}
	if (swapBanks)
	{
		selectRegBank(FUNC_REGBANK(currFunc->type), IS_BIT(etype));
	}
	/* if we need assign a result value */
	if ((IS_ITEMP(IC_RESULT(ic)) && !IS_BIT(OP_SYM_ETYPE(IC_RESULT(ic)))
			&& (OP_SYMBOL(IC_RESULT(ic))->nRegs || OP_SYMBOL(IC_RESULT(ic))->spildir)) || IS_TRUE_SYMOP(IC_RESULT(ic)))
	{
		_G.accInUse++;
		aopOp(IC_RESULT(ic), ic, FALSE);
		_G.accInUse--;
		assignResultValue(IC_RESULT(ic), IC_LEFT(ic));
		freeAsmop(IC_RESULT(ic), NULL, ic, TRUE);
	}
	/* adjust the stack for parameters if required */
	if (ic->parmBytes)
	{
		int i;
		if (ic->parmBytes > 3)
		{
			if (IS_BIT(OP_SYM_ETYPE(IC_LEFT(ic))) && IS_BIT(OP_SYM_ETYPE(IC_RESULT(ic))))
			{
				resultInF0 = TRUE;
			}

			if (options.useXstack)
				_G.stack.xpushed -= ic->parmBytes;
			else
				_G.stack.pushed -= ic->parmBytes;
		}
		else
		{
			for (i = 0; i < ic->parmBytes; i++)
			{}
			if (options.useXstack)
				_G.stack.xpushed -= ic->parmBytes;
			else
				_G.stack.pushed -= ic->parmBytes;
		}
	}
	/* if we had saved some registers then unsave them */
	if (ic->regsSaved && !IFFUNC_CALLEESAVES(dtype))
		unsaveRegisters(ic);
	if (IS_BIT(OP_SYM_ETYPE(IC_RESULT(ic))))
	{
		if (resultInF0)
		{
		}
		aopOp(IC_RESULT(ic), ic, FALSE);
		assignResultValue(IC_RESULT(ic), IC_LEFT(ic));
		freeAsmop(IC_RESULT(ic), NULL, ic, TRUE);
	}
}
/*-----------------------------------------------------------------*/
/* resultRemat - result  is rematerializable                       */
/*-----------------------------------------------------------------*/
static int resultRemat(iCode * ic)
{
	if (SKIP_IC(ic) || ic->op == IFX)
		return 0;
	if (IC_RESULT(ic) && IS_ITEMP(IC_RESULT(ic)))
	{
		symbol *sym = OP_SYMBOL(IC_RESULT(ic));
		if (sym->remat && !POINTER_SET(ic))
			return 1;
	}
	return 0;
}
/*-----------------------------------------------------------------*/
/* inExcludeList - return 1 if the string is in exclude Reg list   */
/*-----------------------------------------------------------------*/
static int regsCmp(void *p1, void *p2)
{
	return (STRCASECMP((char *) p1, (char *) (p2)) == 0);
}
static bool inExcludeList(char *s)
{
	const char *p = setFirstItem(options.excludeRegsSet);
	if (p == NULL || STRCASECMP(p, "none") == 0)
		return FALSE;
	return isinSetWith(options.excludeRegsSet, s, regsCmp);
}
/*-----------------------------------------------------------------*/
/* genFunction - generated code for function entry                 */
/*-----------------------------------------------------------------*/
static void genFunction(iCode * ic)
{

	D(printf ("%s\n", __FUNCTION__));

	if (options.stackAuto)
   	{}

  	if (options.useXstack) //--xstack
	{}

	symbol *sym = OP_SYMBOL(IC_LEFT(ic));
	
	if (IFFUNC_ISREENT(sym->type))
	{
		emitcode("", "%s:MOV %s , sp\n", sym->name, tempRegs[tempRegsId]);
		if (++tempRegsId == 6)
		{
			tempRegsId = 1;
		}
	}
	else if (!strcmp(sym->name, "main"))
	{
		emitcode("", "%s: MVS sp , 200\n", sym->name);
		

	}
	else
	{
		emitcode("", "%s:", sym->name);
	}
	sym_link *ftype;
	bool switchedPSW = FALSE;
	int calleesaves_saved_register = -1;
	int stackAdjust = sym->stack;
	int accIsFree = sym->recvSize < 4;
	char *freereg = NULL;
	iCode *ric = (ic->next && ic->next->op == RECEIVE) ? ic->next : NULL;
	genLine.lineCurr->isLabel = 1;
	ftype = operandType(IC_LEFT(ic));
	_G.currentFunc = sym;
	_G.stack.param_offset = 0;
	_G.stack.offset = sym->stack;
	_G.stack.xoffset = sym->xstack;
	wassertl(_G.stack.pushed == 0, "stack over/underflow");
	wassertl(_G.stack.xpushed == 0, "xstack over/underflow");

	// se for uma isr, salva registradores.
	if (IFFUNC_ISISR(sym->type))
	{
		ISRWasGenerated = true;
		strcpy (ISRname , sym->name);
		int i;
		for (i = 0; i < zr16_nRegs; i++)
		{
			if (regsZR16[i].rIdx != R0_IDX && regsZR16[i].rIdx != R13_IDX && 
			    regsZR16[i].rIdx != R14_IDX && regsZR16[i].rIdx != CND_IDX) // cnd_idx = id do R15	
			{
				if (bitVectBitValue(sym->regsUsed, i)) // empilha reg. so se estiver sendo usado (se foi alocado)
				{
					emitpush(regsZR16[i].name);
				}
			}
		}
	}
	else
	{
		
	}


	_G.stack.param_offset = options.useXstack ? _G.stack.xpushed : _G.stack.pushed;
	_G.stack.pushedregs = _G.stack.pushed;
	_G.stack.xpushedregs = _G.stack.xpushed;
	_G.stack.pushed = 0;
	_G.stack.xpushed = 0;
	/* if critical function then turn interrupts off */
	if (IFFUNC_ISCRITICAL(ftype))
	{
		
	}
}
/*-----------------------------------------------------------------*/
/* genEndFunction - generates epilogue for functions               */
/*-----------------------------------------------------------------*/
static void genEndFunction(iCode * ic)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode("\n;" , "%s\n", __FUNCTION__));

	symbol *sym = OP_SYMBOL(IC_LEFT(ic));

	lineNode *lineBodyEnd = genLine.lineCurr;
	lineNode *linePrologueStart = NULL;
	lineNode *lnp;
	bitVect *regsUsed;
	bitVect *regsUnneeded;
	int idx;
	_G.currentFunc = NULL;

	if (IFFUNC_ISCRITICAL(sym->type))
	{

	}
	_G.stack.xpushed = _G.stack.xpushedregs;
	_G.stack.pushed = _G.stack.pushedregs;


		// se for uma isr, recupera registradores.

	if (IFFUNC_ISISR(sym->type))
	{
		int i;
	
		for (i =  zr16_nRegs-1; i > -1; i--)
		{
			if (regsZR16[i].rIdx != R0_IDX && regsZR16[i].rIdx != R13_IDX && 
			    regsZR16[i].rIdx != R14_IDX && regsZR16[i].rIdx != CND_IDX) // cnd_idx = id do R15	
			{
				if (bitVectBitValue(sym->regsUsed, i)) 
				{
					emitpop(regsZR16[i].name);
				}
			}
		}
	}

	emitcode("", "%s", IFFUNC_ISISR(sym->type) ? "RETS" : "RET");
}
/*-----------------------------------------------------------------*/
/* genRet - generate code for return statement                     */
/*-----------------------------------------------------------------*/
static void genRet(iCode * ic)
{
	D(printf ("%s\n",__FUNCTION__));
	D(emitcode("\n;", "genRet\n"));

	operand *left;
	aopOp((left = IC_LEFT(ic)), ic, FALSE);

	if (!left)	// return;
	{
		emitcode ("RET" , "");
		return;
	}

	char *le = Safe_strdup(aopGet(left, 0, FALSE, FALSE));

	if (*le == '@')
	{
		emitcode("MOV", "R0 , (sp)");
		emitcode("MOV", "R8 , R0");
		emitcode("INC", "sp");
		emitcode("MOV", "R0 , (sp)");
		emitcode("MOV", "R9 , R0");
		emitcode("RET", "");
	}
	
	else if (AOP_TYPE (left) == AOP_LIT)
	{
		emitcode("MVS", "R8 , %s", le);
		emitcode("MVS", "R9 , %s", aopGet(IC_LEFT(ic), 1, FALSE, FALSE));
		emitcode("RET", "");
	}
	else if (IS_PARM(left))
	{
		emitcode("MOV", "R0 , (%s_L)", le);
		emitcode("MOV", "R8 , R0");
		emitcode("MOV", "R0 , (%s_H)", le);
		emitcode("MOV", "R9 , R0");
		emitcode("RET", "");
	}
	
	else if (IS_OP_GLOBAL(left))
	{
		emitcode("MOV", "R0 , (%s_L)", aopGet(left, 0, FALSE, FALSE) + 1);
		emitcode("MOV", "R8 , R0");
		emitcode("MOV", "R0 , (%s_H)", aopGet(left, 0, FALSE, FALSE) + 1);
		emitcode("MOV", "R9 , R0");
		emitcode("RET", "");
	}

	else if (IS_ITEMP (left))
	{
		emitcode ("MOV" , "R8 , %s", aopGet(left, 0, FALSE, FALSE));

		if (!EQ (aopGet(left, 1, FALSE, FALSE) , "0x00"))
			emitcode ("MOV" , "R9 , %s", aopGet(left, 1, FALSE, FALSE));

		else
			emitcode ("MVS" , "R9 , 0x00"); 
		emitcode("RET", "");
	}

}
/*-----------------------------------------------------------------*/
/* genLabel - generates a label                                    */
/*-----------------------------------------------------------------*/
static void genLabel(iCode * ic)
{
	D(emitcode ("\n;",  "%s\n", __FUNCTION__));
	D(printf("%s\n", __FUNCTION__))

	/*
		Caso algum label tenha sido gerado, deve-se forçar o prox. valor a ser inserido em r0.


		Para relembrar:

		void main ()
		{
			for (i = 0 ; i < M ; i++)
			for (j = 0 ; j < N ; j++)
			A[i][j] = 0x22;
		}
		

		main:   MOV	R0 , 0x00
			   MOV	(i_L) , R0
		L00105: MOV	R0 , 0x00  ; Reseta j para zero quando houver um jmp L00105.
			  MOV	(j_L) , R0


	*/
	strcpy (lastValueInR0 , "\0");
	
	/* special case never generate */
	if (IC_LABEL(ic) == entryLabel)
		return;
	emitLabel(IC_LABEL(ic));
}


static void genGoto(iCode * ic)
{
	D(emitcode (";\n",  "%s\n", __FUNCTION__));
	emitcode("JMP", "!tlabel", labelKey2num(IC_LABEL(ic)->key));
}


static void genIncr(iCode * ic)
{
	aopOp(IC_RESULT(ic), ic, TRUE);
	operand *result = IC_RESULT(ic);
	D(emitcode("\n;", "%s\n", __FUNCTION__));
	if (AOP_SIZE (result) == 2)
	{
		toR0Str("0x04");
		emitcode("OR", "R15 , R0");
		toR0Str("0xBF");
		emitcode("AND", "R15 , R0");
		toR0Str("0x01");
		emitcode("ADD", "%s , R0", F_OP(result, 0));
		toR0Str("0xBB");
		emitcode("AND", "R15 , R0");
	}
	else
	{
		if (SPEC_USIGN(operandType(result)))
		{
			emitcode("INC", "%s", F_OP(result, 0));
		}
		
		else
		{
			// comp. original gera ADD 0x01, so pus inc.
			//toR0Str ("0x01");
			//emitcode ("ADD" , "%s , R0" , F_OP(result , 0));
			emitcode("INC", "%s", F_OP(result, 0));
		}
	}
}
/*-----------------------------------------------------------------*/
/* outBitAcc - output a bit in acc                                 */
/*-----------------------------------------------------------------*/
static void outBitAcc(operand * result)
{
}


bool isVetWithLiteralIndex(operand *op)
{
	char *str = aopGet(op, 0, FALSE, FALSE);
	return IS_ITEMP(op) && (*str == '#' || *str == '(' || *str == '_');
}

void assignVectorWithNonLiteralIndex(operand *result, operand *left, operand *right)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode("\n;", "%s\n", __FUNCTION__));
	
	char *res = Safe_strdup(aopGet(result, 0, FALSE, FALSE));
	char *ri = Safe_strdup(aopGet(right, 0, FALSE, FALSE));
	char *le = Safe_strdup(aopGet(left, 0, FALSE, FALSE) + 2);
	
	if (!strncmp(le, "IO", 2)) // corrigir
	{
		replace(ri, "_", "");
		if (!strcmp(res, "R0"))
		{
			emitcode("MOV", "R0 , (%s_L)", ri);
			emitcode("MOV", "R1 , R0");
		}
		else
		{
			//emitcode ("MOV" , "R0 , (%s_L)",ri);
			//emitcode ("MOV" ,  "R1 , R0");
			emitcode("MOV", "IO R0 , (%s_L)", ri);
		}
	}
	
	else
	{
		if (!IS_ITEMP(right))
		{
			replace(ri, "_", "");
			emitcode("MOV", "R0 , (%s_L)", ri);
		}

		else
		{
			emitcode ("MOV" , "R0 , %s", ri);
		}
		emitcode("ADD", "R0 , %s", le);
		emitcode("MOV", "%s , R0", res);
	}
}

/*-----------------------------------------------------------------*/
/* genPlus - generates code for addition                           */
/*-----------------------------------------------------------------*/
static void genPlus(iCode * ic)
{
	D(printf ("%s\n",__FUNCTION__));
	
	aopOp(IC_LEFT(ic), ic, FALSE);
	aopOp(IC_RIGHT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	
	operand *left = IC_LEFT(ic);
	operand *right = IC_RIGHT(ic);
	operand *result = IC_RESULT(ic);
	
	char *res = Safe_strdup(aopGet(result, 0, FALSE, FALSE));
	char *ri = Safe_strdup(aopGet(right, 0, FALSE, FALSE));
	char *le = Safe_strdup(aopGet(left, 0, FALSE, FALSE) + 2);
	
	if (isVetWithLiteralIndex(left) && IS_ITEMP(result))
	{
		if (!strncmp(le, "IO", 2))
		{
			result->isPtr = 1;
		}
		else
			result->isPtr = 0;
		
		assignVectorWithNonLiteralIndex(result, left, right);
		return;
	}
	
	if (operandsEqu(left, result))
	{
		if (AOP_SIZE (right) == 1)
		{
			if (EQ (aopGet (right , 0 , FALSE , FALSE) , "0x01"))
			{
				genIncr(ic);
				return;
			}
		}
		if (AOP_SIZE (right) == 2)
		{
			if (EQ (aopGet (right , 0 , FALSE , FALSE) , "0x01"))
			{
				if (!strcmp(aopGet(right, 1, FALSE, FALSE), "0x00"))
				{
					genIncr(ic);
					return;
				}
			}
		}
	}
	
	if (AOP_SIZE (result) == 2)
	{
		toR0Str("0x04");
		emitcode("OR", "R15 , R0");
		toR0Str("0xBF");
		emitcode("AND", "R15 , R0");
	}
	genBitwiseOperation(ic, "ADD");
	
	if (AOP_SIZE (result) == 2)
	{
		toR0Str("0xBB");
		emitcode("AND", "R15 , R0");
	}
}

/*-----------------------------------------------------------------*/
/* genDecr :- does subtraction with decrement if possible      */
/*-----------------------------------------------------------------*/
static void genDecr(iCode * ic)
{
	D(emitcode("\n;" , "%s\n",__FUNCTION__));
	aopOp(IC_RESULT(ic), ic, TRUE);
	operand *result = IC_RESULT(ic);
	
	if (AOP_SIZE (result) == 1)
	{
		if (SPEC_USIGN(operandType(result)))
		{
			emitcode("DEC", "%s", F_OP(result, 0));
		}
		else
		{
			toR0Str("0xFF");
			emitcode("ADD", "%s , R0", F_OP(result, 0));
		}
	}
	else
	{
		toR0Str("0x04");
		emitcode("OR", "R15 , R0");
		toR0Str("0xBF");
		emitcode("AND", "R15 , R0");
		
		if (SPEC_USIGN(operandType(result)))
		{
			toR0Str("0x01");
			emitcode("SUB", "%s , R0", F_OP(result, 0));
		}
		else
		{
			toR0Str("0xFF");
			emitcode("ADD", "%s , R0", F_OP(result, 0));
			emitcode("ADD", "%s , R0", F_OP(result, 1));
		}
		toR0Str("0xBB");
		emitcode("AND", "R15 , R0");
	}
}


/*-----------------------------------------------------------------*/
/* genMinus - generates code for subtraction                       */
/*-----------------------------------------------------------------*/
static void genMinus(iCode * ic)
{
	D(emitcode ("\n;" , "%s\n", __FUNCTION__));
	aopOp(IC_LEFT(ic), ic, FALSE);
	aopOp(IC_RIGHT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	
	operand *left = IC_LEFT(ic);
	operand *right = IC_RIGHT(ic);
	operand *result = IC_RESULT(ic);


	if (!IS_ITEMP (result) && AOP_SIZE (result) == 1 && IS_ITEMP (left) && AOP_SIZE (right) == 1 && 
		!strcmp (aopGet (right , 0 , FALSE , FALSE) , "0x01"))
	{
		emitcode ("DEC" , "%s", aopGet (left , 0 , FALSE , FALSE));
		toR0 (left , 0);
		emitcode ("MOV" , "%s , R0", F_OP (result , 0));

		return;
	}


	if (IS_ITEMP (result))
	{
		emitcode ("DEC" , "%s", aopGet (result , 0 , FALSE , FALSE));
		return;
	}

	if (operandsEqu(left, result))
	{
		if (AOP_SIZE (right) == 1)
		{
			if (EQ (aopGet (right , 0 , FALSE , FALSE) , "0x01"))
			{
				genDecr(ic);
				return;
			}
		}
		if (AOP_SIZE (right) == 2)
		{
			if (EQ (aopGet (right , 0 , FALSE , FALSE) , "0x01"))
			{
				if (EQ (aopGet (right , 1 , FALSE , FALSE) , "0x00"))
				{
					genDecr(ic);
					return;
				}
			}
		}
	}
	
	if (AOP_SIZE (result) == 1)
	{
		if (SPEC_USIGN(operandType(left)) && SPEC_USIGN(operandType(right)))
		{
			toR0(left, 0);
			emitcode("SUB", "R0 , %s", F_OP(right, 0));
			emitcode("MOV", "%s , R0", F_OP(result, 0));
		}
		else
		{
			toR0(right, 0);
			emitcode("XOR", "R0 , 0xFF");
			emitcode("ADD", "R0 , 0x01");
			emitcode("ADD", "R0 , %s", F_OP(left, 0));
			emitcode("MOV", "%s , R0", F_OP(result, 0));
		}
		
		return;
	}
	
	toR0Str("0x04");
	emitcode("OR", "R15 , R0");
	toR0Str("0xBF");
	emitcode("AND", "R15 , R0");
	
	if (SPEC_USIGN(operandType(left)) && SPEC_USIGN(operandType(right)))
	{
		genBitwiseOperation(ic, "SUB");
	}
	
	else
	{
		toR0(right, 0);
		emitcode("XOR", "R0 , 0xFF");
		emitcode("ADD", "R0 , 0x01");
		emitcode("ADD", "R0 , %s", F_OP(left, 0));
		emitcode("MOV", "%s , R0", F_OP(result, 0));
		
		toR0(right, 1);
		emitcode("XOR", "R0 , 0xFF");
		//emitcode ("ADD" , "R0 , 0x00");
		emitcode("ADD", "R0 , %s", F_OP(left, 1));
		emitcode("MOV", "%s , R0", F_OP(result, 1));
	}
	
	toR0Str("0xBB");
	emitcode("AND", "R15 , R0");
}

static void genZr16Mult()
{

	emitcode("\n\nmul8: MVS", " R12 , 0");
	emitcode("MVS", "R11 , 0");
	emitcode("MVS", "R10 , 0");
	emitcode("MOV", "R0 , 0b11111001");
	emitcode("AND", "R15 , R0");
	emitcode("MVS", "R7 , 8");
	emitcode("mul8_00: JZ", "fim_mul8");
	emitcode("MVS", "R0 , 0b00000001");
	emitcode("AND", "R0 , R1");
	emitcode("JZ", "mul8_05");
	emitcode("ADD", "R11 , R2");
	emitcode("MVS", "R0 , 0b00000100");
	emitcode("XOR", "R15 , R0");
	emitcode("ADD", "R12 , R10");
	emitcode("XOR", "R15 , R0");
	emitcode("mul8_05: SHL", "R1 , R1");
	emitcode("MVS", "R0 , 0b00000010");
	emitcode("XOR", "R15 , R0");
	emitcode("SHL", "R2 , R2");
	emitcode("MOV", "R0 , 0b00000100");
	emitcode("XOR", "R15 , R0");
	emitcode("ROT", "R10 , R10");
	emitcode("MOV", "R0 , 0b00000110");
	emitcode("XOR", "R15 , R0");
	emitcode("DEC", "R7");
	emitcode("JMP", "mul8_00");
	emitcode("fim_mul8:", "MOV R0 , R11");
	emitcode("RET", "\n\n");
}

static void genZr16Div()
{
	emitcode("\n\ndiv: MOV", "R0 , R1");
	emitcode("JNZ", "div_05");
	emitcode("RET", "");
	emitcode("div_05:", "MVS R6 , 0");
	emitcode("MVS", "R5 , 0");
	emitcode("MVS", "R4 , 0");
	emitcode("MVS", "R3 , 0");
	emitcode("MVS", "R11 , 0");
	emitcode("MVS", "R2 , 16");
	emitcode("MOV", "R0 , 0b11111001");
	emitcode("AND", "R15 , R0");
	emitcode("div_07: ", "MVS R0 , 0b00000100");
	emitcode("XOR", "R15 , R0");
	emitcode("ROT", "R1 , R1 ");
	emitcode("ROT", "R6 , R6 ");
	emitcode("ROT", "R5 , R5");
	emitcode("XOR", "R15 , R0");
	emitcode("CMP", "R12 , R5");
	emitcode("XOR", "R15 , R0");
	emitcode("CMP", "R10 , R6");
	emitcode("CMP", "R11 , R1");
	emitcode("JC", "div_10");
	emitcode("XOR", "R15 , R0");
	emitcode("SUB", "R12 , R5");
	emitcode("XOR", "R15 , R0");
	emitcode("SUB", "R10 , R6");
	emitcode("SUB", "R11 , R1");
	emitcode("MOV", "R0 , 0b01000000");
	emitcode("OR", "R15 , R0");
	emitcode("JMP", "div_15");
	emitcode("div_10:", "MOV R0 , 0b10111111");
	emitcode("AND", "R15 , R0");
	emitcode("div_15:", "MOV R0 , 0b00000010");
	emitcode("XOR", "R15 , R0");
	emitcode("ROT", "R3 , R3");
	emitcode("ROT", "R4 , R4");
	emitcode("MOV ", "R0 , 0b00000110");
	emitcode("XOR", "R15 , R0");
	emitcode("DEC", "R2");
	emitcode("JNZ", "div_07");
	emitcode("MOV", "R0 , R3");
	emitcode("RET", "\n\n");
}

/*-----------------------------------------------------------------*/
/* genMult - generates code for multiplication                     */
/*-----------------------------------------------------------------*/
static void genMult(iCode * ic)
{
	D(printf("genMult\n"));
	
	operand *left = IC_LEFT(ic);
	operand *right = IC_RIGHT(ic);
	operand *result = IC_RESULT(ic);
	aopOp(result, ic, TRUE);
	aopOp(left, ic, FALSE);
	aopOp(right, ic, FALSE);
	
	char *res_H = F_OP(result, 1);
	char *res_L = F_OP(result, 0);
	char *ri = F_OP(right, 0);
	char *le = F_OP(left, 0);
	

	// Empilha regs. alterados no alg. de multiplicação
	symbol *sym1 = OP_SYMBOL(IC_LEFT(ic));
	symbol *sym2 = OP_SYMBOL(IC_RIGHT(ic));
	int i;
	for (i = 0; i < zr16_nRegs; i++)
	{
		if (regsZR16[i].rIdx != R0_IDX && regsZR16[i].rIdx != R13_IDX && 
			    regsZR16[i].rIdx != R14_IDX && regsZR16[i].rIdx != CND_IDX) // cnd_idx = id do R15	
		{
			if (bitVectBitValue(sym1->regsUsed, i)||bitVectBitValue(sym2->regsUsed, i)) // empilha reg. so se estiver sendo usado (se foi alocado)
			{
				emitpush(regsZR16[i].name);
			}
		}
	}


	emitcode("MOV", "R0 , %s", le);
	emitcode("MOV", "R1 , R0");
	emitcode("MOV", "R0 , %s", ri);
	emitcode("MOV", "R2 , R0");
	emitcode("CALL", "mul8");
	
	if (!mulWasGenerated)
	{
		mulWasGenerated = true;
	}
	emitcode("MOV", "%s , R0", res_L);
	
	
	if (AOP_SIZE (result) == 2)
	{
		emitcode("MOV", "R0 , R12");
		emitcode("MOV", "%s , R0", res_H);
	}


	// Restaura regs.
	for (i = 0; i < zr16_nRegs; i++)
	{
		if (regsZR16[i].rIdx != R0_IDX && regsZR16[i].rIdx != R13_IDX && 
			    regsZR16[i].rIdx != R14_IDX && regsZR16[i].rIdx != CND_IDX) // cnd_idx = id do R15	
		{
			if (bitVectBitValue(sym1->regsUsed, i)||bitVectBitValue(sym2->regsUsed, i)) // empilha reg. so se estiver sendo usado (se foi alocado)
			{
				emitpop(regsZR16[i].name);
			}
		}
	}
}

/*-----------------------------------------------------------------*/
/* genDiv - generates code for division                            */
/*-----------------------------------------------------------------*/
static void genDiv(iCode * ic)
{
	operand *left = IC_LEFT(ic);
	operand *right = IC_RIGHT(ic);
	operand *result = IC_RESULT(ic);
	
	aopOp(left, ic, FALSE);
	aopOp(right, ic, FALSE);
	aopOp(result, ic, TRUE);
	
	char *res_H = F_OP(result, 1);
	char *res_L = F_OP(result, 0);
	char *ri = F_OP(right, 0);
	char *le = F_OP(left, 0);
	 
	// Empilha regs. alterados no alg. de divisão
	symbol *sym1 = OP_SYMBOL(IC_LEFT(ic));
	symbol *sym2 = OP_SYMBOL(IC_RIGHT(ic));
	int i;
	for (i = 0; i < zr16_nRegs; i++)
	{
		if (regsZR16[i].rIdx != R0_IDX && regsZR16[i].rIdx != R13_IDX && 
			    regsZR16[i].rIdx != R14_IDX && regsZR16[i].rIdx != CND_IDX) // cnd_idx = id do R15	
		{
			if (bitVectBitValue(sym1->regsUsed, i)||bitVectBitValue(sym2->regsUsed, i)) // empilha reg. so se estiver sendo usado (se foi alocado)
			{
				emitpush(regsZR16[i].name);
			}
		}
	}


	if (EQ (ri ,"0x02")) // Otimiza divisao por 2
	{
		emitcode("MOV", "R0 , 0b11111101");
		emitcode("AND", "R15 , R0");
		emitcode("MOV", "R0 , %s", F_OP(left, 0));
		emitcode("SHL", "R0 , R0");	
		emitcode("MOV", "%s , R0", F_OP(result, 0));
		return;
	}

	if (!divWasGenerated)
	{
		divWasGenerated = true;
	}
	
	/*

	 Divisao por 1 ja vem otimizada pelo sdcc.

	 So funciona para:
	 char = char/char
	 int = char/char
	 */

	emitcode("MOV", "R0 , %s", le);
	emitcode("MOV", "R12 , R0");
	emitcode("MOV", "R0 , %s", ri);
	emitcode("MOV", "R1 , R0");
	emitcode("CALL", "div");
	emitcode("MOV", "%s , R0", res_L);

// Restaura regs.
	for (i = 0; i < zr16_nRegs; i++)
	{
		if (regsZR16[i].rIdx != R0_IDX && regsZR16[i].rIdx != R13_IDX && 
			    regsZR16[i].rIdx != R14_IDX && regsZR16[i].rIdx != CND_IDX) // cnd_idx = id do R15	
		{
			if (bitVectBitValue(sym1->regsUsed, i)||bitVectBitValue(sym2->regsUsed, i)) // empilha reg. so se estiver sendo usado (se foi alocado)
			{
				emitpop(regsZR16[i].name);
			}
		}
	}
}


/*-----------------------------------------------------------------*/
/* genMod - generates code for division                            */
/*-----------------------------------------------------------------*/
static void genMod(iCode * ic)
{
	D(printf("%s\n" , __FUNCTION__));
}
/*-----------------------------------------------------------------*/
/* genIfxJump :- will create a jump depending on the ifx           */
/*-----------------------------------------------------------------*/
static void genIfxJump(iCode * ic, const char *jval, operand * left, operand * right, operand * result, iCode * popIc)
{
	 symbol *jlbl;
	 symbol *tlbl = newiTempLabel (NULL);
	 char *inst;


	D(printf("genIfxJump\n"));
	D(emitcode ("\n;" , "%s\n", __FUNCTION__));
	//symbol *jlbl;
	//symbol *tlbl = newiTempLabel(NULL);
	//char *inst;
	/* if there is something to be popped then do it first */
	popForBranch(popIc, TRUE);

	/* if true label then we jump if condition
	 supplied is true */
	if (IC_TRUE(ic))
	{
		jlbl = IC_TRUE(ic);
		inst = "JZ";
	}
	else
	{
		/* false label is present */
		jlbl = IC_FALSE(ic);
		inst = "JNZ";
	}

	emitcode(inst, "!tlabel", labelKey2num(tlbl->key));
	freeForBranchAsmops(result, right, left, ic);
	emitcode("JMP", "!tlabel", labelKey2num(jlbl->key));
	emitLabel(tlbl);

	if (ic-> next->op == LABEL)
	emitcode ("JMP" , "$+1");		// evita a emição de labels em sequencia: ex: LBL_1:LBL_2	
	/* mark the icode as generated */
	ic->generated = 1;
}


static void newGenCmpLt(operand *, operand *, operand *);

/*-----------------------------------------------------------------*/
/* genCmpGt :- greater than comparison                             */
/*-----------------------------------------------------------------*/
static void genCmpGt(iCode * ic, iCode * ifx)
{
	D(printf("%s\n", __FUNCTION__));
	
	operand *left, *right, *result;
	sym_link *letype, *retype;
	int sign = 0;
	left = IC_LEFT(ic);
	right = IC_RIGHT(ic);
	result = IC_RESULT(ic);
	aopOp(result, ic, TRUE);
	aopOp(left, ic, FALSE);
	aopOp(right, ic, FALSE);
	newGenCmpLt(result, right, left);
}

static void genCmpLtZero(operand *result, operand *left)
{
	D(emitcode ("\n;" , "%s\n", __FUNCTION__));
	char *reg_res = Safe_strdup(aopGet(result, 0, FALSE, FALSE));
	symbol *emitLblExit = newiTempLabel(NULL);
	int lblExit = labelKey2num(emitLblExit->key);
	
	if(!EQ (reg_res , "0x00"))
		emitcode("MVS", "%s , 0x01", (left->isPtr || !IS_ITEMP(result)) ? "R2" : aopGet(result, 0, FALSE, FALSE));
	//emitcode ("MVS" , "R2 , 0x01");
	
	if (left->isPtr && AOP_SIZE (left) == 2) // inc ptr. pra pegar a parte alta, que contem o sinal.
	{
		emitcode("INC", aopGet(left, 0, FALSE, FALSE));
	}
	toR0(left, (left->isPtr) || (AOP_SIZE (left) == 1) ? 0 : 1);
	
	emitcode("AND", "R0 , 0x80");
	emitcode("CMP", "R0 , 0x80");
	emitcode("JZ", "!tlabel", lblExit);
	
	emitcode("MVS", "%s , 0x00", (left->isPtr || !IS_ITEMP(result)||EQ(reg_res,"0x00")) ? "R2" : aopGet(result, 0, FALSE, FALSE));

	emitLabel(emitLblExit);
	
	if(!EQ (reg_res , "0x00"))
	{
		if (!IS_ITEMP(result)) // char = int1 < int 2	nao gera cast, ajusta o resultado aqui
		{
			emitcode("MOV", "R0 , R2");
			emitcode("MOV", "%s , R0", F_OP(result, 0));
		}
		else
		{
			// poe res em r0, o valor eh do resultado eh ajustado em genCast
			emitcode("MOV", "R0 , %s", left->isPtr ? "R2" : aopGet(result, 0, FALSE, FALSE));
		}
	}
}

static void genCmpGtZero(operand *result, operand *left)
{
	D(emitcode (";\n", "%s\n", __FUNCTION__));
	char *reg_res = Safe_strdup(aopGet(result, 0, FALSE, FALSE));
	symbol *emitLblExit = newiTempLabel(NULL);
	int lblExit = labelKey2num(emitLblExit->key);
	
	if(!EQ (reg_res , "0x00"))
		emitcode("MVS", "%s , 0x00", (left->isPtr || !IS_ITEMP(result)) ? "R2" : aopGet(result, 0, FALSE, FALSE));
	
	if (left->isPtr)
	{
		emitcode("INC", aopGet(left, 0, FALSE, FALSE));
	}
	toR0(left, (left->isPtr) || (AOP_SIZE (left) == 1) ? 0 : 1);
	if (left->isPtr)
	{
		emitcode("DEC", aopGet(left, 0, FALSE, FALSE));
	}
	// verifica se valor eh zero.
	if (AOP_SIZE (left) == 1)
	{
		emitcode("JZ", "!tlabel", lblExit);
	}
	
	else
	{
		emitcode("OR", "R0 , %s", F_OP(left, 0));
		emitcode("JZ", "!tlabel", lblExit);
	}
	
	emitcode("AND", "R0 , 0x80");
	emitcode("CMP", "R0 , 0");
	emitcode("JNZ", "!tlabel", lblExit);
	
	emitcode("MVS", "%s , 0x01", (left->isPtr || !IS_ITEMP(result)||EQ(reg_res,"0x00")) ? "R2" : aopGet(result, 0, FALSE, FALSE));
	emitLabel(emitLblExit);
	

	if(!EQ (reg_res , "0x00"))
	{
		if (!IS_ITEMP(result)) // char = int1 < int 2	nao gera cast, ajusta o resultado aqui
		{
			emitcode("MOV", "R0 , R2");
			emitcode("MOV", "%s , R0", F_OP(result, 0));
		}
		else
		{
			// poe res em r0, o valor eh do resultado eh ajustado em genCast
			emitcode("MOV", "R0 , %s", left->isPtr ? "R2" : aopGet(result, 0, FALSE, FALSE));
		}
	}
}


static void newGenCmpLt(operand *result, operand *left, operand *right)
{
	D(printf ("%s\n", __FUNCTION__));
	D(emitcode ("\n;", "%s\n",__FUNCTION__));
	
	bool leftIsUnsigend = SPEC_USIGN(operandType(left));
	bool rightIsUnsigned = SPEC_USIGN(operandType(right));
	
	symbol *emitLblExit = newiTempLabel(NULL);
	symbol *emitLblTrue = newiTempLabel(NULL);
	int lblExit = labelKey2num(emitLblExit->key);
	int lblTrue = labelKey2num(emitLblTrue->key);

	// otimiza para left < 0
	if (!leftIsUnsigend)
	{
		if (IS_OP_LITERAL(right))
		{
			if (AOP_SIZE (right) == 1)
			{
				if (EQ(aopGet (right, 0 , FALSE , FALSE) , "0x00"))
				{
					genCmpLtZero(result, left);
					return;
				}
			}
			else
			{
				if (EQ(aopGet (right, 0 , FALSE , FALSE) , "0x00"))
				{
					if (EQ(aopGet (right, 1 , FALSE , FALSE) , "0x00"))
					{
						genCmpLtZero(result, left);
						return;
					}
				}
			}
		}
	}
	
	// otimiza para right > 0
	if (!rightIsUnsigned)
	{
		if (IS_OP_LITERAL(left))
		{
			if (AOP_SIZE (left) == 1)
			{
				if (EQ(aopGet (left, 0 , FALSE , FALSE) , "0x00"))
				{
					genCmpGtZero(result, right);
					return;
				}
			}
			else
			{
				if (EQ(aopGet (left, 0 , FALSE , FALSE) , "0x00"))
				{
					if (EQ(aopGet (left, 1 , FALSE , FALSE) , "0x00"))
					{
						genCmpGtZero(result, right);
						return;
					}
				}
			}
		}
	}
	char *reg_res = Safe_strdup(aopGet(result, 0, FALSE, FALSE));
	
	if (IS_ITEMP (left) && IS_ITEMP (right) && rightIsUnsigned && leftIsUnsigend) // compara dois valores temporarios.
	{
		if (!EQ (reg_res , "0x00"))
			emitcode("MVS", "%s , 0x01", IS_ITEMP(result) ? aopGet(result, 0, FALSE, FALSE) : "R2");
		
		if (AOP_SIZE (left) == 1 && AOP_SIZE (right) == 1)
			goto CMP_LOW_PART_UNSIGNED;

	
		else if (AOP_SIZE (left) == 2 && AOP_SIZE (right) == 2)
			goto CMP_HIGH_PART_UNSIGNED;
	}


	if (!leftIsUnsigend && !rightIsUnsigned) //res = sig1 < sig2
	{
		//if(!EQ (reg_res , "0x00"))
		emitcode("MVS", "%s , 0x00", IS_ITEMP(result)&&!EQ (reg_res , "0x00") ? aopGet(result, 0, FALSE, FALSE) : "R2");

		bool cnd = (AOP_SIZE (left) == 1 && AOP_SIZE (right) == 1);
		bool saveR15 = (left -> isPtr && AOP_SIZE(left) == 2) || (right -> isPtr && AOP_SIZE(right) == 2);


		if (left -> isPtr && AOP_SIZE(left) == 2)
			emitcode ("INC" , "%s", aopGet (left , 0 , FALSE , FALSE));
		if (right -> isPtr && AOP_SIZE(right) == 2)
			emitcode ("INC" , "%s", aopGet (right , 0 , FALSE , FALSE));
		
		if (AOP_TYPE (left) == AOP_LIT)
		{
			char *l = aopGet (left , AOP_SIZE (right)-1 , FALSE , FALSE);	
			int t = (int) strtol(l , NULL, 0)&0x80;
			emitcode ("MOV" , "R0 , %d", t);
		}	
	
		else
		{	
			toR0 (left , left -> isPtr||cnd ? 0 : 1);
			emitInstR0Str ("AND" , "0x80");
		}

		emitcode ("MOV" , "R1 , R0");

		if (AOP_TYPE (right) == AOP_LIT)
		{
			char *l = aopGet (right , AOP_SIZE (right)-1 , FALSE , FALSE);	
			int t = (int) strtol(l , NULL, 0)&0x80;
			emitcode ("MOV" , "R0 , %d", t);
		}	
	
		else
		{	
			toR0 (right , right -> isPtr||cnd ? 0 : 1);
			emitInstR0Str ("AND" , "0x80");
		}
	
		emitcode ("CMP" , "R1 , R0");

		if (saveR15)
			emitcode ("MOV" , "R0 , R15");	// salva estado do r15 para impedir que dec modifique as flags
		

		if (left -> isPtr && AOP_SIZE(left) == 2)
			emitcode ("DEC" , "%s", aopGet (left , 0 , FALSE , FALSE));
		if (right -> isPtr && AOP_SIZE(right) == 2)
			emitcode ("DEC" , "%s", aopGet (right , 0 , FALSE , FALSE));


		if (saveR15)
			emitcode ("MOV" , "R15 , R0"); // restaura r15	
		

		emitcode ("JC" , "!tlabel" , lblExit);
		emitcode ("JNZ" , "!tlabel" , lblTrue);

		if (left -> isPtr && AOP_SIZE(left) == 2)
			emitcode ("INC" , "%s", aopGet (left , 0 , FALSE , FALSE));
		if (right -> isPtr && AOP_SIZE(right) == 2)
			emitcode ("INC" , "%s", aopGet (right , 0 , FALSE , FALSE));

		toR0 (left , left -> isPtr||cnd ? 0 : 1);

		emitInstR0Str ("XOR" , "0xFF");		
		emitInstR0Str ("ADD" , "0x01");		
		emitInstR0 ("ADD" , right ,  right -> isPtr||cnd ? 0 : 1);		
		emitcode ("MOV" , "R1 , R0");
		emitInstR0Str ("AND" , "0x80");				

		if (saveR15)
			emitcode ("MOV" , "R0 , R15");

		if (left -> isPtr && AOP_SIZE(left) == 2)
			emitcode ("DEC" , "%s", aopGet (left , 0 , FALSE , FALSE));
		if (right -> isPtr && AOP_SIZE(right) == 2)
			emitcode ("DEC" , "%s", aopGet (right , 0 , FALSE , FALSE));

		if (saveR15)
			emitcode ("MOV" , "R15 , R0");

		emitcode ("JNZ" , "!tlabel" , lblExit);
		toR0Str ("0");
		emitcode ("CMP" , "R1 , R0");
		emitcode ("JC" , "!tlabel" , lblExit);
		emitcode ("JNZ" , "!tlabel" , lblTrue);

		CMP_LOW_PART_SS:
	
		if (IS_ITEMP (right) && IS_ITEMP (left))
		{
			emitcode ("CMP" , "%s , %s",F_OP (right , 0) , F_OP (left , 0));
		}
		else
		{
			toR0 (right , 0);
			emitcode ("MOV" , "R1 , R0");	
			toR0 (left , 0);
			emitcode ("CMP" , "R1 , R0");
		}
		

		emitcode ("JC" , "!tlabel" , lblExit);
		emitcode ("JZ" , "!tlabel",  lblExit);
		emitLabel (emitLblTrue);
	
		emitcode("MVS", "%s , 0x01",
				IS_ITEMP(result) && !EQ (reg_res , "0x00") ? aopGet(result, 0, FALSE, FALSE) : "R2");

		emitLabel (emitLblExit);
	
		//if(!EQ (reg_res , "0x00"))
		{
			if (!IS_ITEMP(result)) // char = int1 < int 2	nao gera cast, ajusta o resultado aqui
			{
				toR0Str ("R2");
				emitcode("MOV", "%s , R0", F_OP(result, 0));
			}

			else
				emitcode("MOV", "R0 , R2");
		}

		return;
	}
	
	if (leftIsUnsigend && rightIsUnsigned) // res = unsig1 < unsig2
	{	
		CMP_HIGH_PART_UNSIGNED: 
		if(!EQ (reg_res , "0x00"))
			emitcode("MVS", "%s , 0x01", IS_ITEMP(result) ? aopGet(result, 0, FALSE, FALSE) : "R2");
		if (left -> isPtr && AOP_SIZE(left) == 2)
		{
			emitcode ("INC" , "%s", aopGet (left , 0 , FALSE , FALSE));
		}
		if (right -> isPtr && AOP_SIZE(right) == 2)
		{
			emitcode ("INC" , "%s", aopGet (right , 0 , FALSE , FALSE));
		}

		if (AOP_SIZE (left) == 1 && AOP_SIZE (right) == 1)
			goto CMP_LOW_PART_UNSIGNED;


		if (IS_ITEMP (left) && IS_ITEMP (right))
		{
			emitcode("CMP", "%s , %s", F_OP(left, left->isPtr ? 0 : 1) ,  F_OP(right, right->isPtr ? 0 : 1));
		}		
		else
		{
			toR0(left, left->isPtr ? 0 : 1);
			emitInstR0 ("CMP" , right, right->isPtr ? 0 : 1);
		}

		emitcode("JC", "!tlabel", lblExit);
		emitcode("JNZ", "!tlabel", lblTrue);
		
		if (left->isPtr)
		{
			emitcode("DEC", "%s", aopGet(left, 0, FALSE, FALSE));
		}
		if (right->isPtr)
		{
			emitcode("DEC", "%s", aopGet(right, 0, FALSE, FALSE));
		}
		
		CMP_LOW_PART_UNSIGNED: 
		if (IS_ITEMP (left) && IS_ITEMP (right))
		{
			emitcode("CMP", "%s , %s", F_OP(left, 0) ,  F_OP(right, 0));
		}		
		else
		{		
			toR0(left, 0);
			emitInstR0 ("CMP" , right , 0);
		}

		emitcode("JC", "!tlabel", lblExit);
		emitLabel(emitLblTrue);
		emitcode("MVS", "%s , 0x00",
				IS_ITEMP(result) && !EQ (reg_res , "0x00") ? aopGet(result, 0, FALSE, FALSE) : "R2");
		
		emitLabel(emitLblExit);
		if(!EQ (reg_res , "0x00"))
		{
			if (!IS_ITEMP(result)) // char = int1 < int 2	nao gera cast, ajusta o resultado aqui
			{
				toR0Str ("R2");
				emitcode("MOV", "%s , R0", F_OP(result, 0));
			}
		}
		return;
	}
}
/*-----------------------------------------------------------------*/
/* genCmpLt - less than comparisons                                */
/*-----------------------------------------------------------------*/
static void genCmpLt(iCode * ic, iCode * ifx)
{
	D(printf ("%s\n",__FUNCTION__));
	D(emitcode ("\n;", "%s\n",__FUNCTION__));
	operand *left, *right, *result;
	left = IC_LEFT(ic);
	right = IC_RIGHT(ic);
	result = IC_RESULT(ic);
	aopOp(result, ic, TRUE);
	aopOp(left, ic, FALSE);
	aopOp(right, ic, FALSE);
	newGenCmpLt(result, left, right);
}

/*-----------------------------------------------------------------*/
/* gencjneshort - compare and jump if not equal                    */
/*-----------------------------------------------------------------*/
static void gencjneshort(operand * left, operand * right, symbol * lbl)
{
	D(emitcode ("\n;", "%s\n", __FUNCTION__));
	
	if (IS_ITEMP(left) && IS_ITEMP(right) && !isVetWithLiteralIndex(left) && !isVetWithLiteralIndex(right))
	{
		emitcode("CMP", "%s , %s", F_OP(left, 0), F_OP(right, 0));
		emitcode("JNZ", "!tlabel", labelKey2num(lbl->key));
		
		if (AOP_SIZE(left) == 1 && AOP_SIZE(right) == 1)
			return;
		
		if (left->isPtr)
		{
			emitcode("INC", "%s", aopGet(left, 0, FALSE, FALSE));
		}
		
		if (right->isPtr)
		{
			emitcode("INC", "%s", aopGet(right, 0, FALSE, FALSE));
		}
		
		emitcode("CMP", "%s , %s", F_OP(left, left->isPtr ? 0 : 1), F_OP(right, right->isPtr ? 0 : 1));
		emitcode("JNZ", "!tlabel", labelKey2num(lbl->key));
	}
	
	else
	{
		 toR0(left, 0);
		//emitcode("CMP", "R0 , %s", F_OP(right, 0));
		emitInstR0 ("CMP" , right , 0);
		emitcode("JNZ", "!tlabel", labelKey2num(lbl->key));
		
		if (AOP_SIZE(left) == 1 && AOP_SIZE(right) == 1)
			return;
		
		if (left->isPtr)
		{
			emitcode("INC", "%s", aopGet(left, 0, FALSE, FALSE));
		}
		
		if (right->isPtr)
		{
			emitcode("INC", "%s", aopGet(right, 0, FALSE, FALSE));
		}
		toR0(left, left->isPtr ? 0 : 1);
		//emitcode("CMP", "R0 , %s", F_OP(right, right->isPtr ? 0 : 1));
		emitInstR0 ("CMP" , right, right->isPtr ? 0 : 1);
		emitcode("JNZ", "!tlabel", labelKey2num(lbl->key));
	}
}

/*-----------------------------------------------------------------*/
/* gencjne - compare and jump if not equal                         */
/*-----------------------------------------------------------------*/
static void gencjne(operand *result, operand * left, operand * right, symbol * lbl, bool useCarry)
{
	D(printf ("%s\n" , __FUNCTION__));
	//emitcode ("MVS" , "R2 , 0x00");
	emitcode("MVS", "%s , 0x00", !IS_ITEMP(result) ? "R2" : aopGet(result, 0, FALSE, FALSE));
	
	// Otimiza para res == 0
	if (IS_OP_LITERAL(right))
	{
		if (AOP_SIZE (right) == 1)
		{
			if (EQ(aopGet (right, 0 , FALSE , FALSE) , "0x00"))
			{
				toR0(left, 0);
				emitcode("JNZ", "!tlabel", labelKey2num(lbl->key));
			}
		}
		else
		{
			if (EQ(aopGet (right, 0 , FALSE , FALSE) , "0x00"))
			{
				if (EQ(aopGet (right, 1 , FALSE , FALSE) , "0x00"))
				{
					toR0(left, 0);
					if (left->isPtr)
					{
						emitcode("INC", "%s", aopGet(left, 0, FALSE, FALSE));
					}
					emitInstR0 ("OR" , left, left->isPtr ? 0 : 1);
					emitcode("JNZ", "!tlabel", labelKey2num(lbl->key));
				}
			}
		}
	}
	else
	{
		gencjneshort(left, right, lbl);
	}
	//emitcode ("MVS" , "R2 , 0x01");
	emitcode("MVS", "%s , 0x01", !IS_ITEMP(result) ? "R2" : aopGet(result, 0, FALSE, FALSE));
	emitLabel(lbl);
	//emitcode ("MOV" , "R0 , R2");
	emitcode("MOV", "R0 , %s", !IS_ITEMP(result) ? "R2" : aopGet(result, 0, FALSE, FALSE));
}
/*-----------------------------------------------------------------*/
/* genCmpEq - generates code for equal to                          */
/*-----------------------------------------------------------------*/
static void genCmpEq(iCode * ic, iCode * ifx)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode ("\n;", "genCmpEq\n"));
	bool swappedLR = FALSE;
	operand *left, *right, *result;
	iCode *popIc = ic->next;
	
	aopOp((left = IC_LEFT(ic)), ic, FALSE);
	aopOp((right = IC_RIGHT(ic)), ic, FALSE);
	aopOp((result = IC_RESULT(ic)), ic, TRUE);
	
	if ((AOP_TYPE (left) == AOP_LIT) || (IS_AOP_PREG (right) && !IS_AOP_PREG (left)))
	{
		swapOperands(&left, &right);
		swappedLR = TRUE;
	}
	if (ifx && !AOP_SIZE (result))
	{
		symbol *tlbl;
		// if they are both bit variables
		if (AOP_TYPE (left) == AOP_CRY && ((AOP_TYPE (right) == AOP_CRY) || (AOP_TYPE (right) == AOP_LIT)))
		{
			if (AOP_TYPE (right) == AOP_LIT)
			{
				unsigned long lit = ulFromVal(AOP (right)->aopu.aop_lit);
				if (lit == 0L)
				{

				}
				else if (lit == 1L)
				{

				}
				else
				{
				}
				// AOP_TYPE(right) == AOP_CRY
			}
			else
			{

			}
			//if true label then we jump if condition
			// supplied is true
			tlbl = newiTempLabel(NULL);
			if (IC_TRUE(ifx))
			{
				emitcode("jnc", "!tlabel", labelKey2num(tlbl->key));
				freeForBranchAsmops(result, right, left, ic);
				popForBranch(popIc, FALSE);
				emitcode("JMP", "!tlabel", labelKey2num(IC_TRUE(ifx)->key));
			}
			else
			{
				emitcode("jc", "!tlabel", labelKey2num(tlbl->key));
				freeForBranchAsmops(result, right, left, ic);
				popForBranch(popIc, FALSE);
				emitcode("JMP", "!tlabel", labelKey2num(IC_FALSE(ifx)->key));
			}
			emitLabel(tlbl);
		}
		else
		{
			tlbl = newiTempLabel(NULL);
			gencjneshort(left, right, tlbl);
			if (IC_TRUE(ifx))
			{
				freeForBranchAsmops(result, right, left, ic);
				popForBranch(popIc, FALSE);
				emitcode("MOV", "R0 , 0x01");
				emitcode("JMP", "!tlabel", labelKey2num(IC_TRUE(ifx)->key));
				emitLabel(tlbl);
			}
			else
			{
				symbol *lbl = newiTempLabel(NULL);
				emitcode("JMP", "!tlabel", labelKey2num(lbl->key));
				emitLabel(tlbl);
				freeForBranchAsmops(result, right, left, ic);
				popForBranch(popIc, FALSE);
				emitcode("JMP", "!tlabel", labelKey2num(IC_FALSE(ifx)->key));
				emitLabel(lbl);
			}
		}
		// mark the icode as generated
		ifx->generated = 1;
		goto release;
	}
	// if they are both bit variables
	if (AOP_TYPE (left) == AOP_CRY && ((AOP_TYPE (right) == AOP_CRY) || (AOP_TYPE (right) == AOP_LIT)))
	{
		if (AOP_TYPE (right) == AOP_LIT)
		{
			unsigned long lit = ulFromVal(AOP (right)->aopu.aop_lit);
			if (lit == 0L)
			{

			}
			else if (lit == 1L)
			{
			}
			else
			{
			}
			//AOP_TYPE(right) == AOP_CRY
		}
		else
		{

		}
		// c = 1 if egal
		if (AOP_TYPE (result) == AOP_CRY && AOP_SIZE (result))
		{
			outBitC(result);
			goto release;
		}
		if (ifx)
		{
			genIfxJump(ifx, "c", left, right, result, popIc);
			goto release;
		}
		// if the result is used in an arithmetic operation
		//then put the result in place
		outBitC(result);
	}
	else
	{
		bool useCarry = (AOP_TYPE (result) == AOP_CRY);
		gencjne(result, left, right, newiTempLabel(NULL), useCarry);
		if (useCarry && AOP_SIZE (result))
		{
			//aopPut(result, "c", 0, __FUNCTION__, __LINE__);
			goto release;
		}
		if (ifx)
		{
			genIfxJump(ifx, useCarry ? "c" : "a", left, right, result, popIc);
			goto release;
		}
		// if the result is used in an arithmetic operation
		// then put the result in place
		if (!useCarry)
			outAcc(result);
		// leave the result in acc
	}
	
	//emitcode ("MOV" , "%s , R1	;abc", aopGet (result , 0 , FALSE , FALSE));
	
	if (!IS_ITEMP(result) && AOP_SIZE (result) == 1)
	{
		emitcode("MOV", "%s , R0", F_OP(result, 0));
	}
	release: freeAsmop(result, NULL, ic, TRUE);
	if (swappedLR)
		swapOperands(&left, &right);
	freeAsmop(right, NULL, ic, (RESULTONSTACK (ic) ? FALSE : TRUE));
	freeAsmop(left, NULL, ic, (RESULTONSTACK (ic) ? FALSE : TRUE));
}
/*-----------------------------------------------------------------*/
/* hasInc - operand is incremented before any other use            */
/*-----------------------------------------------------------------*/
static iCode *
hasInc(operand * op, iCode * ic, int osize)
{
	sym_link *type = operandType(op);
	sym_link *retype = getSpec(type);
	iCode *lic = ic->next;
	int isize;
	/* this could from a cast, e.g.: "(char xdata *) 0x7654;" */
	if (!IS_SYMOP(op))
		return NULL;
	if (IS_BITVAR(retype) || !IS_PTR(type))
		return NULL;
	if (IS_AGGREGATE(type->next))
		return NULL;
	if (osize != (isize = getSize(type->next)))
		return NULL;
	while (lic)
	{
		/* if operand of the form op = op + <sizeof *op> */
		if (lic->op == '+' && isOperandEqual(IC_LEFT(lic), op) && isOperandEqual(IC_RESULT(lic), op)
				&& isOperandLiteral(IC_RIGHT(lic)) && operandLitValue(IC_RIGHT(lic)) == isize)
		{
			return lic;
		}
		/* if the operand used or deffed */
		if (bitVectBitValue(OP_USES(op), lic->key) || lic->defKey == op->key)
		{
			return NULL;
		}
		/* if GOTO or IFX */
		if (lic->op == IFX || lic->op == GOTO || lic->op == LABEL)
			break;
		lic = lic->next;
	}
	return NULL;
}
/*-----------------------------------------------------------------*/
/* genAndOp - for && operation                                     */
/*-----------------------------------------------------------------*/
static void genAndOp(iCode * ic)
{
	D(printf ("%s\n",__FUNCTION__));
	operand *left, *right, *result;
	symbol *tlbl;
	D(emitcode (";", "genAndOp"));
	/* note here that && operations that are in an
	 if statement are taken away by backPatchLabels
	 only those used in arthmetic operations remain */
	aopOp((left = IC_LEFT(ic)), ic, FALSE);
	aopOp((right = IC_RIGHT(ic)), ic, FALSE);
	aopOp((result = IC_RESULT(ic)), ic, FALSE);
	
	/* if both are bit variables */
	if (AOP_TYPE (left) == AOP_CRY && AOP_TYPE (right) == AOP_CRY)
	{
		emitcode("mov", "c,%s", AOP (left)->aopu.aop_dir);
		emitcode("AND", "c,%s", AOP (right)->aopu.aop_dir);
		outBitC(result);
	}
	else
	{
		tlbl = newiTempLabel(NULL);
		toBoolean(left);		// faz OR low , right pra detectar zero
		emitcode("jz", "!tlabel", labelKey2num(tlbl->key));
		toBoolean(right);
		emitLabel(tlbl);
		outBitAcc(result);
	}
	freeAsmop(result, NULL, ic, TRUE);
	freeAsmop(right, NULL, ic, (RESULTONSTACK (ic) ? FALSE : TRUE));
	freeAsmop(left, NULL, ic, (RESULTONSTACK (ic) ? FALSE : TRUE));
}
/*-----------------------------------------------------------------*/
/* genOrOp - for || operation                                      */
/*-----------------------------------------------------------------*/
static void genOrOp(iCode * ic)
{
	operand *left, *right, *result;
	symbol *tlbl;
	D(emitcode (";", "genOrOp"));
	/* note here that || operations that are in an
	 if statement are taken away by backPatchLabels
	 only those used in arthmetic operations remain */
	aopOp((left = IC_LEFT(ic)), ic, FALSE);
	aopOp((right = IC_RIGHT(ic)), ic, FALSE);
	aopOp((result = IC_RESULT(ic)), ic, FALSE);
	/* if both are bit variables */
	if (AOP_TYPE (left) == AOP_CRY && AOP_TYPE (right) == AOP_CRY)
	{
		outBitC(result);
	}
	else
	{
		tlbl = newiTempLabel(NULL);
		toBoolean(left);
		emitcode("jnz", "!tlabel", labelKey2num(tlbl->key));
		toBoolean(right);
		emitLabel(tlbl);
		outBitAcc(result);
	}
	freeAsmop(result, NULL, ic, TRUE);
	freeAsmop(right, NULL, ic, (RESULTONSTACK (ic) ? FALSE : TRUE));
	freeAsmop(left, NULL, ic, (RESULTONSTACK (ic) ? FALSE : TRUE));
}



char *F_OP(operand *op, int offset)
{
	D(printf ("%s\n", __FUNCTION__));

	char *opName = aopGet (op , 0 , FALSE , FALSE);
	
	if (!strncmp (opName , "(_IO" , 4) || !strncmp (opName , "_IO" , 3))
	{
		char *P = (char*) malloc(20 * sizeof(char));
		strcpy(P, "(");
		strcat(P, getIndex (opName));
		return strcat(P, ")");
	} 

	if (isVetWithLiteralIndex(op))
	{
		return fVetLitId(aopGet(op, 0, FALSE, FALSE), offset);
	}
	
	if (IS_OP_PARM(op))
	{
		char *parm = Safe_strdup(aopGet(op, offset, FALSE, FALSE));
	
		if (*parm == '@')
			return "(sp)";
	
		if (offset)
		{
			replace(parm, " + 1", "_H");
			return parm;
		}
		
		char *B = (char*) malloc(50 * sizeof(char));
		strcpy(B, "(");
		return strcat(B, strcat(parm, "_L)"));
	}
	
	if (op->isPtr)
	{
		char *reg = Safe_strdup(aopGet(op, offset, FALSE, FALSE));
		char *B = (char*) malloc(10 * sizeof(char));
		strcpy(B, "(");
		strcat(B, strcat(reg, ")"));
		return B;
	}
	
	if (IS_ITEMP(op) || IS_OP_LITERAL(op)) // registrador ou literal
	{
		return Safe_strdup(aopGet(op, offset, FALSE, FALSE));
	}

	char *v = op->svt.symOperand->name; // entra x	retorna  (x_L) ou (x_H)
	char *B = (char*) malloc(50 * sizeof(char));
	strcpy(B, "(");
	strcat(B, v);
	return strcat(B, offset ? "_H)" : "_L)");
}

static void genBitwiseOperation(iCode *ic, char *MNM)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode ("\n;", "gen%s\n", MNM));

	aopOp(IC_LEFT(ic), ic, FALSE);
	aopOp(IC_RIGHT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	
	operand *left = IC_LEFT(ic);
	operand *right = IC_RIGHT(ic);
	operand *result = IC_RESULT(ic);
	
	char *res = Safe_strdup(aopGet(result, 0, FALSE, FALSE));
	char *le = Safe_strdup(aopGet(left, 0, FALSE, FALSE));
	char *ri = Safe_strdup(aopGet(right, 0, FALSE, FALSE));
	bool leftIsIO = !strncmp (le , "(_IO" , 4) || !strncmp (le , "_IO" , 3);
	bool rightIsIO =!strncmp (ri , "(_IO" , 4) || !strncmp (ri , "_IO" , 3); 

	if (leftIsIO||rightIsIO)
	{/*
		a = b&IO[2]

		MOV R0 , (b_L)
		AND IO R0  , (2) 
		MOV (a_L) , R0
	*/
		if (rightIsIO) toR0Str (F_OP(left , 0));
		else toR0Str (F_OP (right , 0));

		emitcode("", "%s IO R0 , %s", MNM, rightIsIO ? Safe_strdup(F_OP(right, 0)) : Safe_strdup(F_OP(left, 0)));
		emitcode ("MOV" , "%s , R0", F_OP (result , 0));		
		return;
	}


	if (isVetWithLiteralIndex(right) && isVetWithLiteralIndex(left))
	{
		emitcode("MOV", "R0 , %s", fVetLitId(le, 0));
		emitcode("", "%s R0 , %s", MNM, fVetLitId(ri, 0));
		emitcode("MOV", "%s , R0", F_OP(result, 0));
		emitcode("MOV", "R0 , %s", fVetLitId(aopGet(left, 0, FALSE, FALSE), 1));
		emitcode("", "%s R0 , %s", MNM, fVetLitId(aopGet(right, 0, FALSE, FALSE), 1));
		emitcode("MOV", "%s , R0", F_OP(result, 1));
		return;
	}
	

	if (EQ (res , "0x00"))
	{
		toR0 (right , 0);
		emitcode ("MOV" , "R1 , %s ;*", F_OP(left , 0));
		emitcode("", "%s R1 , R0 ;*", MNM);// F_OP(left, 0));

		/*if (AOP_SIZE (result) == 1)
			return;
		toR0 (right , 1);
		emitcode("#", "%s %s , R0", MNM, F_OP(left, 1));*/
		return;
	}

	if (IS_ITEMP(left) && IS_ITEMP(right))
	{
		emitcode("", "%s %s , %s", MNM, Safe_strdup(F_OP(left, 0)), Safe_strdup(F_OP(right, 0)));
		
		if (IS_ITEMP(result))
		{
			emitcode("MOV", "%s , %s", Safe_strdup(F_OP(result, 0)), Safe_strdup(F_OP(left, 0)));
		}
		
		else
		{
			emitcode("MOV", "R0 , %s", Safe_strdup(F_OP(left, 0)));
			emitcode("MOV", "%s , R0", Safe_strdup(F_OP(result, 0)));
		}
	}
	
	else
	{
		emitcode("MOV", "R0 , %s", F_OP(left, 0));
		emitcode("", "%s R0 , %s", MNM, F_OP(right, 0));
		emitcode("MOV", "%s , R0", F_OP(result, 0));
	}
	
	if (AOP_SIZE (result) == 1 ||AOP_SIZE(right) == 1 || AOP_SIZE(left) == 1) // FIXME
	{
		return;
	}
	
	if (result->isPtr)
	{
		emitcode("INC", "%s", aopGet(result, 1, FALSE, FALSE));
	}
	if (right->isPtr)
	{
		emitcode("INC", "%s", aopGet(right, 1, FALSE, FALSE));
	}
	if (left->isPtr)
	{
		emitcode("INC", "%s", aopGet(left, 1, FALSE, FALSE));
	}
	
	if (IS_ITEMP(left) && IS_ITEMP(right))
	{
		emitcode("", "%s %s , %s", MNM, Safe_strdup(F_OP(left, 1)), Safe_strdup(F_OP(right, 1)));
		
		if (IS_ITEMP(result))
		{
			emitcode("MOV", "%s , %s", Safe_strdup(F_OP(result, result->isPtr ? 0 : 1)), Safe_strdup(F_OP(left, 1)));
		}
		else
		{
			emitcode("MOV", "R0 , %s", Safe_strdup(F_OP(left, 1)));
			emitcode("MOV", "%s , R0", Safe_strdup(F_OP(result, result->isPtr ? 0 : 1)));
		}
	}
	else
	{
		emitcode("MOV", "R0 , %s", F_OP(left, 1));
		emitcode("", "%s R0 , %s", MNM, F_OP(right, 1));
		emitcode("MOV", "%s , R0", F_OP(result, result->isPtr ? 0 : 1));
	}
}

/*-----------------------------------------------------------------*/
/* genAnd  - code for and                                          */
/*-----------------------------------------------------------------*/
static void genAnd(iCode * ic, iCode * ifx)
{
	genBitwiseOperation(ic, "AND");
	return;
}

/*-----------------------------------------------------------------*/
/* genOr  - code for or                                            */
/*-----------------------------------------------------------------*/
static void genOr(iCode * ic, iCode * ifx)
{
	genBitwiseOperation(ic, "OR");
}

/*-----------------------------------------------------------------*/
/* genXor - code for xclusive or                                   */
/*-----------------------------------------------------------------*/
static void genXor(iCode * ic, iCode * ifx)
{
	genBitwiseOperation(ic, "XOR");
}

/*-----------------------------------------------------------------*/
/* genRRC - rotate right with carry                                */
/*-----------------------------------------------------------------*/
static void genRRC(iCode * ic)
{
}
/*-----------------------------------------------------------------*/
/* genRLC - generate code for rotate left with carry               */
/*-----------------------------------------------------------------*/
static void genRLC(iCode * ic)
{

}
/*-----------------------------------------------------------------*/
/* genGetAbit - generates code get a single bit                    */
/*-----------------------------------------------------------------*/
static void genGetAbit(iCode * ic)
{

}
/*-----------------------------------------------------------------*/
/* genGetByte - generates code get a single byte                   */
/*-----------------------------------------------------------------*/
static void genGetByte(iCode * ic)
{
}
/*-----------------------------------------------------------------*/
/* genGetWord - generates code get two bytes                       */
/*-----------------------------------------------------------------*/
static void genGetWord(iCode * ic)
{

}
/*-----------------------------------------------------------------*/
/* genSwap - generates code to swap nibbles or bytes               */
/*-----------------------------------------------------------------*/
static void genSwap(iCode * ic)
{
}

/*-----------------------------------------------------------------*/
/* shiftL1Left2Result - shift left one byte from left to result    */
/*-----------------------------------------------------------------*/
static void shiftL1Left2Result(operand * left, int offl, operand * result, int offr, int shCount)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode("\n;", "; %s\n", __FUNCTION__));

	toR0 (left , 0);
	emitInstR0Str ("ADD" , "R0");
	emitcode ("MOV" , "%s , R0", F_OP (result , 0));

}



static void shiftL2Left2Result(operand * left, int offl, operand * result, int offr, int shCount)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode("\n;", "; %s\n", __FUNCTION__));
	

	//emitcode ("MOV" , "R9 , R0");
	toR0 (left , 0);
	emitInstR0Str ("ADD" , "R0");
	emitcode("MOV", "R1 , R0");
	//emitcode ("MOV" , "R9 , R0");
	
	return;
}


/*-----------------------------------------------------------------*/
/* genLeftShiftLiteral - left shifting by 1 bit

 -> shift left e/d=1
 /*-----------------------------------------------------------------*/
static void genLeftShiftLiteral(operand * left, operand * right, operand * result, iCode * ic)
{
	D(emitcode ("\n;" , "%s\n",__FUNCTION__));

	//if (IS_ITEMP (left))
	{
		int i, shiftNmb = (int) strtol(aopGet(right, 0, FALSE, FALSE), NULL, 0);

		toR0(left, 0);

		/*
			// forma antiga:

			emitcode("MOV", "R0 , 2");
			emitcode("OR", "R15 , R0");
		
			for (i = 0; i < shiftNmb; i++)
			{
				emitcode("SHL", "R0 , R0");
			}

		*/
		
		// forma nova ; Poupa as duas instruções  emitcode("MOV", "R0 , 2"); e emitcode("OR", "R15 , R0");

			for (i = 0; i < shiftNmb; i++)
			{
				emitInstR0Str("ADD", "R0");
			}
	
		emitcode("MOV", "%s , R0", F_OP(result, 0));
		
		if (AOP_SIZE (result) == 1)
			return;
		
		toR0(left, 1);
		
		for (i = 0; i < shiftNmb; i++)
		{
			emitInstR0Str("ADD", "R0"); //emitcode("SHL", "R0 , R0");
		}
		
		emitcode("MOV", "%s , R0", F_OP(result, 1));
		return;
	}
	freeAsmop(result, NULL, ic, TRUE);
	freeAsmop(left, NULL, ic, TRUE);
}

/*-----------------------------------------------------------------*/
/* genLeftShift - generates code for left shifting                 */
/*-----------------------------------------------------------------*/
static void genLeftShift(iCode * ic)
{
	D(printf ("%s\n", __FUNCTION__));
	
	operand *left, *right, *result;
	int size, offset;
	symbol *tlbl, *tlbl1;
	bool pushedB;
	right = IC_RIGHT(ic);
	left = IC_LEFT(ic);
	result = IC_RESULT(ic);
	aopOp(right, ic, FALSE);
	aopOp(left, ic, FALSE);
	aopOp(result, ic, FALSE);
	
	char *res = Safe_strdup(aopGet(result, 0, FALSE, FALSE));
	char *le = Safe_strdup(aopGet(left, 0, FALSE, FALSE));
	char *ri = Safe_strdup(aopGet(right, 0, FALSE, FALSE));
	
	if (AOP_TYPE (right) == AOP_LIT)
	{
		genLeftShiftLiteral(left, right, result, ic);
		return;
	}
}


/*-----------------------------------------------------------------*/
/* genRightShiftLiteral - right shifting by known count            */
/*-----------------------------------------------------------------*/
static void genRightShiftLiteral(operand * left, operand * right, operand * result, iCode * ic, int sign)
{
	D(printf ("%s\n",__FUNCTION__));
	
	int i, shiftNmb = (int) strtol(aopGet(right, 0, FALSE, FALSE), NULL, 0);

	toR0(left, 0);
	
	for (i = 0; i < shiftNmb; i++)
	{
	//	emitcode("SHL", "R0 , R0");
		emitInstR0Str ("SHL" , "R0");
	}
	
	emitcode("MOV", "%s , R0", F_OP(result, 0));
	
	if (AOP_SIZE (result) == 1)
		return;
	
	emitcode("MOV", "R0 , %s", F_OP(left, 1));
	
	for (i = 0; i < shiftNmb; i++)
	{
		//emitcode("SHL", "R0 , R0");	
		emitInstR0Str ("SHL" , "R0");
	}
	
	emitcode("MOV", "%s , R0", F_OP(result, 1));
	return;
}
/*-----------------------------------------------------------------*/
/* genSignedRightShift - right shift of signed number              */
/*-----------------------------------------------------------------*/
static void genSignedRightShift(iCode * ic)
{
	operand *right, *left, *result;
	
	right = IC_RIGHT(ic);
	left = IC_LEFT(ic);
	result = IC_RESULT(ic);
	aopOp(right, ic, FALSE);
	aopOp(result, ic, FALSE);
	aopOp(left, ic, FALSE);
	
	D(printf("%s\n", __FUNCTION__));
	
	int i, shiftNmb = (int) strtol(aopGet(right, 0, FALSE, FALSE), NULL, 0);
	
	toR0(left, 0);
	
	for (i = 0; i < shiftNmb; i++)
	{
		//emitcode("SHL", "R0 , R0");
		emitInstR0Str ("SHL" , "R0");
	}
	
	emitcode("MOV", "%s , R0", F_OP(result, 0));
	
	if (AOP_SIZE (result) == 1)
		return;
	
	emitcode("MOV", "R0 , %s", F_OP(left, 1));
	
	for (i = 0; i < shiftNmb; i++)
	{
		//emitcode("SHA", "R0 , R0");
		emitInstR0Str ("SHA" , "R0");
	}
	
	emitcode("MOV", "%s , R0", F_OP(result, 1));
}

/*-----------------------------------------------------------------*/
/* genRightShift - generate code for right shifting                */
/*-----------------------------------------------------------------*/
static void genRightShift(iCode * ic)
{
	D(printf ("%s\n", __FUNCTION__));

	aopOp(IC_LEFT(ic), ic, FALSE);
	aopOp(IC_RIGHT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	
	operand *left = IC_LEFT(ic);
	operand *right = IC_RIGHT(ic);
	operand *result = IC_RESULT(ic);
	
	toR0Str("0b11111101");
	emitcode("AND", "R15 , R0");
	
	sym_link *letype = getSpec(operandType(IC_LEFT(ic)));
	if (!SPEC_USIGN(letype))
	{
		genSignedRightShift(ic);
		return;
	}
	
	if (AOP_TYPE (right) == AOP_LIT)
	{
		genRightShiftLiteral(left, right, result, ic, 0);
		return;
	}
	 freeAsmop(result, NULL, ic, TRUE);
	freeAsmop(left, NULL, ic, TRUE);
}


/*-----------------------------------------------------------------*/
/* genUnpackBits - generates code for unpacking bits               */
/*-----------------------------------------------------------------*/
static char *
genUnpackBits(operand * result, const char *rname, int ptype, iCode * ifx)
{
	D(printf("%s\n", __FUNCTION__));
	return NULL;
}
/*-----------------------------------------------------------------*/
/* genDataPointerGet - generates code when ptr offset is known     */
/*-----------------------------------------------------------------*/
static void genDataPointerGet(operand * left, operand * result, iCode * ic)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode (";\n", "%s\n", __FUNCTION__));
	char *l;
	int size, offset = 0;
	
	aopOp(result, ic, TRUE);
	aopOp(left, ic, TRUE);
	
	char *res = aopGet(result, 0, FALSE, TRUE);
	
	if (!isVetWithLiteralIndex(result))
	{
		//if (strstr (le , "+")) //isVetWithLiteralIndex (left , le))
		{
			/*
			 Exemplo:
			 x = A[3];

			 mvs R8 , A
			 mov R0 , 3
			 add R8 , R0
			 mov r0 , (r1)
			 mov (x_L) , r0
			 inc r1
			 mov r0 , (r1)
			 mov (x_H) , r0


			 */

			if (!IS_ITEMP(result))
			{
				char *le = aopGet(left, 0, FALSE, TRUE);
				bool cond = strstr(le, ")"); // verifica se indice eh zero.
				char *endBaseVetor = getVarName(le);
				
				char *str_index = cond ? getSubString(res, "+", ")") : "0";
				int index = (int) strtol(str_index, NULL, 0);
				emitcode("MVS", "R8 , %s", endBaseVetor);
				emitcode("MOV", "R0 , %d", index);
				emitcode("ADD", "R8 , R0");
				emitcode("MOV", "R0 , (R8)");
				
				res = aopGet(result, 0, FALSE, TRUE);
				replace(res, "_", "");
				emitcode("MOV", "(%s_L) , R0", res);
				emitcode("INC", "R8");
				emitcode("MOV", "R0 , (R8)");
				emitcode("MOV", "(%s_H) , R0", res);
			}
			
			else
			{
				char *le = aopGet(left, 0, FALSE, TRUE);
				bool cond = strstr(le, ")"); // verifica se indice eh zero.
				char *endBaseVetor = getVarName(le);
				
				char *str_index = cond ? getSubString(res, "+", ")") : "0";
				int index = (int) strtol(str_index, NULL, 0);
				emitcode("MVS", "R8 , %s", endBaseVetor);
				emitcode("MOV", "R0 , %d", index);
				emitcode("ADD", "R8 , R0");
				emitcode("MOV", "R0 , (R8)");
				
				res = aopGet(result, 0, FALSE, FALSE);
				replace(res, "_", "");
				emitcode("MOV", "%s , R0", res);
				emitcode("INC", "R8");
				emitcode("MOV", "R0 , (R8)");
				res = aopGet(result, 1, FALSE, FALSE);
				emitcode("MOV", "%s , R0", res);
			}
		}
		
		//else
		{
		}
	}
}


/*-----------------------------------------------------------------*/
/* genNearPointerGet - emitcode for near pointer fetch             */
/*-----------------------------------------------------------------*/
static void genNearPointerGet(operand * left, operand * result, iCode * ic, iCode * pi, iCode * ifx)
{
	D(printf ("%s\n",__FUNCTION__));
	D(emitcode ("\n;", "genNearPointerGet\n"));
	
	asmop *aop = NULL;
	reg_info *preg = NULL;
	const char *rname;
	char *ifxCond = "a";
	sym_link *rtype, *retype;
	sym_link *ltype = operandType(left);

	aopOp(result, ic, FALSE);
	aopOp(left, ic, FALSE);
	
	char *res = IS_ITEMP(result) ? Safe_strdup(aopGet(result, 0, FALSE, FALSE)) : result->svt.symOperand->name;
	char *le = IS_ITEMP(left) ? Safe_strdup(aopGet(left, 0, FALSE, FALSE)) : left->svt.symOperand->name;
	D(emitcode ("\n;" , "res = %s" , res));
	D(emitcode ("\n;" , "left = %s\n" , le));
	if (!strncmp(le, "#(_IO", 5) || !strncmp(le, "#_IO", 4))
	{
		/*
		 x = IO[2];
		 mov IO r0 (2)
		 mov (x_L) , r0
		 */
		bool cond = strstr(le, ")"); // verifica se indice eh zero.
		char *str_index = cond ? getSubString(le, "+", ")") : "0";
		int index = (int) strtol(str_index, NULL, 0);
		emitcode("MOV", "IO R0 , (%d)", index);
		emitcode("MOV", "(%s_L) , R0", res);
		return;
	}
	
	if (IS_ITEMP(result))
	{		
		if (*le != '#') //IS_ITEMP(left)) // v1[i] = v2[i]
		{
			
			emitcode("MOV", "%s , %s", res, le);
			result->isPtr = 1;//
			//left->isPtr = 1;
			return;
		}
		
		else if (isVetWithLiteralIndex (left))
		{
			toR0 (left , 0);
			emitcode("MOV", "%s , R0", aopGet(result, 0, FALSE, FALSE));

			if (AOP_SIZE (result) == 1)
				return;

			toR0 (left , 1);
			emitcode("MOV", "%s , R0",  aopGet(result, 1, FALSE, FALSE));
			return;
		}
	}
	
	//x = v[i]
	if (!isVetWithLiteralIndex(left))
	{
		res = Safe_strdup(aopGet(result, 0, FALSE, FALSE) + 1);
		le = Safe_strdup(aopGet(left, 0, FALSE, FALSE));
		
		if (!left->isPtr)
		{
			left -> isPtr = 1;
			emitcode("MOV", "R0 , (%s)", le);
			emitcode("MOV", "(%s_L) , R0", res);
			
			if (AOP_SIZE(result) == 1)
				return;
			emitcode("INC", "%s", le);
			emitcode("MOV", "R0 , (%s)", le);
			emitcode("MOV", "(%s_H) , R0", res);
			emitcode("DEC", "%s", le);
		}
		else // MOV IO R0 , (Addr)  IO tem 1B
		{
			emitcode("MOV", "(%s_L) , R0", res);
		}
	}
	
	else //x = v[3]
	{

		emitcode("MOV", "R0 , %s", fVetLitId(aopGet(left, 0, FALSE, FALSE), 0));
		emitcode("MOV", "%s , R0", F_OP(result, 0));
		if (AOP_SIZE(result) == 1)
			return;
		emitcode("MOV", "R0 , %s", fVetLitId(aopGet(left, 0, FALSE, FALSE), 1));
		emitcode("MOV", "%s , R0", F_OP(result, 1));
	}
}
/*-----------------------------------------------------------------*/
/* genPagedPointerGet - emitcode for paged pointer fetch           */
/*-----------------------------------------------------------------*/
static void genPagedPointerGet(operand * left, operand * result, iCode * ic, iCode * pi, iCode * ifx)
{
	D(printf("%s\n", __FUNCTION__));
}
/*-----------------------------------------------------------------*/
/* genFarPointerGet - get value from far space                     */
/*-----------------------------------------------------------------*/
static void genFarPointerGet(operand * left, operand * result, iCode * ic, iCode * pi, iCode * ifx)
{
	int size, offset;
	char *ifxCond = "a";
	sym_link *retype = getSpec(operandType(result));
	D(emitcode (";", "genFarPointerGet"));
	aopOp(left, ic, FALSE);
	loadDptrFromOperand(left, FALSE);
	/* so dptr now contains the address */
	aopOp(result, ic, FALSE);
	/* if bit then unpack */
	if (IS_BITFIELD(retype))
		ifxCond = genUnpackBits(result, "dptr", FPOINTER, ifx);
	else
	{
		size = AOP_SIZE (result);
		offset = 0;
		while (size--)
		{
			emitcode("movx", "a,@dptr");
			//if (!ifx)
			//	aopPut(result, "a", offset++, __FUNCTION__, __LINE__);
			if (size || pi)
				emitcode("inc", "dptr");
		}
	}
	if (pi && AOP_TYPE (left) != AOP_IMMD && AOP_TYPE (left) != AOP_STR)
	{
		//aopPut(left, "R8", 0, __FUNCTION__, __LINE__);
		//aopPut(left, "R9", 1, __FUNCTION__, __LINE__);
		pi->generated = 1;
	}
	if (ifx && !ifx->generated)
	{
		genIfxJump(ifx, ifxCond, left, NULL, result, ic->next);
	}
	freeAsmop(result, NULL, ic, TRUE);
	freeAsmop(left, NULL, ic, TRUE);
}
/*-----------------------------------------------------------------*/
/* genCodePointerGet - get value from code space                   */
/*-----------------------------------------------------------------*/
static void genCodePointerGet(operand * left, operand * result, iCode * ic, iCode * pi, iCode * ifx)
{
	D(printf("%s\n", __FUNCTION__));
}
/*-----------------------------------------------------------------*/
/* genGenPointerGet - get value from generic pointer space         */
/*-----------------------------------------------------------------*/
static void genGenPointerGet(operand * left, operand * result, iCode * ic, iCode * pi, iCode * ifx)
{
	int size, offset;
	char *ifxCond = "a";
	sym_link *retype = getSpec(operandType(result));
	D(emitcode (";", "genGenPointerGet\n"));

	aopOp(left, ic, FALSE);
	aopOp(result, ic, FALSE);


	if (IS_ITEMP (result) && IS_ITEMP (left))
	{
		emitcode ("MOV" , "%s , %s", F_OP (result , 0) , F_OP (left , 0));
		if (AOP_SIZE (result) == 1)
			return;
		
		emitcode ("MOV" , "%s , %s", F_OP (result , 1) , F_OP (left , 1));
		return;
	}

	left -> isPtr = true;
	emitcode ("MOV" , "R0 , %s", F_OP (left , 0));
	emitcode ("MOV" , "%s , R0", F_OP (result , 0));

	if (AOP_SIZE (result) == 1)
		return;

	emitcode ("INC" , "%s", aopGet (left , 0 , FALSE , FALSE));	
	emitcode ("MOV" , "R0 , %s", F_OP (left , 0));
	emitcode ("MOV" , "%s , R0", F_OP (result , 1));
	emitcode ("DEC" , "%s", aopGet (left , 0 , FALSE , FALSE));	
}
/*-----------------------------------------------------------------*/
/* genPointerGet - generate code for pointer get                   */
/*-----------------------------------------------------------------*/
static void genPointerGet(iCode * ic, iCode * pi, iCode * ifx)
{
	operand *left, *result;
	sym_link *type, *etype;
	int p_type;
	D(emitcode (";", "genPointerGet"));
	left = IC_LEFT(ic);
	result = IC_RESULT(ic);
	if (getSize(operandType(result)) > 1)
		ifx = NULL;
	/* depending on the type of pointer we need to
	 move it to the correct pointer register */
	type = operandType(left);
	etype = getSpec(type);
	/* if left is of type of pointer then it is simple */
	if (IS_PTR(type) && !IS_FUNC(type->next))
	{
		p_type = DCL_TYPE(type);
	}
	else
	{
		/* we have to go by the storage class */
		p_type = PTR_TYPE(SPEC_OCLS(etype));
	}
	/* special case when cast remat */
	while (IS_SYMOP(left) && OP_SYMBOL(left)->remat && IS_CAST_ICODE(OP_SYMBOL(left)->rematiCode))
	{
		left = IC_RIGHT(OP_SYMBOL(left)->rematiCode);
		type = operandType(left);
		p_type = DCL_TYPE(type);
	}
	/* now that we have the pointer type we assign
	 the pointer values */
	switch (p_type)
	{
		case POINTER:
		case IPOINTER:
			genNearPointerGet(left, result, ic, pi, ifx);
			break;
		case PPOINTER:
			genPagedPointerGet(left, result, ic, pi, ifx);
			break;
		case FPOINTER:
			genFarPointerGet(left, result, ic, pi, ifx);
			break;
		case CPOINTER:
			genCodePointerGet(left, result, ic, pi, ifx);
			break;
		case GPOINTER:
			genGenPointerGet(left, result, ic, pi, ifx);
			break;
	}
}

/*-----------------------------------------------------------------*/
/* genLiteralAssign - assignment of literal                        */
/*-----------------------------------------------------------------*/
static void genLiteralAssign(operand * result, operand * right, int size,
		bool (*output_fn)(operand * result, const char *s, int offset))
{
	D(printf("%s\n", __FUNCTION__));
}
/*-----------------------------------------------------------------*/
/* dataPut - puts a string for a aop and indicates if acc is in use */
/*-----------------------------------------------------------------*/
static bool litPut(operand * result, char *s, int offset)
{
	return FALSE;
}
/*-----------------------------------------------------------------*/
/* genDataPointerSet - remat pointer to data space                 */
/*-----------------------------------------------------------------*/
static void genDataPointerSet(operand * right, operand * result, iCode * ic)
{
	int size, offset;
	D(emitcode (";", "genDataPointerSet"));
	aopOp(right, ic, FALSE);
	size = max(AOP_SIZE (right), AOP_SIZE (result));
	if ((size > 1) && IS_OP_LITERAL(right))
	{
		genLiteralAssign(result, right, size, litPut);
	}
	else
	{
//remove #
		char *l = Safe_strdup(aopGet(result, 0, FALSE, TRUE) + 1); //remove #
		for (offset = 0; offset < size; offset++)
		{
			struct dbuf_s dbuf;
			dbuf_init(&dbuf, 128);
			if (size > 1)
				dbuf_printf(&dbuf, "(%s + %d)", l, offset);
			else
				dbuf_append_str(&dbuf, l);
//emitcode("mov", "%s,%s", dbuf_c_str(&dbuf), aopGet(right, offset, FALSE, FALSE));
// Aqui ocorre a verificação pra escrita em IO
			if (strstr(dbuf_c_str(&dbuf), "IO"))
			{
				char *str_index, *value = (char*) malloc(10 * sizeof(char));
				str_index = getSubString(dbuf_c_str(&dbuf), "+", ")");
//value = getSubString(aopGet(right, offset, FALSE, FALSE), "#", "\0");
				strcpy(value, aopGet(right, offset, FALSE, FALSE));
//replace(value, "#", "\0");
				int index = (int) strtol(str_index, NULL, 0);
				emitcode("MOV", "R0 , %s", value);
				emitcode("MOV", "IO , (%d), R0", index);
			}
			dbuf_destroy(&dbuf);
		}
		Safe_free(l);
	}
	freeAsmop(right, NULL, ic, TRUE);
	freeAsmop(result, NULL, ic, TRUE);
}


/*
 EX.: receives #(_A + 0x0004) returns (A2_H) or (A2_L)
 */

/*
 recebe #(_A + 0x0002) retorna Ai + offset
 */
char *fVetLitId(char *v, int offset)
{
	char *varName = getVarName(v);
	char *index = getIndex(v);
	int intIndex = (int) strtol(index, NULL, 0);
	char *brq = (char*) malloc(strlen(v)*sizeof(char)+10);
	char *strIndex = (char*) malloc(10 * sizeof(char));
	intIndex += offset;
	sprintf(strIndex, "%d", intIndex);
	strcat(varName, strIndex);
	strcpy(brq, "(");
	strcat(brq, varName);
	return strcat(brq, ")");
}

char *getIndex(char *s)
{
	int intIndex = (int) strtol((strstr(s, ")") ? getSubString(s, "+", ")") : "0"), NULL, 0);
	char *strIndex = (char*) malloc(5 * sizeof(char));
	sprintf(strIndex, "%d", intIndex);
	return strIndex;
}

/*-----------------------------------------------------------------*/
/* genPointerSet - stores the value into a pointer location        */
/*-----------------------------------------------------------------*/
static void genPointerSet(iCode * ic, iCode * pi)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode("\n;", "genPointerSet\n"));
	operand *right, *result;
	
	aopOp(IC_RIGHT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	result = IC_RESULT(ic);
	right = IC_RIGHT(ic);
	
	char *res = Safe_strdup(aopGet(result, 0, FALSE, FALSE));
	char *ri = Safe_strdup(aopGet(right, 0, FALSE, FALSE));

	if (result->isPtr) // IO[i] = ...
	{
		toR0(right, 0);
		emitcode("MOV", "IO (R1) , R0");
		
		return;
	}
	if (!strncmp(res, "#(_IO", 5) || !strncmp(res, "#_IO", 4))
	{
		toR0(right, 0);
		emitcode("MOV", "IO (%s) , R0", getIndex(res));
		return;
	}
	
	sym_link *resType = getSpec(operandType(result));
	
	if (*res == '#') // v[2] = x , v[2] = 0x2233 v[2] = iTemp
	{
		if (!IS_ITEMP(right))
		{
			toR0(right, 0);
			emitcode("MOV", "%s , R0", fVetLitId(res, 0));
			if (IS_CHAR(resType))
				return;
			toR0(right, 1);
			emitcode("MOV", "%s , R0", fVetLitId(res, 1));
		}
		
		else
		{
			emitcode("MOV", "R0 , (%s)", ri);
			emitcode("MOV", "%s , R0", fVetLitId(res, 0));
			if (IS_CHAR(resType))
				return;
			emitcode("INC", "%s", ri);
			emitcode("MOV", "R0 , (%s)", ri);
			emitcode("MOV", "%s , R0", fVetLitId(res, 1));
		}
		return;
	}
	
	if (IS_ITEMP(right))
	{
		if (EQ (res , "R0"))
			emitcode("MOV", "(%s) , (%s)", res, F_OP(right ,0));
		else
			emitcode("MOV", "(%s) , %s", res, F_OP(right ,0));
		
		if (IS_CHAR(resType))
			return;
		
		emitcode("INC", "%s", res);

		if (right->isPtr)
		{
			emitcode("INC", "%s", aopGet(right, 0, FALSE, FALSE));
		}

		if (EQ (res , "R0"))
		{	
			emitcode ("INC" , "%s", F_OP(right ,0));
			emitcode("MOV", "(%s) , (%s)", res,F_OP(right ,0));
		}
		else
			emitcode("MOV", "(%s) , %s", res, F_OP(right ,right->isPtr ? 0 : 1));
	}
	
	else
	{
		if (IS_OP_LITERAL(right))
		{
			emitcode("MVS", "R2 , %s", Safe_strdup(F_OP(right, 0)));
			emitcode("MOV", "(%s) , R2", res);
			
			if (IS_CHAR(resType))
				return;

			emitcode("INC", "%s", res);
			emitcode("MVS", "R2 , %s", Safe_strdup(F_OP(right, 1)));
			emitcode("MOV", "(%s) , R2", res);
		}
		else
		{
			if (result->isPtr == 1)
			{
				emitcode("MOV", "IO (%s) , R0", Safe_strdup(F_OP(right, 0)));
			}
			
			else
			{

				emitcode("MOV", "R2 , %s", F_OP(result, 0));
				emitcode("MOV", "R0 , %s", F_OP(right, 0));
				emitcode("MOV", "(R2) , R0");
				if (IS_CHAR(resType))
					return;
				emitcode("INC", "R2");
				emitcode("MOV", "R0 , %s", Safe_strdup(F_OP(right, 1)));
				emitcode("MOV", "(R2) , R0");
			}
		}
	}
}


/*-----------------------------------------------------------------*/
/* genIfx - generate code for Ifx statement                        */
/*-----------------------------------------------------------------*/
static void genIfx(iCode * ic, iCode * popIc)
{
	operand *cond = IC_COND(ic);
	int isbit = 0;
	char *dup = NULL;
	D(emitcode (";", "genIfx\n"));
	aopOp(cond, ic, FALSE);
	/* get the value into acc */
	if (AOP_TYPE (cond) != AOP_CRY)
	{
		toBoolean(cond);
	}
	else
	{
		isbit = 1;
		if (AOP (cond)->aopu.aop_dir)
			dup = Safe_strdup(AOP (cond)->aopu.aop_dir);
	}
	/* the result is now in the accumulator or a directly addressable bit */
	freeAsmop(cond, NULL, ic, TRUE);
	/* if the condition is a bit variable */
	if (isbit && dup)
		genIfxJump(ic, dup, NULL, NULL, NULL, popIc);
	else if (isbit && IS_OP_ACCUSE(cond))
		genIfxJump(ic, "c", NULL, NULL, NULL, popIc);
	else if (isbit && IS_ITEMP(cond) && SPIL_LOC(cond))
		genIfxJump(ic, SPIL_LOC(cond)->rname, NULL, NULL, NULL, popIc);
	else if (isbit && !IS_ITEMP(cond))
		genIfxJump(ic, OP_SYMBOL(cond)->rname, NULL, NULL, NULL, popIc);
	else
		genIfxJump(ic, "a", NULL, NULL, NULL, popIc);
	if (dup)
		Safe_free(dup);
	ic->generated = 1;
}
/*-----------------------------------------------------------------*/
/* genAddrOf - generates code for address of                       */
/*-----------------------------------------------------------------*/
static void genAddrOf(iCode * ic)
{
	D(printf ("%s\n", __FUNCTION__));
}

/*-----------------------------------------------------------------*/
/* genAssign - generate code for assignment                        */
/*-----------------------------------------------------------------*/
static void genAssign(iCode * ic)
{
	D(printf("%s\n", __FUNCTION__));
	D(emitcode ("\n;", "%s\n", __FUNCTION__));

	operand *result, *right;
	
	aopOp(IC_RIGHT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	result = IC_RESULT(ic);
	right = IC_RIGHT(ic);

	if (operandsEqu(result, right))
	{
		return;
	}
	
	char *res = result->svt.symOperand->name;
	char *ri = right->svt.symOperand->name;
	
	ri = Safe_strdup(aopGet(right, 0, FALSE, FALSE));
	
	if (IS_PARM(right))
	{
		emitcode("MOV", "R0 , %s",F_OP(right,0));
		emitcode("MOV", "%s , R0", F_OP(result,0));
			
		if (AOP_SIZE (result) == 1||AOP_SIZE (right) == 1)
			return;
			
		emitcode("MOV", "R0 , %s", F_OP(right,1));
		emitcode("MOV", "%s , R0", F_OP(result,1));
		return;
	}
	
    if (IS_ITEMP(result))
	{
		res = Safe_strdup(aopGet(result, 0, FALSE, FALSE));
		ri = Safe_strdup(aopGet(right, 0, FALSE, FALSE));
		
		if (IS_OP_LITERAL(right))
		{
			emitcode("MVS", "%s , %s", res, ri);
			//emitcode ("MVS" , "R0 , %s" , ri);
		}
		
		
		if (IS_ITEMP(right) && IS_ITEMP(result) &&AOP_SIZE(result) == 1 && AOP_SIZE(right) == 1
			&& !EQ (res , "R9")) 
		{ 
			emitcode ("MOV" , "%s , (%s)",res , res);		
		}

		if (IS_ITEMP(right) && EQ(res , ri)) 
 		{
			/*
			 auto int tmp = A[i];
			 MOV	R0 , (R7)
			 INC	R7
			 MOV	R8 , (R7)
			 mov r7 , r0

			 */
			emitcode("MOV", "R0 , (%s)", F_OP(right, 0));

			if (AOP_SIZE(result) == 1)
				return;
			emitcode("INC", "%s", ri);
			emitcode("MOV", "%s , (%s)", F_OP(result, 1), ri);
			emitcode("MOV", "%s , R0", F_OP(result, 0));
		}
		
		else
		{
			toR0(right, 0);
			emitcode("MOV", "%s , R0", F_OP(result, 0));
			if (AOP_SIZE (result) == 1)
				return;
			
			toR0(right, 1);
			emitcode("MOV", "%s , R0", F_OP(result, 1));
		}
	}
	
	else
	{
		if (AOP_SIZE (result) == 1 && AOP_SIZE (right) == 1)
		{
			toR0(right, 0);
			emitcode("MOV", "%s , R0", F_OP(result, 0));
			return;
		}
		if (!SPEC_USIGN(operandType(result)) && IS_OP_LITERAL(right) && !IS_PARM(result) && AOP_SIZE (right) == 1 &&
			AOP_SIZE (result) == 2)
		{
			toR0(right, 0);
			emitcode("MOV", "%s , R0", F_OP(result, 0));
			emitcode("AND", "R0 , 0x80");
			emitcode("JZ", "$+3");
			toR0Str("0xFF");
			emitcode("MOV", "%s , R0", F_OP(result, 1));
			emitcode("JMP", "$+3");
			toR0Str("0x00");
			emitcode("MOV", "%s , R0", F_OP(result, 1));
		}
		
		else
		if (!SPEC_USIGN(operandType(result)) && IS_OP_LITERAL(right) && IS_PARM(result))
		{
			toR0(right, 0);
			emitcode("MOV", "%s , R0", F_OP(result, 0));
			
			if (AOP_SIZE (result) == 1)
				return;
			toR0(right, 1);
			emitcode("MOV", "%s , R0", F_OP(result, 1));
		}
		
		else
		{
			toR0(right, 0);
			emitcode("MOV", "%s , R0", F_OP(result, 0));
			if (AOP_SIZE (result) == 1)
				return;
			toR0(right, 1);
			emitcode("MOV", "%s , R0", F_OP(result, 1));
		}
	}
}
/*-----------------------------------------------------------------*/
/* genJumpTab - generates code for jump table                      */
/*-----------------------------------------------------------------*/
static void genJumpTab(iCode * ic)
{
}

/*-----------------------------------------------------------------*/
/* genCast - gen code for casting                                  */
/*-----------------------------------------------------------------*/
static void genCast(iCode * ic)
{
	// result <- (type of left) right
	
	D(printf("genCast\n"));
	D(emitcode (";", "genCast\n"));
	aopOp(IC_RIGHT(ic), ic, FALSE);
	aopOp(IC_RESULT(ic), ic, TRUE);
	operand *right = IC_RIGHT(ic);
	operand *result = IC_RESULT(ic);
	operand *left = IC_LEFT(ic);
	
	if (result->isPtr)
	{
		if (IS_PARM (result))
		{
			if (isVetWithLiteralIndex(right))
			{
				toR0 (right , 0);
				emitcode ("MOV" , "%s , R0", F_OP (result , 0));
			}
			return;
		}
		emitcode("MOV", "R0 , ptr_%s_L", aopGet(right, 0, FALSE, FALSE) + 2);
		emitcode("MOV", "(%s_L) , R0", result->svt.symOperand->name);

		if (AOP_SIZE (result) == 1)
			return;
		emitcode("MOV", "R0 , ptr_%s_H", aopGet(right, 0, FALSE, FALSE) + 2);
		emitcode("MOV", "(%s_H) , R0", result->svt.symOperand->name);
		return;
	}
	
	sym_link *type1 = operandType(right);
	sym_link *type2 = operandType(left);
	int R = type1->select.s.b_unsigned; // 1=unsigned, 0=signed
	int L = type2->select.s.b_unsigned;
	
	bool leftIsUnsigend = SPEC_USIGN(operandType(IC_LEFT(ic)));
	bool rightIsUnsigned = SPEC_USIGN(operandType(IC_RIGHT(ic)));
	

	if (IS_ITEMP(right))
	{
		toR0(right, 0);
		emitcode("MOV", "%s , R0", F_OP(result, 0));
		
		if (AOP_SIZE (result) == 2)
		{
			if (IS_ITEMP(result))
			{
				emitcode("MVS", "%s , 0x00", F_OP(result, 1));
			}
			else
			{
				toR0Str("0x00");
				emitcode("MOV", "%s , R0", F_OP(result, 1));
			}
		}
		
		else
		{
			emitcode("MOV", "%s , R0", F_OP(result, 0));
		}
		return;
	}
	
	if (AOP_SIZE (result) == 1)
	{
		if (IS_ITEMP(result) && IS_ITEMP(right))
		{
			emitcode("MOV", "%s , %s", F_OP(result, 0), F_OP(right, 0));
		}
		else
		{
			toR0(right, 0);
			emitcode("MOV", "%s , R0", F_OP(result, 0));
		}
	}
	
	else // AOP_SIZE (result) = 2 ,  AOP_SIZE (right) = 1
	{
		if (IS_ITEMP(result) && IS_ITEMP(right))
		{
			emitcode("MOV", "%s , %s", F_OP(result, 0), F_OP(right, 0));
		}
		else
		{
			toR0(right, 0);
			emitcode("MOV", "%s , R0", F_OP(result, 0));
		}
		if (IS_ITEMP(result))
		{
			emitcode("MVS", "%s , 0x00", F_OP(result, 1));
		}
		
		else
		{
			if (SPEC_USIGN(operandType(result)))
			{
				toR0Str("0x00");
				emitcode("MOV", "%s , R0", F_OP(result, 1));
			}
			else
			{
				toR0(right, 0);
				emitcode("AND", "R0 , 0x80");
				emitcode("JZ", "$+4");
				toR0Str("0xFF");
				emitcode("MOV", "%s , R0", F_OP(result, 1));
				emitcode("JMP", "$+3");
				toR0Str("0x00");
				emitcode("MOV", "%s , R0", F_OP(result, 1));
			}
		}
	}
}

/*-----------------------------------------------------------------*/
/* genDjnz - generate decrement & jump if not zero instruction     */
/*-----------------------------------------------------------------*/
static int genDjnz(iCode * ic, iCode * ifx)
{
	symbol *lbl, *lbl1;
	D(emitcode(";", "genDjnz\n"));
	if (!ifx)
		return 0;
	/* if the if condition has a false label
	 then we cannot save */
	if (IC_FALSE(ifx))
		return 0;
	/* if the minus is not of the form a = a - 1 */
	if (!isOperandEqual(IC_RESULT(ic), IC_LEFT(ic)) || !IS_OP_LITERAL(IC_RIGHT(ic)))
		return 0;
	if (operandLitValue(IC_RIGHT(ic)) != 1)
		return 0;
	/* if the size of this greater than one then no saving */
	if (getSize(operandType(IC_RESULT(ic))) > 1)
		return 0;
	/* otherwise we can save BIG */
	popForBranch(ic->next, TRUE);
	
	lbl = newiTempLabel(NULL);
	lbl1 = newiTempLabel(NULL);
	aopOp(IC_RESULT(ic), ic, FALSE);

		
	char *reg = aopGet(IC_RESULT(ic), 0, FALSE, FALSE);
		
	// DJNZ works only for R1 , R2 , R3 and R4.
	if (EQ (reg , "R1") || EQ (reg , "R2") || EQ (reg , "R3") || EQ (reg , "R4"))
	{
		emitcode("DJNZ", "%s , !tlabel", reg, labelKey2num(lbl1->key));
	}
	else
	{
		emitcode("DEC", "%s", aopGet(IC_RESULT(ic), 0, FALSE, FALSE));
		emitcode("JZ", "!tlabel", labelKey2num(lbl1->key));
	}
	
	emitLabel(lbl);
	emitcode("JMP", "!tlabel", labelKey2num(IC_TRUE(ifx)->key));
	emitLabel(lbl1);
	if (!ifx->generated)
		freeAsmop(IC_RESULT(ic), NULL, ic, TRUE);
	ifx->generated = 1;
	return 1;
}
/*-----------------------------------------------------------------*/
/* genReceive - generate code for a receive iCode                  */
/*-----------------------------------------------------------------*/
static void genReceive(iCode * ic)
{ 
	D(emitcode("\n;", "genReceive\n"));
	aopOp(IC_RESULT(ic), ic, TRUE);
	assignResultValue(IC_RESULT(ic), NULL);
}
/*-----------------------------------------------------------------*/
/* genDummyRead - generate code for dummy read of volatiles        */
/*-----------------------------------------------------------------*/
static void genDummyRead(iCode * ic)
{
}
/*-----------------------------------------------------------------*/
/* genCritical - generate code for start of a critical sequence    */
/*-----------------------------------------------------------------*/
static void genCritical(iCode * ic)
{
}
/*-----------------------------------------------------------------*/
/* genEndCritical - generate code for end of a critical sequence   */
/*-----------------------------------------------------------------*/
static void genEndCritical(iCode * ic)
{

}
/*-----------------------------------------------------------------*/
/* gen51Code - generate code for ZR16 based controllers            */
/*-----------------------------------------------------------------*/
void genZr16Code(iCode * lic)
{
	iCode *ic;
	int cln = 0;
#ifdef _DEBUG
	int cseq = 0;
#endif
	_G.currentFunc = NULL;
	/* print the allocation information */
//if (allocInfo && currFunc)
//printAllocInfo(currFunc, codeOutBuf);
	/* if debug information required */
	if (options.debug && currFunc)
	{
		debugFile->writeFunction(currFunc, lic);
	}
	/*stack pointer name */
	if (options.useXstack)
		spname = "_spx";
	else
		spname = "sp";
	for (ic = lic; ic; ic = ic->next)
	{
		initGenLineElement();
		genLine.lineElement.ic = ic;
		if (ic->lineno && cln != ic->lineno)
		{
			if (options.debug)
			{
				debugFile->writeCLine(ic);
			}
			if (!options.noCcodeInAsm)
			{
//emitcode(";", "%s:%d: %s", ic->filename, ic->lineno, printCLine(ic->filename, ic->lineno));
			}
			cln = ic->lineno;
		}
#ifdef _DEBUG
		if (ic->seqPoint && ic->seqPoint != cseq)
		{	
//emitcode (";", "sequence point %d", ic->seqPoint);
			cseq = ic->seqPoint;
		}
#endif
		/* if the result is marked as
		 spilt and rematerializable or code for
		 this has already been generated then
		 do nothing */
		if (resultRemat(ic) || ic->generated)
			continue;
		/* depending on the operation */
		switch (ic->op)
		{
			case '!':
				genNot(ic);
				break;
			case '~':
				genCpl(ic);
				break;
			case UNARYMINUS:
				genUminus(ic);
				break;
			case IPUSH:
				genIpush(ic);
				break;
			case IPOP:
			{
				iCode *ifxIc, *popIc;
				bool CommonRegs = FALSE;
				/* IPOP happens only when trying to restore a
				 spilt live range, if there is an ifx statement
				 following this pop (or several) then the if statement might
				 be using some of the registers being popped which
				 would destroy the contents of the register so
				 we need to check for this condition and handle it */
				for (ifxIc = ic->next; ifxIc && ifxIc->op == IPOP; ifxIc = ifxIc->next)
					;
				for (popIc = ic; popIc && popIc->op == IPOP; popIc = popIc->next)
					CommonRegs |= (ifxIc && ifxIc->op == IFX && !ifxIc->generated
							&& regsInCommon(IC_LEFT(popIc), IC_COND(ifxIc)));
				if (CommonRegs)
					genIfx(ifxIc, ic);
				else
					genIpop(ic);
			}
				break;
			case CALL:
				genCall(ic);
				break;
			case PCALL:
				genPcall(ic);
				break;
			case FUNCTION:
				genFunction(ic);
				break;
			case ENDFUNCTION:
				genEndFunction(ic);
				break;
			case RETURN:
				genRet(ic);
				break;
			case LABEL:
				genLabel(ic);
				break;
			case GOTO:
				genGoto(ic);
				break;
			case '+':
				genPlus(ic);
				break;
			case '-':
				if (!genDjnz(ic, ifxForOp(IC_RESULT(ic), ic)))
					genMinus(ic);
				break;
			case '*':
				genMult(ic);
				break;
			case '/':
				genDiv(ic);
				break;
			case '%':
				genMod(ic);
				break;
			case '>':
				genCmpGt(ic, ifxForOp(IC_RESULT(ic), ic));
				break;
			case '<':
				genCmpLt(ic, ifxForOp(IC_RESULT(ic), ic));
				break;
			case LE_OP:
			case GE_OP:
			case NE_OP:
				/* note these two are xlated by algebraic equivalence
				 in decorateType() in SDCCast.c */
				werror(E_INTERNAL_ERROR, __FILE__, __LINE__, "got '>=' or '<=' shouldn't have come here");
				break;
			case EQ_OP:
				genCmpEq(ic, ifxForOp(IC_RESULT(ic), ic));
				break;
			case AND_OP:
				genAndOp(ic);
				break;
			case OR_OP:
				genOrOp(ic);
				break;
			case '^':
				genXor(ic, ifxForOp(IC_RESULT(ic), ic));
				break;
			case '|':
				genOr(ic, ifxForOp(IC_RESULT(ic), ic));
				break;
			case BITWISEAND:
				genAnd(ic, ifxForOp(IC_RESULT(ic), ic));
				break;
			case INLINEASM:
				genInline(ic);
				break;
			case RRC:
				genRRC(ic);
				break;
			case RLC:
				genRLC(ic);
				break;
			case GETHBIT:
				assert(0);
				break;
			case GETABIT:
				genGetAbit(ic);
				break;
			case GETBYTE:
				genGetByte(ic);
				break;
			case GETWORD:
				genGetWord(ic);
				break;
			case LEFT_OP:
				genLeftShift(ic);
				break;
			case RIGHT_OP:
				genRightShift(ic);
				break;
			case GET_VALUE_AT_ADDRESS:
				genPointerGet(ic, hasInc(IC_LEFT(ic), ic, getSize(operandType(IC_RESULT(ic)))),
						ifxForOp(IC_RESULT(ic), ic));
				break;
			case '=':
				if (POINTER_SET(ic))
					genPointerSet(ic, hasInc(IC_RESULT(ic), ic, getSize(operandType(IC_RIGHT(ic)))));
				else
					genAssign(ic);
				break;
			case IFX:
				genIfx(ic, NULL);
				break;
			case ADDRESS_OF:
				genAddrOf(ic);
				break;
			case JUMPTABLE:
				genJumpTab(ic);
				break;
			case CAST:
				genCast(ic);
				break;
			case RECEIVE:
				genReceive(ic);
				break;
			case SEND:
				addSet(&_G.sendSet, ic);
				break;
			case DUMMY_READ_VOLATILE:
				genDummyRead(ic);
				break;
			case CRITICAL:
				genCritical(ic);
				break;
			case ENDCRITICAL:
				genEndCritical(ic);
				break;
			case SWAP:
				genSwap(ic);
				break;
			default:
				ic = ic;
		}
	}
	
	if (mulWasGenerated)
	{
		mulWasGenerated = false;
		genZr16Mult();
	}
	
	if (divWasGenerated)
	{
		divWasGenerated = false;
		genZr16Div();
	}

	if (ISRWasGenerated)
	{
		ISRWasGenerated = false;
		emitcode ("ORG" , "0x3C0");
		emitcode("JMP" , "%s", ISRname); 	
	}

	genLine.lineElement.ic = NULL;
	/* now we are ready to call the
	 peep hole optimizer */
	if (!options.nopeep)
	{
		peepHole(&genLine.lineHead);
	}
	/* now do the actual printing */
	printLine(genLine.lineHead, codeOutBuf);
	/* destroy the line list */
	destroy_line_list();
}

