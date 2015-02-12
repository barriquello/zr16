/*-------------------------------------------------------------------------
  rtrack.c - tracking content of registers on an zr16

  Copyright 2007 Frieder Ferlemann (Frieder Ferlemann AT web.de)

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301 USA
-------------------------------------------------------------------------*/

/*-------------------------------------------------------------------------
  Status:
    - passes regression test suite, still bugs are likely
    - only active if environment variable SDCC_REGTRACK is set

  Missed opportunities:
    - does not track offsets to symbols as in "mov dptr,#(_my_int + 2)"
    - only used for moves to acc or dptr so chances to use:
      "inc r2", "mov r2,a" would not be taken
    - a label causes loss of tracking (no handling of information of blocks
      known to follow/preceed the current block)
    - not used in aopGet or genRet
    - SFRX (__xdata volatile unsigned char __at(addr)) not handled as value
    - does not track which registers are known to be unchanged within
      a function (would not have to be saved when calling the function)
-------------------------------------------------------------------------*/


#include <stdio.h>
#include <string.h>
#include "SDCCglobl.h"

#include "common.h"
#include "ralloc.h"
#include "gen.h"
#include "rtrack.h"


#define D(x)  do if (options.verboseAsm) {x;} while(0)
#define DD(x) do if (options.verboseAsm && enableextraverbose) {x;} while(0)


/* move this (or zr16_rtrackGetLit() and zr16_rtrackMoveALit()
   elsewhere? stealing emitcode from gen.c */
void emitcode (const char *inst, const char *fmt,...);


static int enable = +1;
static int enableextraverbose = -1;


static unsigned int rx_num_to_idx (const unsigned int num)
{
  const unsigned int regidx[8] =
    { R7_IDX, R6_IDX, R5_IDX, R4_IDX, R3_IDX, R2_IDX, R1_IDX, R0_IDX };

  assert( 7 >= num );

  return regidx [num & 0x7];
}


static void rtrack_data_unset (const unsigned int idx)
{
  assert (idx >= 0);
  assert (idx < END_IDX);

  if (regsZR16[idx].rtrack.symbol || regsZR16[idx].rtrack.valueKnown)
    {
      DD(emitcode (";", "\t%s=?", regsZR16[idx].name););
    }

  if (regsZR16[idx].rtrack.symbol)
    {
      Safe_free (regsZR16[idx].rtrack.symbol);
    }

  memset (&regsZR16[idx].rtrack, 0, sizeof regsZR16[idx].rtrack);
}


static void rtrack_data_set_val (const unsigned int idx, const unsigned char value)
{
  assert (idx >= 0);
  assert (idx < END_IDX);

  regsZR16[idx].rtrack.value = value;
  regsZR16[idx].rtrack.valueKnown = 1;

  /* in case it was set by symbol, unset symbol */
  if (regsZR16[idx].rtrack.symbol)
    {
      Safe_free (regsZR16[idx].rtrack.symbol);
      regsZR16[idx].rtrack.symbol = NULL;
    }

  DD(emitcode (";", "\t%s=#0x%02x",
                    regsZR16[idx].name,
                    regsZR16[idx].rtrack.value););
}


static void rtrack_data_set_symbol (const unsigned int idx, const char * const symbol)
{
  assert (idx >= 0);
  assert (idx < END_IDX);

  /* in case it was set by value, unset value */
  regsZR16[idx].rtrack.value = 0;
  regsZR16[idx].rtrack.valueKnown = 0;

  /* eventually free a previous symbol */
  if (regsZR16[idx].rtrack.symbol)
    {
      Safe_free (regsZR16[idx].rtrack.symbol);
    }
  regsZR16[idx].rtrack.symbol = Safe_strdup(symbol);

  DD(emitcode (";", "\t%s=#%s",
                    regsZR16[idx].name,
                    regsZR16[idx].rtrack.symbol););
}


static int rtrack_data_is_same (const unsigned int idxdst, const unsigned int idxsrc)
{
  return ((regsZR16[idxdst].rtrack.valueKnown && regsZR16[idxsrc].rtrack.valueKnown) &&
          (regsZR16[idxdst].rtrack.value      == regsZR16[idxsrc].rtrack.value)) ||
         ((regsZR16[idxdst].rtrack.symbol && regsZR16[idxsrc].rtrack.symbol) &&
         !strcmp (regsZR16[idxdst].rtrack.symbol, regsZR16[idxsrc].rtrack.symbol));
}


static void rtrack_data_copy_dst_src (const unsigned int idxdst, const unsigned int idxsrc)
{
  assert (idxdst >= 0);
  assert (idxdst < END_IDX);
  assert (idxsrc >= 0);
  assert (idxsrc < END_IDX);

  DD
  (
    if ((NULL != regsZR16[idxsrc].rtrack.symbol) || regsZR16[idxsrc].rtrack.valueKnown)
      {
        emitcode (";", "\t%s=%s", regsZR16[idxdst].name, regsZR16[idxsrc].name);
      }
    else if (regsZR16[idxdst].rtrack.symbol || regsZR16[idxdst].rtrack.valueKnown)
      {
        emitcode (";", "\t%s=*",regsZR16[idxdst].name);
      }

    if (rtrack_data_is_same (idxdst, idxsrc))
      {
        emitcode (";", "genFromRTrack redundant?");
      }
  );

  /* mov a, acc */
  if (idxsrc == idxdst)
    return;

  regsZR16[idxdst].rtrack.valueKnown = regsZR16[idxsrc].rtrack.valueKnown;
  regsZR16[idxdst].rtrack.value      = regsZR16[idxsrc].rtrack.value;

  if (regsZR16[idxdst].rtrack.symbol)
    {
      Safe_free (regsZR16[idxdst].rtrack.symbol);
      regsZR16[idxdst].rtrack.symbol = NULL;
    }

  memcpy (&regsZR16[idxdst].rtrack, &regsZR16[idxsrc].rtrack, sizeof regsZR16[idxdst].rtrack);

  if (regsZR16[idxsrc].rtrack.symbol)
    {
      regsZR16[idxdst].rtrack.symbol = Safe_strdup(regsZR16[idxsrc].rtrack.symbol);
    }
}


static void dumpAll()
{
  DD
  (
    unsigned int i;
    unsigned int column = 0;
    char s[512];

    s[0] = 0;
    for (i = 0; i < END_IDX; i++)
      {
        if (regsZR16[i].rtrack.valueKnown)
          {
            column += sprintf(s + column, "%s%s:#0x%02x",
                              column?" ":"", regsZR16[i].name, regsZR16[i].rtrack.value);
          }
        if (NULL != regsZR16[i].rtrack.symbol)
          {
            column += sprintf(s + column, "%s%s:#%s",
                              column?" ":"", regsZR16[i].name, regsZR16[i].rtrack.symbol);
          }
        if (column>160)
          {
            strcpy (&s[157], "...");
            break;
          }
      }
    emitcode (";", "\t%s", s);
  );
}


static void invalidateAllRx()
{
  unsigned int i;
  for (i = 0; i <= 7; i++)
    {
      rtrack_data_unset (rx_num_to_idx (i));
    }
}


static void invalidateAll()
{
  invalidateAllRx();

  rtrack_data_unset (DPL_IDX);
  rtrack_data_unset (DPH_IDX);
  rtrack_data_unset (B_IDX);
  rtrack_data_unset (A_IDX);
}


static int regidxfromregname (const char* const s)
{
  unsigned int i;

  for (i = 0; i < END_IDX; i++)
    {
       if (regsZR16[i].name)
         if (!strncmp (s, regsZR16[i].name, strlen(regsZR16[i].name)))
            return i;

       if (regsZR16[i].dname)
         if (!strncmp (s, regsZR16[i].dname, strlen(regsZR16[i].dname)))
            return i;
    }

  return -1;
}


static int valuefromliteral (const char* const s)
{
  char* tmp = NULL;
  int value;

  if (strncmp (s, "0x", 2))
    return -1;

  value = strtol (s + 2, &tmp, 16);
  if (s != tmp)
    return value;

  return -1;
}


/* tracking values within registers by looking
   at the line passed to the assembler.
   Tries to keep regsZR16[] up to date */
bool _zr16_rtrackUpdate (const char *line)
{
  bool modified = false;

  if (enable == -1)
    enable = (NULL != getenv("SDCC_REGTRACK"));

  if (enableextraverbose == -1)
    enableextraverbose = (NULL != getenv("SDCC_REGTRACK_VERBOSE"));

  if (!enable ||
      *line == ';' ||                 /* comment */
      (NULL != strstr( line, "==."))) /* dirty check for _G.debugLine */
    return false;                     /* nothing to do */

  dumpAll ();

  if (!strncmp (line, "mov", 3))
    {
      if (!strncmp (line, "movc\ta", 6) ||
          !strncmp (line, "movx\ta", 6))
        {
          rtrack_data_unset (A_IDX);
          return false;
        }

      /* mov to register (r0..r7, dpl, dph, a, b)*/
      if (!strncmp (line, "mov\t", 4))
        {
          int regIdx = regidxfromregname (line + 4);

          if (0 <= regIdx)
            {
              char *argument = strstr (line, ",") + 1;
              char *s;
              int value;

              value = strtol (argument + 1, &s, 16);

              /* check literal mov to register */
              if ((s != argument + 1) && !strncmp (argument, "#0x", 3))
                {
                  D
                  (
                    if (regsZR16[regIdx].rtrack.valueKnown && (value == regsZR16[regIdx].rtrack.value))
                      {
                        emitcode (";", "genFromRTrack removed\t%s", line);
                        modified = true;
                      }
                    if (regsZR16[A_IDX].rtrack.valueKnown && (value == regsZR16[A_IDX].rtrack.value) &&
                        (regIdx != A_IDX) && (regIdx != DPL_IDX) && (regIdx != DPH_IDX))
                        /* ignore DPL/DPH for now as peephole rule for MOV DPTR is much better */
                      {
                        emitcode (";", "genFromRTrack replaced\t%s", line);
                        emitcode ("mov", "%s,a", regsZR16[regIdx].name);
                        modified = true;
                      }
                    else if (regsZR16[regIdx].rtrack.valueKnown && (value == regsZR16[regIdx].rtrack.value + 1) &&
                             ((regIdx != A_IDX) || (0xff != regsZR16[regIdx].rtrack.value)))
                      {
                        /* does not occur in regression test zr16-small */
                        emitcode (";", "genFromRTrack replaced\t%s", line);
                        emitcode ("inc", "%s", regsZR16[regIdx].name);
                        modified = true;
                      }
                    else if (regsZR16[regIdx].rtrack.valueKnown && (value == regsZR16[regIdx].rtrack.value - 1) &&
                             ((regIdx != A_IDX) || (0x01 != regsZR16[regIdx].rtrack.value)))
                      {
                        /* does not occur in regression test zr16-small */
                        emitcode (";", "genFromRTrack replaced\t%s", line);
                        emitcode ("dec", "%s", regsZR16[regIdx].name);
                        modified = true;
                      }
                  );

                  rtrack_data_set_val (regIdx, (unsigned char) value);
                }
              /* check literal mov of symbol to register */
              else if (!strncmp (argument, "#", 1))
                {
                  rtrack_data_set_symbol (regIdx, argument + 1);
                }
              /* check mov from register to register */
              else if (0 <= regidxfromregname (argument))
                {
                  rtrack_data_copy_dst_src (regIdx, regidxfromregname (argument));
                }
              else
                {
                  /* mov acc.7,c and the likes */
                  rtrack_data_unset (regIdx);
                }
              return modified;
            }
        }

      /* mov to psw can change register bank */
      if (!strncmp (line, "mov\tpsw,", 8))
        {
          invalidateAllRx ();
          return false;
        }

      /* tracking dptr */
      /* literal number 16 bit */
      if (!strncmp (line, "mov\tdptr,#0x", 12))
        {
          char* s;
          int value = strtol (line + 10, &s, 16);
          if( s != line + 10 )
            {
              if (options.verboseAsm)
                {
                  bool foundshortcut = 0;

                  if ( regsZR16[DPH_IDX].rtrack.valueKnown &&
                       regsZR16[DPL_IDX].rtrack.valueKnown &&
                      (regsZR16[DPH_IDX].rtrack.value == (value >> 8)) &&
                      (regsZR16[DPL_IDX].rtrack.value == (value & 0xff)))
                    {
                      emitcode (";", "genFromRTrack removed\t%s", line);
                      foundshortcut = 1;
                      modified = true;
                    }

                  if (!foundshortcut &&
                       regsZR16[DPH_IDX].rtrack.valueKnown &&
                       regsZR16[DPL_IDX].rtrack.valueKnown)
                    {
                      /* some instructions are shorter than mov dptr,#0xabcd */
                      const struct
                        {
                           int offset;
                           const char* inst;
                           const char* parm;
                        } reachable[6] =
                        {
                          {   1, "inc", "dptr"},
                          { 256, "inc", "dph"},
                          {-256, "dec", "dph"},
                          {-255, "inc", "dpl"},    /* if overflow */
                          {  -1, "dec", "dpl"},    /* if no overflow */
                          { 255, "dec", "dpl"}     /* if overflow */
                        };

                       unsigned int dptr = (regsZR16[DPH_IDX].rtrack.value << 8 ) |
                                            regsZR16[DPL_IDX].rtrack.value;
                       unsigned int i;

                       for (i = 0; i < 6; i++)
                         {
                           if (dptr + reachable[i].offset == value)
                             {
                                /* check if an overflow would occur */
                                if ((i == 3) && ((dptr & 0xff) != 0xff)) continue;
                                if ((i == 4) && ((dptr & 0xff) == 0x00)) continue;
                                if ((i == 5) && ((dptr & 0xff) != 0x00)) continue;

                                /* does not occur in regression test zr16-small */
                                emitcode (";", "genFromRTrack replaced\t%s", line);
                                emitcode (reachable[i].inst, "%s", reachable[i].parm);
                                modified = true;
                                foundshortcut = 1;

                                break;
                             }
                         };
                    }

                  if (!foundshortcut &&
                       regsZR16[DPH_IDX].rtrack.valueKnown &&
                      (regsZR16[DPH_IDX].rtrack.value == (value >> 8)))
                    {
                      char s[32];
                      sprintf (s, "#0x%02x", value & 0xff);

                      if (s != zr16_rtrackGetLit(s))
                        {
                          /* does not occur in regression test zr16-small */
                          emitcode (";", "genFromRTrack replaced\t%s", line);
                          emitcode ("mov", "dpl,%s", zr16_rtrackGetLit (s));
                          modified = true;
                          foundshortcut = 1;
                        }
                    }
                  if (!foundshortcut &&
                       regsZR16[DPL_IDX].rtrack.valueKnown &&
                      (regsZR16[DPL_IDX].rtrack.value == (value & 0xff)))
                    {
                      char s[32];
                      sprintf (s, "#0x%02x", value >> 8);

                      if (s != zr16_rtrackGetLit (s))
                        {
                          /* does not occur in regression test zr16-small */
                          emitcode (";", "genFromRTrack replaced\t%s", line);
                          emitcode ("mov", "dph,%s", zr16_rtrackGetLit (s));
                          modified = true;
                          foundshortcut = 1;
                        }
                    }
                }

              rtrack_data_set_val (DPH_IDX, (unsigned char) (value >> 8));
              rtrack_data_set_val (DPL_IDX, (unsigned char) value);
              return modified;
            }
        }
      /* literal symbol 16 bit */
      else if (!strncmp (line, "mov\tdptr,#", 10))
        {
          char* s = Safe_alloc (strlen (line) + strlen ("( >> 8)"));

          strcat (s, "(");
          strcat (s, &line[10]);
          strcat (s, " >> 8)");

          rtrack_data_set_symbol (DPH_IDX, s);
          rtrack_data_set_symbol (DPL_IDX, &line[10]);

          Safe_free (s);
          return false;
        }
      else if (!strncmp (line, "mov\tdptr", 8))
        {
          /* unidentified */
          rtrack_data_unset (DPH_IDX);
          rtrack_data_unset (DPL_IDX);
          return false;
        }

      /* move direct to symbol */
      if (!strncmp (line, "mov\t_", 5) ||
          !strncmp (line, "mov\t(", 5))
        {
          char* argument = strstr (line, ",") + 1;

          if (argument && !strncmp (argument, "#0x", 3))
            {
              char s[8] = {0};

              strncpy ((void *)&s, argument, strlen ("#0xab"));

              /* could we get it from a, r0..r7? */
              if (s != zr16_rtrackGetLit (s))
                {
                  int lengthuptoargument = argument - (line + 4);
                  emitcode (";", "1-genFromRTrack replaced\t%s", line);
                  emitcode ("mov", "%.*s%s",
                                  lengthuptoargument,
                                  line + 4,
                                  zr16_rtrackGetLit (s));
                  modified = true;
                }
          }
          return modified;
        }

      /* no tracking of SP, so we do not care */
      if (!strncmp (line, "mov\tsp,", 7))
        return false;

      /* mov to xdata or pdata memory does not change registers */
      if (!strncmp (line, "movx\t@", 6))
        return false;

      /* mov to idata memory might change registers r0..r7
         but unless there is a stack problem
         compiler generated code does not do idata
         writes to 0x00..0x1f? */
      if (!strncmp (line, "mov\t@", 5))
        {
          /* a little too paranoid? */
          invalidateAllRx ();
          return false;
        }
    }

  /* no tracking of SP */
  if (!strncmp (line, "push", 4))
    return false;

  if (!strncmp (line, "pop\t", 4))
    {
      int regIdx = regidxfromregname (line + 4);
      if (0 <= regIdx)
        {
          rtrack_data_unset (regIdx);
        }
      return false;
    }

  if (!strncmp (line, "inc", 3))
    {
      if (!strcmp (line, "inc\tdptr"))
        {
          if (regsZR16[DPH_IDX].rtrack.valueKnown &&
              regsZR16[DPL_IDX].rtrack.valueKnown)
            {
              int val = (regsZR16[DPH_IDX].rtrack.value << 8) | regsZR16[DPL_IDX].rtrack.value;
              val += 1;
              rtrack_data_set_val (DPL_IDX, (unsigned char) val);
              rtrack_data_set_val (DPH_IDX, (unsigned char) (val >> 8));
            }
          else
            {
              /* not yet handling offset to a symbol. Invalidating. So no inc dptr for:
                 __xdata char array[4]; array[0] = 0; array[1] = 0; array[2] = 0;
                 (If an offset to the respective linker segment would be
                 available then additionally
                 __xdata int a = 123; __xdata int b = 456; __xdata c= 'a';
                 could be 4 bytes shorter) */
              rtrack_data_unset (DPL_IDX);
              rtrack_data_unset (DPH_IDX);
            }
          return false;
        }
      if (!strncmp (line, "inc\t", 4))
        {
          int regIdx = regidxfromregname (line + 4);
          if (0 <= regIdx)
            {
              if (regsZR16[regIdx].rtrack.valueKnown)
                rtrack_data_set_val (regIdx, (unsigned char) (regsZR16[regIdx].rtrack.value + 1));
              else
                /* explicitely unsetting (could be known by symbol).
                   not yet handling offset to a symbol. (idata/pdata) */
                rtrack_data_unset (regIdx);

              return false;
            }
        }
      return false;
    }

  /* some bit in acc is cleared
     MB: I'm too lazy to find out which right now */
  if (!strncmp (line, "jbc\tacc", 7))
    {
      rtrack_data_unset (A_IDX);
      return false;
    }

  /* unfortunately the label typically following these
     will cause loss of tracking */
  if (!strncmp (line, "jc\t", 3) ||
      !strncmp (line, "jnc\t", 4) ||
      !strncmp (line, "jb\t", 3) ||
      !strncmp (line, "jnb\t", 4) ||
      !strncmp (line, "jbc\t", 4))
    return false;

  /* if branch not taken in "cjne r2,#0x08,somewhere" 
     r2 is known to be 8 */
  if (!strncmp (line, "cjne\t", 5))
    {
      int regIdx = regidxfromregname (line + 5);
      if (0 <= regIdx)
        {
          char *argument = strstr (line, ",") + 1;
          char *s;
          int value;

          value = strtol (argument + 1, &s, 16);

          /* check literal compare to register */
          if ((s != argument + 1) && !strncmp (argument, "#0x", 3))
            {
               rtrack_data_set_val (regIdx, (unsigned char) value);
               return false;
            }
          rtrack_data_unset (regIdx);
        }
      return false;
    }

  /* acc eventually known to be zero */
  if (!strncmp (line, "jz\t", 3))
    return false;

  /* acc eventually known to be zero */
  if (!strncmp (line, "jnz\t", 4))
    {
      rtrack_data_set_val (A_IDX, 0x00); // branch not taken
      return false;
    }

  if (!strncmp (line, "djnz\t", 5))
    {
      int regIdx = regidxfromregname (line + 5);
      if (0 <= regIdx)
        {
          rtrack_data_set_val (regIdx, 0x00); // branch not taken
          return false;
        }
    }

  /* only carry bit, so we do not care */
  if (!strncmp (line, "setb\tc", 6) ||
      !strncmp (line, "clr\tc", 5) ||
      !strncmp (line, "cpl\tc", 5))
    return false;

  /* operations on acc which depend on PSW */
  if (!strncmp (line, "addc\ta,", 7)||
      !strncmp (line, "subb\ta,", 7)||
      !strncmp (line, "da\ta", 4)   ||
      !strncmp (line, "rlc\ta", 5) ||
      !strncmp (line, "rrc\ta", 5))
    {
      rtrack_data_unset (A_IDX);
      return false;
    }

  /* bitwise operations on acc */
  if (!strncmp (line, "setb\ta", 6) ||
      !strncmp (line, "clrb\ta", 6))
    {
      rtrack_data_unset (A_IDX);
      return false;
    }

  /* other operations on acc that can be tracked */
  if (!strncmp (line, "add\ta,", 6) ||
      !strncmp (line, "anl\ta,", 6) ||
      !strncmp (line, "orl\ta,", 6) ||
      !strncmp (line, "xrl\ta,", 6) ||
      !strcmp (line, "cpl\ta"))
    {
      if (regsZR16[A_IDX].rtrack.valueKnown)
        {
          if (!strncmp (line, "add\ta,", 6))
            {
              int regIdx = regidxfromregname (line + 6);

              if (0 <= regIdx && regsZR16[regIdx].rtrack.valueKnown)
                {
                  rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value + regsZR16[regIdx].rtrack.value));
                  return false;
                }
              else if (('#' == line[6]) && (0 <= valuefromliteral (line + 7)))
                {
                  rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value + valuefromliteral (line + 7)));
                  return false;
                }
            }

          if (!strncmp (line, "anl\ta,", 6))
            {
              int regIdx = regidxfromregname (line + 6);

              if (0 <= regIdx && regsZR16[regIdx].rtrack.valueKnown)
                {
                  rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value & regsZR16[regIdx].rtrack.value));
                  return false;
                }
              else if (('#' == line[6]) && (0 <= valuefromliteral (line + 7)))
                {
                  rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value & valuefromliteral (line + 7)));
                  return false;
                }
            }

          if (!strncmp (line, "orl\ta,", 6))
            {
              int regIdx = regidxfromregname (line + 6);

              if (0 <= regIdx && regsZR16[regIdx].rtrack.valueKnown)
                {
                  rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value | regsZR16[regIdx].rtrack.value));
                  return false;
                }
              else if (('#' == line[6]) && (0 <= valuefromliteral (line + 7)))
                {
                  rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value | valuefromliteral (line + 7)));
                  return false;
                }
            }

          if (!strncmp (line, "xrl\ta,", 6))
            {
              int regIdx = regidxfromregname (line + 6);

              if (0 <= regIdx && regsZR16[regIdx].rtrack.valueKnown)
                {
                  rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value ^ regsZR16[regIdx].rtrack.value));
                  return false;
                }
              else if (('#' == line[6]) && (0 <= valuefromliteral (line + 7)))
                {
                  rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value ^ valuefromliteral (line + 7)));
                  return false;
                }
            }

          if (!strcmp (line, "cpl\ta"))
            {
              rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value ^ 0xff));
              return false;
            }

          rtrack_data_unset (A_IDX);
          return false;
        }
      else
        {
          rtrack_data_unset (A_IDX);
          return false;
        }
    }

  if (!strncmp (line, "dec\t", 4))
    {
      int regIdx = regidxfromregname (line + 4);
      if (0 <= regIdx)
        {
          if (regsZR16[regIdx].rtrack.valueKnown)
            rtrack_data_set_val (regIdx, (unsigned char) (regsZR16[regIdx].rtrack.value - 1));

          /* not handling offset to a symbol. invalidating if needed */
          if (NULL != regsZR16[regIdx].rtrack.symbol)
            rtrack_data_unset (regIdx);

          return false;
        }
      return false;
    }

  if (!strcmp (line, "clr\ta"))
    {
      if (regsZR16[A_IDX].rtrack.valueKnown && (0 == regsZR16[A_IDX].rtrack.value))
        {
          emitcode (";", "genFromRTrack removed\t%s", line);
          modified = true;
        }
      rtrack_data_set_val (A_IDX, 0);
      return modified;
    }

  if (!strcmp (line, "cpl\ta"))
    {
      if (regsZR16[A_IDX].rtrack.valueKnown)
        rtrack_data_set_val (A_IDX, (unsigned char) (~regsZR16[A_IDX].rtrack.value));
      else
        /* in case a holds a symbol */
        rtrack_data_unset (A_IDX);
      return false;
    }
  if (!strcmp (line, "rl\ta"))
    {
      if (regsZR16[A_IDX].rtrack.valueKnown)
        rtrack_data_set_val (A_IDX, (unsigned char) ((regsZR16[A_IDX].rtrack.value<<1) |
                                    (regsZR16[A_IDX].rtrack.value>>7)));
      else
        rtrack_data_unset (A_IDX);
      return false;
    }
  if (!strcmp (line, "rr\ta"))
    {
      if (regsZR16[A_IDX].rtrack.valueKnown)
        rtrack_data_set_val (A_IDX, (unsigned char) ((regsZR16[A_IDX].rtrack.value>>1) |
                                    (regsZR16[A_IDX].rtrack.value<<7)));
      else
        rtrack_data_unset (A_IDX);
      return false;
    }
  if (!strcmp (line, "swap\ta"))
    {
      if (regsZR16[A_IDX].rtrack.valueKnown)
        rtrack_data_set_val (A_IDX, (unsigned char) ((regsZR16[A_IDX].rtrack.value>>4) |
                                    (regsZR16[A_IDX].rtrack.value<<4)));
      else
        rtrack_data_unset (A_IDX);
      return false;
    }

  if (!strncmp (line, "mul\t", 4))
    {
      if (regsZR16[A_IDX].rtrack.valueKnown && regsZR16[B_IDX].rtrack.valueKnown)
        {
           unsigned int value = (unsigned int)regsZR16[A_IDX].rtrack.value *
                                (unsigned int)regsZR16[B_IDX].rtrack.value;

           rtrack_data_set_val (A_IDX, (unsigned char) value);
           rtrack_data_set_val (B_IDX, (unsigned char) (value >> 8));
        }
      else
        {
          rtrack_data_unset (A_IDX);
          rtrack_data_unset (B_IDX);
        }
      return false;
    }

  if (!strncmp (line, "div\t", 4))
    {
      if (regsZR16[A_IDX].rtrack.valueKnown && regsZR16[B_IDX].rtrack.valueKnown)
        {
           rtrack_data_set_val (A_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value / regsZR16[B_IDX].rtrack.value));
           rtrack_data_set_val (B_IDX, (unsigned char) (regsZR16[A_IDX].rtrack.value % regsZR16[B_IDX].rtrack.value));
        }
      else
        {
          rtrack_data_unset (A_IDX);
          rtrack_data_unset (B_IDX);
        }
      return false;
    }

  /* assuming these library functions have no side-effects */
  if (!strncmp (line, "lcall", 5))
    {
      if (!strcmp (line, "lcall\t__gptrput"))
        {
          /* invalidate R0..R7 because they might have been changed */
          /* MB: too paranoid ? */
          //invalidateAllRx();
          return false;
        }
      if (!strcmp (line, "lcall\t__gptrget"))
        {
          rtrack_data_unset (A_IDX);
          return false;
        }
      if (!strcmp (line, "lcall\t__decdptr"))
        {
          if (regsZR16[DPH_IDX].rtrack.valueKnown &&
              regsZR16[DPL_IDX].rtrack.valueKnown)
            {
              int val = (regsZR16[DPH_IDX].rtrack.value << 8) | regsZR16[DPL_IDX].rtrack.value;
              val -= 1;
              rtrack_data_set_val (DPL_IDX, (unsigned char) val);
              rtrack_data_set_val (DPH_IDX, (unsigned char) (val >> 8));
            }
          else
            {
              rtrack_data_unset (DPL_IDX);
              rtrack_data_unset (DPH_IDX);
            }
          return false;
        }
       /* if callee_saves */
     }

  if (!strncmp (line, "xch\ta,", 6))
    {
      /* handle xch from register (r0..r7, dpl, dph, b) */
      int regIdx = regidxfromregname (line + 6);
      if (0 <= regIdx)
        {
          void* swap = Safe_malloc (sizeof regsZR16[A_IDX].rtrack);

          memcpy (swap,                     &regsZR16[A_IDX].rtrack,  sizeof regsZR16[A_IDX].rtrack);
          memcpy (&regsZR16[A_IDX ].rtrack, &regsZR16[regIdx].rtrack, sizeof regsZR16[A_IDX].rtrack);
          memcpy (&regsZR16[regIdx].rtrack, swap,                     sizeof regsZR16[A_IDX].rtrack);

          Safe_free (swap);
          return false;
        }
    }

  /* all others unrecognized, invalidate */
  invalidateAll();
  return false;
}


/* expects f.e. "#0x01" and returns either "#0x01"
   if the value is not known to be within registers
   or "a" or "r0".."r7".
   (mov a,r7 or add a,r7 need one byte whereas
    mov a,#0x01 or add a,#0x01 would take two
 */
char * zr16_rtrackGetLit(const char *x)
{
  unsigned int i;

  char *s;

  if (enable != 1)
    return (char *)x;

  /* was it a numerical literal? */
  if (*x == '#')
    {
      int val = strtol (x+1, &s, 16);
      if (x+1 != s)
        {
          /* try to get from acc */
          reg_info *r = &regsZR16[A_IDX];
          if (r->rtrack.valueKnown &&
              r->rtrack.value == val)
            {
              D(emitcode (";", "genFromRTrack 0x%02x==%s", val, r->name));
              return r->name;
            }
          /* try to get from register R0..R7 */
          for (i = 0; i < 8; i++)
            {
              reg_info *r = &regsZR16[rx_num_to_idx(i)];
              if (r->rtrack.valueKnown &&
                  r->rtrack.value == val)
                {
                  D(emitcode (";", "genFromRTrack 0x%02x==%s", val, r->name));
                  return r->name;
                }
            }
        }
      else
        {
          /* probably a symbolic literal as in "mov r3,#(_i+1)",
             not handled... */
        }
    }

  return (char *)x;
}

/* Similar to the above function 
   As the destination is the accumulator try harder yet and
   try to generate the result with arithmetic operations */
int zr16_rtrackMoveALit (const char *x)
{

  if (enable != 1)
    return 0;

  /* if it is a literal mov try to get it cheaper */
  if ( *x == '#' )
    {
      reg_info *a = &regsZR16[A_IDX];

      char *s;
      int val = strtol (x+1, &s, 16);

      /* was it a numerical literal? */
      if (x+1 != s)
        {
          /* prefer mov a,#0x00 */
          if (val == 0 &&
              ((a->rtrack.valueKnown && a->rtrack.value != 0) ||
               !a->rtrack.valueKnown))
            {
              /* peepholes convert to clr a */
              /* (regression test suite is slightly larger if "clr a" is used here) */
              emitcode ("MOV", "a , 0x00");
              return 1;
            }

          if (a->rtrack.valueKnown)
            {
              /* already there? */
              if (val == a->rtrack.value)
                {
                  D(emitcode (";", "genFromRTrack acc==0x%02x", a->rtrack.value));
                  return 1;
                }

              /* can be calculated with an instruction
                 that does not change flags from acc itself? */
              if (val == ((a->rtrack.value+1) & 0xff) )
                {
                  D(emitcode (";", "genFromRTrack 0x%02x==0x%02x+1", val, a->rtrack.value));
                  emitcode ("inc", "a");
                  return 1;
                }
              if (val == ((a->rtrack.value-1) & 0xff) )
                {
                  D(emitcode (";", "genFromRTrack 0x%02x==0x%02x-1", val, a->rtrack.value));
                  emitcode ("dec", "a");
                  return 1;
                }
              if (val == ((~a->rtrack.value) & 0xff) )
                {
                  D(emitcode (";", "genFromRTrack 0x%02x==~0x%02x", val, a->rtrack.value));
                  emitcode ("cpl", "a");
                  return 1;
                }
              if (val == (((a->rtrack.value>>1) |
                           (a->rtrack.value<<7)) & 0xff))
                {
                  D(emitcode (";", "genFromRTrack 0x%02x==rr(0x%02x)", val, a->rtrack.value));
                  emitcode ("rr", "a");
                  return 1;
                }
              if (val == (((a->rtrack.value<<1) |
                           (a->rtrack.value>>7)) & 0xff ))
                {
                  D(emitcode (";", "genFromRTrack 0x%02x==rl(0x%02x)", val, a->rtrack.value));
                  emitcode ("rl", "a");
                  return 1;
                }
              if (val == ( ((a->rtrack.value & 0x0f)<<4) |
                           ((a->rtrack.value & 0xf0)>>4) ))
                {
                  D(emitcode (";", "genFromRTrack 0x%02x==swap(0x%02x)", val, a->rtrack.value));
                  emitcode ("swap", "a");
                  return 1;
                }
              /* Decimal Adjust Accumulator (da a) changes flags so not used */
            }


          {
            unsigned int i;
            char *ptr= zr16_rtrackGetLit(x);

            if (x != ptr)
              {
                /* could get from register, fine */
          
                return 1;
              }

            /* not yet giving up - try to calculate from register R0..R7 */
            for (i = 0; i < 8; i++)
              {
                reg_info *r = &regsZR16[rx_num_to_idx(i)];

                if (a->rtrack.valueKnown && r->rtrack.valueKnown)
                  {
                    /* calculate with a single byte instruction from R0..R7? */
                    if (val == (a->rtrack.value | r->rtrack.value))
                      {
                        D(emitcode (";", "genFromRTrack 0x%02x==0x%02x|0x%02x",
                                    val, a->rtrack.value, r->rtrack.value));
                        emitcode ("orl", "a,%s",r->name);
                        return 1;
                      }
                    if (val == (a->rtrack.value & r->rtrack.value))
                      {
                        D(emitcode (";", "genFromRTrack 0x%02x==0x%02x&0x%02x",
                                    val, a->rtrack.value, r->rtrack.value));
                        emitcode ("anl", "a,%s", r->name);
                        return 1;
                      }
                    if (val == (a->rtrack.value ^ r->rtrack.value))
                      {
                        D(emitcode (";", "genFromRTrack 0x%02x==0x%02x^0x%02x",
                                    val, a->rtrack.value, r->rtrack.value));
                        emitcode ("xrl", "a,%s", r->name);
                        return 1;
                      }
                    /* changes flags (does that matter?)
                    if (val == (a->rtrack.value + r->rtrack.value))
                      {
                        D(emitcode (";", "genFromRTrack 0x%02x=0x%02x+%0x02x",
                                    val, a->rtrack.value, r->rtrack.value));
                        emitcode ("add", "a,%s",r->name);
                        return 1;
                      }
                    so not used */
                  }
              }
          }
      }
    }

  return 0;
}


/* Loads dptr with symbol (if needed)
 */
void zr16_rtrackLoadDptrWithSym (const char *x)
{
  if (enable != 1)
    {
      emitcode ("mov", "dptr,#%s", x);
      return;
    }

  if (regsZR16[DPL_IDX].rtrack.symbol &&
      regsZR16[DPH_IDX].rtrack.symbol)
    {
      /* rtrack.symbol for dph should look like "(something >> 8)" */
      if ((!strcmp  (x, regsZR16[DPL_IDX].rtrack.symbol) &&
           !strncmp (x, regsZR16[DPH_IDX].rtrack.symbol + 1, strlen (x) ) &&
           !strncmp (" >> 8)", regsZR16[DPH_IDX].rtrack.symbol + 1 + strlen (x), 6)))
        {
          /* dptr already holds the symbol */
          D(emitcode (";", "genFromRTrack dptr==#%s",x));
          return;
        }
    }

  emitcode ("mov", "dptr,#%s", x);
}


#if 0
/* Loads index registers R0, R1 with symbol (if needed)
 *
 * R0, R1 index registers are already handled in gen.c (see AOP_INPREG)
 */
void zr16_rtrackLoadR0R1WithSym (const char *reg, const char *x)
{
  int regNum, regIdx;

  if (enable != 1)
    {
      emitcode ("mov", "%s,#%s", reg, x );
      return;
    }

  regNum = reg[1] - '0';
  if (regNum == 0 || regNum == 1)
    {
      regIdx = rx_num_to_idx(regNum);
      if ((NULL != regsZR16[regIdx].rtrack.symbol) && !strcmp (x, regsZR16[regIdx].rtrack.symbol))
        {
          /* register already holds the symbol */
          D(emitcode (";", "genFromRTrack %s=#%s",reg,x));
          return;
        }
    }

  emitcode ("mov", "%s,#%s", reg, x );
}
#endif
