/*-------------------------------------------------------------------------
  rtrack.h - header file for tracking content of registers on an zr16

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

bool _zr16_rtrackUpdate (const char *line);

char *zr16_rtrackGetLit(const char *x);

int zr16_rtrackMoveALit (const char *x);

void zr16_rtrackLoadDptrWithSym (const char *x);
void zr16_rtrackLoadR0R1WithSym (const char *reg, const char *x);
