#include <stdio.h>
#include <stdlib.h>
#include "arch/cisc.h"

int main()
{
  START_MACHINE;
  JUMP(CONTINUE);
#include "arch/char.lib"
#include "arch/io.lib"
#include "arch/math.lib"
#include "arch/string.lib"
#include "arch/system.lib"
#include "arch/scheme.lib"

CONTINUE:
/* definitions of some basic scheme objects */
/* this might be replaced later when symbols are properly implemented */

  /* allocating 1000 memory cells */
  ADD(IND(0), IMM(1000));

  /* Void object definition */
  MOV(IND(1), IMM(T_VOID));
  #define SOB_VOID 1

  /* Null (empty list) definition */
  MOV(IND(2), IMM(T_NIL));
  #define SOB_NIL 2

  /* #f definition */
  MOV(IND(3), IMM(T_BOOL))
  MOV(IND(4), IMM(0))
  #define SOB_FALSE 3

  /* #t definition */
  MOV(IND(5), IMM(T_BOOL))
  MOV(IND(6), IMM(1))
  #define SOB_TRUE 5
/* #f */
MOV(R0, SOB_FALSE);
/* end of #f */
/* #t */
MOV(R0, SOB_TRUE);
/* end of #t */
/* #f */
MOV(R0, SOB_FALSE);
/* end of #f */
/* #t */
MOV(R0, SOB_TRUE);
/* end of #t */
  /* printing the content of R0 */
  PUSH(R0);
  CALL(WRITE_SOB);
  /* Stopping the machine */
  STOP_MACHINE;
  return 0;
}
