/* scheme/write_sob_symbol.asm
 * Take a pointer to a Scheme symbol object, and 
 * prints (to stdout) the character representation
 * of that object.
 * 
 * Programmer: Pavel Rubinson , 2015
 */

 WRITE_SOB_SYMBOL:
  PUSH(FP);
  MOV(FP, SP);
  MOV(R1,R0);
  MOV(R0, INDD(R1,1));
  JUMP(WRITE_SOB_STRING);
  POP(FP);
  RETURN;
