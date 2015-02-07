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

 CONTINUE:
  STOP_MACHINE;
  return 0;
}

