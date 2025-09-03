#include "midi.h"

volatile char BOB = 10;

void main(void)
{
  parse_type_byte(0x8f);
  while (1) {}
}
