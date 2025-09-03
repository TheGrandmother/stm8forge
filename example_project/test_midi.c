#include "midi.h"
#include <forge_test.h>


void TEST_something() {
  test_start();
  assert_eq(parse_type_byte(0x80), NOTE_ON);
  assert_eq(parse_type_byte(0xC2), PROGRAM_CHANGE);
  assert_eq(parse_type_byte(0x9D), NOTE_OFF);
  assert_eq(parse_type_byte(0xF2), INVALID);
  assert_eq(parse_type_byte(0xFC), STOP);
  assert_eq(parse_type_byte(0xF0), SYSEX_START);
  test_complete();
}



void TEST_test_something_else() {
  test_start();
  MidiMessage m;

  unsigned char invalid[1] = {0xF2};
  parse_midi(&m, invalid);
  assert_eq(m.type, INVALID);

  unsigned char noteon[3] = {0x87, 0x12, 0x13};
  parse_midi(&m, noteon);
  assert_eq(m.type, NOTE_ON);
  assert_eq(m.ch, CH8);
  assert_eq(m.d1, 0x12);
  assert_eq(m.d2, 0x13);
  assert_eq(m._length, 3);

  unsigned char pc[3] = {0xc2, 0x17};
  parse_midi(&m, pc);
  assert_eq(m.type, PROGRAM_CHANGE);
  assert_eq(m.ch, CH3);
  assert_eq(m.d1, 0x17);
  assert_eq(m._length, 2);

  test_complete();
}
