#include "midi.h"
#include "forge_test.h"


void TEST_type_byte_parser() {
  test_start();
  assert_eq(parse_type_byte(0x80), NOTE_ON);
  assert_eq(parse_type_byte(0x9D), NOTE_OFF);
  assert_eq(parse_type_byte(0xF2), INVALID);
  assert_eq(parse_type_byte(0xFC), STOP);
  assert_eq(parse_type_byte(0xF0), SYSEX_START);
  test_complete();
}



void TEST_basic_parsing_message() {
  test_start();

  unsigned char invalid[1] = {0xF2};
  assert_eq(parse_midi(invalid).type, INVALID);

  unsigned char noteon[3] = {0x87, 0x12, 0x13};
  assert_eq(parse_midi(noteon).type, NOTE_ON);
  assert_eq(parse_midi(noteon).ch, CH8);
  assert_eq(parse_midi(noteon).d1, 0x12);
  assert_eq(parse_midi(noteon).d2, 0x13);
  assert_eq(parse_midi(noteon)._length, 3);

  unsigned char pc[3] = {0xc2, 0x17};
  assert_eq(parse_midi(pc).type, NOTE_ON);
  assert_eq(parse_midi(pc).ch, CH3);
  assert_eq(parse_midi(pc).d1, 0x12);
  assert_eq(parse_midi(pc)._length, 2);

  test_complete();
}
