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



void TEST_parser() {
  test_start();
  assert_eq(parse_type_byte(0x80), NOTE_ON);
  assert_eq(parse_type_byte(0x90), NOTE_OFF);
  assert_eq(parse_type_byte(0xF2), INVALID);
  assert_eq(parse_type_byte(0xFC), STOP);
  assert_eq(parse_type_byte(0xF0), SYSEX_START);
  test_complete();
}
