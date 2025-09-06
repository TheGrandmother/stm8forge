#include "midi.h"
#include <forge_test.h>


void TEST_parse_byte() {
  test_start();
  assert_eq(parse_type_byte(0x80), M_NOTE_ON);
  assert_eq(parse_type_byte(0xC2), M_PROGRAM_CHANGE);
  assert_eq(parse_type_byte(0x9D), M_NOTE_OFF);
  assert_eq(parse_type_byte(0xF2), M_SONG_POINTER);
  assert_eq(parse_type_byte(0xFC), M_STOP);
  assert_eq(parse_type_byte(0xF0), M_SYSEX_START);
  assert_eq(parse_type_byte(0xFD), M_INVALID);
  assert_eq(parse_type_byte(0xFF), M_RESET);
  test_complete();
}



void TEST_parser() {
  test_start();
  MidiMessage m;

  unsigned char invalid[1] = {0x01};
  parser_state s = parser(&m, M_INIT, invalid[0]);
  assert_eq(m.type, M_INVALID);
  assert_eq(s, M_COMPLETE);

  unsigned char noteon[3] = {0x87, 0x12, 0x13};
  s = parser(&m, M_INIT, noteon[0]);
  assert_eq(m.type, M_NOTE_ON);
  assert_eq(m._length, 3);
  assert_eq(m.ch, 7);
  assert_eq(s, M_D1);
  s = parser(&m, s, noteon[1]);
  assert_eq(m.d1, 0x12);
  assert_eq(s, M_D2);
  s = parser(&m, s, noteon[2]);
  assert_eq(m.d2, 0x13);
  assert_eq(s, M_COMPLETE);

  unsigned char pc[3] = {0xc2, 0x17};
  s = parser(&m, M_INIT, pc[0]);
  assert_eq(m.type, M_PROGRAM_CHANGE);
  assert_eq(m._length, 2);
  assert_eq(m.ch, 2);
  assert_eq(s, M_D1);
  s = parser(&m, s, pc[1]);
  assert_eq(m.d1, 0x17);
  assert_eq(s, M_COMPLETE);

  test_complete();
}
