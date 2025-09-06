#include "midi.h"
#include "forge_test.h"
// converts a stream into midi messages.
// supports filtering for channel and message types



/*@
  assigns \nothing;
  ensures 1 <= \result <=3;
 */
unsigned char get_length(message_type t) {
  switch (t) {
  case M_NOTE_ON:
    return 3;
  case M_NOTE_OFF:
    return 3;
  case M_AFTERTOUCH:
    return 3;
  case M_CC:
    return 3;
  case M_PROGRAM_CHANGE:
    return 2;
  case M_SONG_POINTER:
    return 3;
  case M_SONG_SELECT:
    return 3;
  case M_QUARTER_FRAME:
    return 2;
  case M_CH_AFTERTOUCH:
    return 2;
  case M_PITCH_BEND:
    return 2;
  case M_MEASURE_END:
    return 2;
  default:
    return 1;
  }
}

/*@
 assigns \nothing;
 */
message_type parse_type_byte(unsigned char b) {
  if (b < 0x80) {
    return M_INVALID;
  } else if (b <= 0xef) {
    return b & 0xf0;
  } else if (b == 0xf0) {
    return M_SYSEX_START;
  } else if (b == 0xf4 || b == 0xf5 || b == 0xfd) {
    return M_INVALID;
  } else {
    return b;
  }
}

/*@
 assigns \nothing;
 ensures \result ==> M_NOTE_ON <= t <= M_PITCH_BEND;
 */
int is_channel_message(message_type t) {
  return t >= M_NOTE_ON && t <= M_PITCH_BEND;
}

/*@
 assigns \nothing;
 ensures 0 <= \result <= 0xf;
 */
unsigned char get_channel(unsigned char b) {
  return (b & 0xf);
}

parser_state parser(MidiMessage* m, parser_state s, unsigned char b) {
  switch (s) {
  case M_INIT:
    m->type = parse_type_byte(b);
    if (m->type == M_INVALID) {
      m->_length = 1;
      return M_COMPLETE;
    }

    if (is_channel_message(m->type)) {
      m->ch = get_channel(b);
    }

    m->_length = get_length(m->type);
    if (m->_length == 1) {
      return M_COMPLETE;
    } else {
      return M_D1;
    }
  case M_D1:
    m->d1 = b;
    if (m->_length == 2) {
      return M_COMPLETE;
    } else {
      return M_D2;
    }
  case M_D2:
    m->d2 = b;
    return M_COMPLETE;
  default:
    return M_COMPLETE;
  }
}
