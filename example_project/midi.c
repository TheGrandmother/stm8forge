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
  case NOTE_ON:
    return 3;
  case NOTE_OFF:
    return 3;
  case AFTERTOUCH:
    return 3;
  case CC:
    return 3;
  case PROGRAM_CHANGE:
    return 2;
  case SONG_POINTER:
    return 3;
  case SONG_SELECT:
    return 3;
  case QUARTER_FRAME:
    return 2;
  case CH_AFTERTOUCH:
    return 2;
  case PITCH_BEND:
    return 2;
  case MEASURE_END:
    return 2;
  default:
    return 1;
  }
}

message_type parse_type_byte(unsigned char b) {
  if (b < 0x80) {
    return INVALID;
  } else if (b <= 0xef) {
    return b & 0xf0;
  } else if (b == 0xf0) {
    return SYSEX_START;
  } else if (b == 0xf4 || b == 0xf5 || b == 0xfd) {
    return INVALID;
  } else {
    return b;
  }
}

/*@
 assigns \nothing;
 ensures t >= NOTE_ON && t <= PITCH_BEND;
 */
int is_channel_message(message_type t) {
  return t >= NOTE_ON && t <= PITCH_BEND;
}

/*@
 assigns \nothing;
 ensures 0 <= b <= 0xf;
 */
int get_channel(unsigned char b) {
  return (b & 0xf);
}

parse_state parser(MidiMessage* m, parse_state s, unsigned char b) {
  switch (s) {
  case INIT:
    m->type = parse_type_byte(b);
    if (m->type == INVALID) {
      m->_length = 1;
      return COMPLETE;
    }

    if (is_channel_message(m->type)) {
      m->ch = get_channel(b);
    }

    m->_length = get_length(m->type);
    if (m->_length == 1) {
      return COMPLETE;
    } else {
      return D1;
    }
  case D1:
    m->d1 = b;
    if (m->_length == 2) {
      return COMPLETE;
    } else {
      return D2;
    }
  case D2:
    m->d2 = b;
    return COMPLETE;
  default:
    return COMPLETE;
  }
}
