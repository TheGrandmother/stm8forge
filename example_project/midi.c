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
  case CH_AFTERTOUCH:
    return 2;
  case PITCH_BEND:
    return 2;
  default:
    return 1;
  }
}

message_type parse_type_byte(unsigned char b) {
  assert(b >= 0x80, "Type byte not in range");
  if (b <= 0xef) {
    return (message_type)(1 << ((b >> 4) - 8));
  } else if (b == 0xf0) {
    return SYSEX_START;
  } else if (b >= 0xf1 && b <= 0xf6) {
    return INVALID;
  } else {
    return (message_type)(1 << ((b & 0xf) + 1));
  }
}

/*@
 assigns \nothing;
 */
char is_channel_message(message_type t) {
  return t >= NOTE_ON && t <= PITCH_BEND;
}

void parse_midi(MidiMessage* m, unsigned char* buf) {
  m->type = parse_type_byte(buf[0]);
  m->_length = get_length(m->type);

  if (m->_length >= 2) {
    m->d1 = buf[1];
  }
  if (m->_length == 3) {
    m->d2 = buf[2];
  }

  if (is_channel_message(m->type)) {
    m->ch = 1 << (buf[0] & 0x0f);
  } else {
    m->ch = SYSTEM;
  }
}
