#include "midi.h"
#include "forge_test.h"
// converts a stream into midi messages.
// supports filtering for channel and message types



/*@
  assigns /nothing;
  ensures 1 <= /result <=3;
 */
unsigned char get_length(message_type t) {
    switch (t) {
    case INVALID:
      return 1;
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
    case SYSEX_START:
      return 1;
    case SYSEX_END:
      return 1;
    case CLOCK:
      return 1;
    case _ME:
      return 1;
    case START:
      return 1;
    case CONTINUE:
      return 1;
    case STOP:
      return 1;
    case ACTIVE_SENSE:
      return 1;
    case RESET:
      return 1;
    }
}

message_type parse_type_byte(unsigned char b) {
    assert(b >= 0x80, "Type byte not in range");
    if (b <= 0xef) {
        return 1 << ((b >> 4) - 8);
    } else if (b == 0xf0) {
        return SYSEX_START;
    } else if (b >= 0xf1 && b <= 0xf6) {
        return INVALID;
    } else {
        return 1 << ((b & 0xf) + 1);
    }
}


char is_channel_message(message_type t) {
    return t >= NOTE_ON && t <= PITCH_BEND;
}

MidiMessage parse_midi(unsigned char* buf) {
    MidiMessage message;
    message.type = parse_type_byte(buf[0]);
    message._length = get_length(message.type);

    if (message._length >= 2) {
      message.d1 = buf[1];
    }
    if (message._length == 3) {
      message.d2 = buf[2];
      }

    if (is_channel_message(message.type)) {
        message.ch = 1 << ((buf[0] & 0x0f) + 1);
    } else {
        message.ch = SYSTEM;
    }

    return message;
}

