#include "midi.h"
#include "forge_test.h"
// converts a stream into midi messages.
// supports filtering for channel and message types


typedef enum{
  SYSTEM = 0,
  CH1  = 1,
  CH2  = 1<<1,
  CH3  = 1<<2,
  CH4  = 1<<3,
  CH5  = 1<<4,
  CH6  = 1<<5,
  CH7  = 1<<6,
  CH8  = 1<<7,
  CH9  = 1<<8,
  CH10 = 1<<9,
  CH11 = 1<<10,
  CH12 = 1<<11,
  CH13 = 1<<12,
  CH14 = 1<<13,
  CH15 = 1<<14,
  CH16 = 1<<15,
} midi_ch;


typedef struct {
  midi_ch ch;
  message_type type;
  unsigned char d1;
  unsigned char d2;
} MidiMessage;


/*@ 
  check requires b >= 0x80 && b <= 0xff;
  assigns \nothing;

  behavior channel_message:
    assumes b >= 0x80 && b <= 0xef;
    assigns \nothing;
    ensures channel_range: \result >= 1 && \result <= 1 << 6;

  behavior silly_messages:
    assumes b >= 0xf1 && b <= 0xf6;
    assigns \nothing;
    ensures is_invalid: \result == INVALID;

  behavior sysex_start:
    assumes b >= 0xf0;
    assigns \nothing;
    ensures is_sysex_start: \result == SYSEX_START;

  behavior system_message:
    assumes b >= 0xf7 && b <= 0xff;
    assigns \nothing;
    ensures channel_range: \result >= 1 << 8 && \result <= 1 << 15;

  ensures isMessageType(\result);
  disjoint behaviors;
 */
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
