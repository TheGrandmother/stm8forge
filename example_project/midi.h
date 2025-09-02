#ifndef MIDI_H
#define MIDI_H

typedef enum  message_type  {
  INVALID           = 0,      //Silly or undefined messages
  NOTE_ON           = 1,      //0x8-
  NOTE_OFF          = 1<<1,   //0x9-
  AFTERTOUCH        = 1<<2,   //0xa-
  CC                = 1<<3,   //0xb-
  PROGRAM_CHANGE    = 1<<4,   //0xc-
  CH_AFTERTOUCH     = 1<<5,   //0xd-
  PITCH_BEND        = 1<<6,   //0xe-
                              //0xF1 to F6 needs to be added.
  SYSEX_START       = 1<<7,   //0xF0
  SYSEX_END         = 1<<8,   //0xF7
  CLOCK             = 1<<9,   //0xF8
  _ME               = 1<<10,  //0xF9
  START             = 1<<11,  //0xFA
  CONTINUE          = 1<<12,  //0xFB
  STOP              = 1<<13,  //0xFC
  ACTIVE_SENSE      = 1<<14,  //0xFE
  RESET             = 1<<15,  //0xFF
} message_type ;
/*@ type invariant isMessageType(message_type t) =
   t == INVALID       ||
   t == NOTE_ON       ||
   t == NOTE_OFF      ||
   t == AFTERTOUCH    ||
   t == CC            ||
   t == PROGRAM_CHANGE||
   t == CH_AFTERTOUCH ||
   t == PITCH_BEND    ||
   t == SYSEX_START   ||
   t == SYSEX_END     ||
   t == CLOCK         ||
   t == _ME           ||
   t == START         ||
   t == CONTINUE      ||
   t == STOP          ||
   t == ACTIVE_SENSE  ||
   t == RESET;
*/


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
  unsigned char _length;
} MidiMessage;



/*@ 
  requires b >= 0x80 && b <= 0xff;
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
message_type parse_type_byte(unsigned char b);

/*@
  predicate is_channel_message(message_type t) = INVALID < t <= PITCH_BEND;
  predicate is_system_message(message_type t) = SYSEX_START < t <= SYSEX_END;
*/

/*@
  requires \valid(buf+(0..2));

  behavior invalid:
    assumes parse_type_byte(buf[0]) == INVALID;
    assigns \nothing;
    ensures \result.type == INVALID;

  behavior system:
    assumes parse_type_byte(buf[0]) == INVALID;
    assigns \nothing;
    ensures \result.type == INVALID;

*/
MidiMessage parse_midi(unsigned char* buf);

#endif
