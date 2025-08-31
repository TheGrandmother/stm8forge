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
                              //0xF1 to F6 are silly.
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

message_type parse_type_byte(unsigned char b);

#endif
