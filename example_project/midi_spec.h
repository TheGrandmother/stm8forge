#ifndef MIDI_H
#define MIDI_H

typedef enum  message_type  {
    INVALID                         = 0,
    NOTE_ON                         = 0x80, // 2
    NOTE_OFF                        = 0x90,// 2
    AFTERTOUCH                      = 0xa0,// 2
    CC                              = 0xb0,// 2
    PROGRAM_CHANGE                  = 0xc0,// 1
    CH_AFTERTOUCH                   = 0xd0,// 1
    PITCH_BEND                      = 0xe0,// 2
    SYSEX_START                     = 0xf0,
    QUARTER_FRAME                   = 0xf1, // 1
    SONG_POINTER                    = 0xf2, // 2
    SONG_SELECT                     = 0xf3, // 1
 // INVALID                         = 0xf4,
 // INVALID                         = 0xf5,
    TUNE_REQUEST                    = 0xf6,
    SYSEX_END                       = 0xf7, // Not supported
    CLOCK                           = 0xf8,
    MEASURE_END                     = 0xf9, // 1
    START                           = 0xfa,
    CONTINUE                        = 0xfb,
    STOP                            = 0xfc,
 // INVALID                         = 0xfd,
    ACTIVE_SENSE                    = 0xfe,
    RESET                           = 0xff,
} message_type ;
/*@ type invariant isMessageType(message_type t) = 0 <= t <= 0xff;
*/

typedef struct {
    unsigned char ch;
    message_type type;
    unsigned char d1;
    unsigned char d2;
    unsigned char _length;
} MidiMessage;


/*@
  predicate is_channel_message(unsigned char b) = b >= 0x80 && b <= 0xef;
  predicate is_system_message(unsigned char b) = b >= 0xf7 && b <= 0xff ||  b == 0xf0;
*/



//@ assigns \nothing;
message_type parse_type_byte(unsigned char b);


typedef enum  parse_state  {
  INIT,
  COMPLETE,
  D1,
  D2,
} parse_state;
/*@ type invariant is_parse_state(parse_state t) =
   t == INIT     ||
   t == COMPLETE ||
   t == D1       ||
   t == D2;
*/

/*@
  requires \valid(m);
  requires s != COMPLETE;
  requires is_parse_state(s);
  behavior init:
    assumes s == INIT;
    assigns m->type;
    assigns m->ch;
    assigns m->_length;
    ensures is_parse_state(\result);
    ensures m->type == INVALID ==> \result == COMPLETE;
    ensures m->type == INVALID ==> m->_length == 1;
    ensures m->type != INVALID && m->_length == 1 ==> \result == COMPLETE;
    ensures m->_length > 1 ==> \result == D1;

  behavior D1:
    assumes s == D1;
    requires m->type != INVALID;
    requires m->_length > 1;
    assigns m->d1;
    ensures is_parse_state(\result);
    ensures m->_length == 2 ==> \result == COMPLETE;
    ensures m->_length > 2 ==> \result == D2;
    ensures m->d1 == b;

  behavior D2:
    assumes s == D2;
    requires m->type != INVALID;
    requires m->_length > 2;
    assigns m->d2;
    ensures is_parse_state(\result);
    ensures m->_length == 3 ==> \result == COMPLETE;
    ensures m->d2 == b;

  disjoint behaviors;
  complete behaviors;
*/
parse_state parser(MidiMessage* m, parse_state s, unsigned char b);

#endif
