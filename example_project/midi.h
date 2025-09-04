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


typedef enum {
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
  predicate is_channel_message(unsigned char b) = b >= 0x80 && b <= 0xef;
  predicate is_system_message(unsigned char b) = b >= 0xf7 && b <= 0xff ||  b == 0xf0;
*/



/*@
  requires \valid(m);
  assigns *m;
*/
void parse_midi(MidiMessage* m, unsigned char* buf);

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
  requires is_parse_state(s);
    assigns *m;
  behavior init:
    assumes s == INIT;
    assigns *m;
    assigns m->type;
    assigns m->ch;
    assigns m->_length;
    ensures is_parse_state(\result);
    ensures m->type == INVALID ==> \result == COMPLETE;
    ensures m->type == INVALID ==> m->_length == 1;
    ensures m->type != INVALID ==> (is_channel_message(b) ==> m->ch > 0);
    ensures m->type != INVALID && m->_length == 1 ==> \result == COMPLETE;
    ensures m->_length > 1 ==> \result == D1;

  behavior D1:
    assumes s == D1;
    assumes m->type != INVALID;
    assumes m->_length > 1;
    assigns *m;
    assigns m->d1;
    ensures is_parse_state(\result);
    ensures m->_length == 2 ==> \result == COMPLETE;
    ensures m->_length > 2 ==> \result == D2;
    ensures m->d1 == b;

  behavior D2:
    assumes s == D2;
    assumes m->type != INVALID;
    assumes m->_length > 2;
    assigns *m;
    assigns m->d2;
    ensures is_parse_state(\result);
    ensures m->_length == 3 ==> \result == COMPLETE;
    ensures m->d2 == b;
*/
parse_state parser(MidiMessage* m, parse_state s, unsigned char b);

#endif
