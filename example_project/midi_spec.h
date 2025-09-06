#include "midi.h"
#ifndef MIDI_SPEC_H
#define MIDI_SPEC_H


/*@ type invariant isMessageType(message_type t) = 0 <= t <= 0xff;
*/

/*@
  predicate is_channel_message(unsigned char b) = b >= 0x80 && b <= 0xef;
  predicate is_system_message(unsigned char b) =  0xf0 <= b <= 0xff && (b != 0xf4 || b != 0xf5 || b != 0xfd);
*/

//@ assigns \nothing;
message_type parse_type_byte(unsigned char b);


/*@ type invariant is_parser_state(parser_state t) =
   t == M_INIT     ||
   t == M_COMPLETE ||
   t == M_D1       ||
   t == M_D2;
*/

/*@
  requires \valid(m);
  requires s != M_COMPLETE;
  requires is_parser_state(s);
  behavior init:
    assumes s == M_INIT;
    assigns m->type;
    assigns m->ch;
    assigns m->_length;
    ensures is_parser_state(\result);
    ensures m->type == M_INVALID ==> \result == M_COMPLETE;
    ensures m->type == M_INVALID ==> m->_length == 1;
    ensures m->type != M_INVALID && m->_length == 1 ==> \result == M_COMPLETE;
    ensures m->_length > 1 ==> \result == M_D1;

  behavior M_D1:
    assumes s == M_D1;
    requires m->type != M_INVALID;
    requires m->_length > 1;
    assigns m->d1;
    ensures is_parser_state(\result);
    ensures m->_length == 2 ==> \result == M_COMPLETE;
    ensures m->_length > 2 ==> \result == M_D2;
    ensures m->d1 == b;

  behavior M_D2:
    assumes s == M_D2;
    requires m->type != M_INVALID;
    requires m->_length > 2;
    assigns m->d2;
    ensures is_parser_state(\result);
    ensures m->_length == 3 ==> \result == M_COMPLETE;
    ensures m->d2 == b;

  disjoint behaviors;
  complete behaviors;
*/
enum parser_state parser(MidiMessage* m, parser_state s, unsigned char b);

#endif
