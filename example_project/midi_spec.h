#include "midi.h"
#ifndef MIDI_SPEC_H
#define MIDI_SPEC_H


/*@ type invariant is_message_type(message_type t) = 0x80 <= t <= 0xff;
*/

/*@
  predicate is_channel_message(unsigned char b) = b >= 0x80 && b <= 0xef;
  predicate is_system_message(unsigned char b) =  0xf0 <= b <= 0xff && (b != 0xf4 || b != 0xf5 || b != 0xfd);
  predicate is_data_byte(unsigned char b) = 0 <= b < 0x80;
*/


/*@
  type invariant is_parser_state(parser_state t) = M_INIT <= t <= M_D2;

  type invariant valid_message(midi_message m) =
    0 <= m.ch <= 0xf && is_message_type(m.type) && 0 <= m._length <= 3;

  type invariant valid_message_ptr(midi_message* m) =
    0 <= m->ch <= 0xf && is_message_type(m->type) && 0 <= m->_length <= 3;
*/



/*@
  assigns \nothing;
  ensures 1 <= \result <=3;
 */
unsigned char get_length(message_type t);

/*@
 assigns \nothing;
 ensures is_message_type(\result);
 */
message_type parse_type_byte(unsigned char b);

/*@
 assigns \nothing;
 ensures \result ==> M_NOTE_ON <= t <= M_PITCH_BEND;
 */
int is_channel_message(message_type t);

/*@
 assigns \nothing;
 ensures 0 <= \result <= 0xf;
 */
unsigned char get_channel(unsigned char b);

/*@
 assigns \nothing;
 ensures 0 <= b < 0x80 == \result;
 */
unsigned char is_data(unsigned char b);


/*@
  requires \valid(m);
  requires s != M_COMPLETE;
  requires is_parser_state(s);
  requires valid_message_ptr(m);

  behavior init:
    assumes s == M_INIT;
    assumes !is_data_byte(b);
    assigns m->type;
    assigns m->ch;
    assigns m->_length;
    ensures is_parser_state(\result);
    ensures m->type == M_INVALID ==> \result == M_COMPLETE;
    ensures m->type == M_INVALID ==> m->_length == 1;
    ensures m->type != M_INVALID && m->_length == 1 ==> \result == M_COMPLETE;
    ensures m->_length > 1 ==> \result == M_D1;

  behavior faulty_running:
    assumes s == M_INIT;
    assumes is_data_byte(b);
    assumes m->type == M_INVALID || m->_length == 1;
    assigns m->type;
    ensures m->type == M_INVALID;
    ensures \result == M_COMPLETE;

  behavior running_mode:
    assumes s == M_INIT;
    assumes is_data_byte(b);
    assumes m->type != M_INVALID;
    assumes m->_length > 1;
    assigns m->d1;
    ensures m->d1 == b;
    ensures m->_length == 2 ==> \result == M_COMPLETE;
    ensures m->_length > 2 ==> \result == M_D2;
    ensures is_parser_state(\result);

  behavior M_D1:
    assumes s == M_D1;
    assumes is_data_byte(b);
    assumes m->type != M_INVALID && m->_length > 1;
    assumes m->_length > 1;
    assigns m->d1;
    ensures is_parser_state(\result);
    ensures m->_length == 2 ==> \result == M_COMPLETE;
    ensures m->_length > 2 ==> \result == M_D2;
    ensures m->d1 == b;

  behavior M_D2:
    assumes s == M_D2;
    assumes is_data_byte(b);
    assumes m->type != M_INVALID;
    assumes m->_length > 2;
    assigns m->d2;
    ensures is_parser_state(\result);
    ensures m->_length == 3 ==> \result == M_COMPLETE;
    ensures m->d2 == b;

  disjoint behaviors;
  complete behaviors;
*/
enum parser_state parser(midi_message* m, parser_state s, unsigned char b);

#endif
