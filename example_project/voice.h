#ifndef VOICE_H
#define VOICE_H

typedef enum state {
  A, D, S, R
} state;
/*@
  type invariant is_env_state(state e) = e == A || e == D || e == S || e == R;
*/

typedef struct voice {
  unsigned char channel;
  char note;
  char gate;
} voice;

typedef struct ar_env {
  char gate;
  state state;
  unsigned int a;
  unsigned int d;
  unsigned int s;
  unsigned int r;
  unsigned int val;
} ar_env;
/*@
  type invariant ptr_is_adsr_env(ar_env* e) = e->s >= 0 && e->a > 0 && e->d > 0 && e->r > 0 && is_env_state(e->state);
*/

/*@
  requires \valid(e);
  requires 0 < a;
  assigns e->a;
*/
void set_a(ar_env* e, unsigned int a);
/*@
  requires \valid(e);
  requires 0 < d;
  assigns e->d;
*/
void set_d(ar_env* e, unsigned int d);
/*@
  requires \valid(e);
  requires 0 < r;
  assigns e->r;
*/
void set_r(ar_env* e, unsigned int r);

/*@
  requires \valid(e);
  assigns e->s;
*/
void set_s(ar_env* e, unsigned int s);

/*@
  requires \valid(e);
  assigns e->a;
  assigns e->d;
  assigns e->s;
  assigns e->r;
  assigns e->state;
  assigns e->val;
  assigns e->gate;
  ensures ptr_is_adsr_env(e);
*/
void init_env(ar_env* e);

/*@
  requires not_stale: dt < 0x8000;
  requires \valid(e);
  requires 0 < dt;
  requires ptr_is_adsr_env(e);
  requires is_env_state(e->state);
  assigns e->val;
  assigns e->state;

  behavior top_out:
    assumes e->state == A;
    assumes e->val + e->a*dt >= 0xffff;
    ensures e->val == 0xffff;
    ensures e->state == D;
  behavior attacking:
    assumes e->state == A;
    assumes e->val + e->a*dt < 0xffff;
    ensures \old(e->val) < e->val;
  behavior decaying:
    assumes e->state == D;
    assumes e->val - e->d*dt > e->s;
    ensures \old(e->val) > e->val;
  behavior done_decay:
    assumes e->state == D;
    assumes e->val - e->d*dt <= e->s;
    ensures e->state == S;
    ensures e->val == e->s;
  behavior release_bottom:
    assumes e->val < e->r*dt;
    assumes e->state == R;
    ensures e->state == R;
    ensures e->val == 0x0;
  behavior release:
    assumes e->state == R;
    assumes e->val >= e->r*dt;
    ensures e->state == R;
    ensures \old(e->val) > e->val;
  behavior sustain:
    assumes e->state == S;
    ensures e->state == S;
    ensures e->val == e->s;
  complete behaviors;
  disjoint behaviors;
*/
void update_env(ar_env* e, unsigned int dt);

/*@
  requires \valid(e);
  requires 0 <= gate <= 1;
  assigns e->gate;
  assigns e->state;
  ensures (gate && e->state == A) || (!gate && e->state == R);
*/
void set_gate(ar_env* e, unsigned char gate);

/*@

  requires 0 <= note;
  assigns \nothing;
  ensures 0 <= \result;
*/
unsigned int note_to_counter(signed char note);

#endif
