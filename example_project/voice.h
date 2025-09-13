#ifndef VOICE_H
#define VOICE_H

typedef enum state {
  A, D, S, R
} state;
/*@
  type invariant is_env_staet(state e) = e == A || e == D || e == S || e == R;
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
  type invariant is_adsr_env(ar_env e) = e.a > 0 && e.d > 0 && e.r > 0;
*/

// Sets attack time in ms
void set_a(ar_env* e, unsigned int a);
void set_d(ar_env* e, unsigned int d);
void set_r(ar_env* e, unsigned int r);
// Max sustain is 0xffff
void set_s(ar_env* e, unsigned int s);

void init_env(ar_env* e);

/*@
  requires \valid(e);
  requires dt > 0;
  requires is_adsr_env(*e);
  assigns e->val;
  assigns e->state;
  behavior attack:
    assumes e->state == A;
    assumes e->gate == 1;
    ensures e->val == 0xffff ==> e->state == D;
  behavior resease:
    assumes e->state == R;
    assumes e->gate == 0;
    ensures e->val <= \old(e->val);
  behavior sustain:
    assumes e->state == S;
    assumes e->gate == 1;
    ensures e->val == e->s;
  behavior decay:
    assumes e->state == D;
    assumes e->gate == 1;
    assumes e->val > e->s;
    ensures e->val <= \old(e->val);
    ensures e->val == e->s ==> e->state == S;
*/
void update_env(ar_env* e, unsigned int dt);

/*@
  requires 0 <= gate <= 1;
  assigns e->gate;
  assigns e->state;
  ensures (gate ==> e->state == A) && (!gate ==> e->state == R);
*/
void set_gate(ar_env* e, unsigned char gate);

/*@

  requires 0 <= vel;
  assigns \nothing;
  ensures 0 <= \result;
*/
unsigned int note_to_counter(char vel);

#endif
