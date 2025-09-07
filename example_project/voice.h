#ifndef VOICE_H
#define VOICE_H

typedef struct voice {
  unsigned char channel;
  char note;
  char gate;
} voice;

typedef struct ar_env {
  char gate;
  char hold;
  unsigned int a; // Attack in change per ms
  unsigned int r; // Release in change per ms
  unsigned int val;
  unsigned int t; // time in ms 
} ar_env;

void init_env(ar_env* e);

/*@
  assigns e->val;
  assigns e->time;
  assigns e->gate;
  behavior rising:
    assumes e->gate == 1;
    ensures e->val >= \old(e->val);
  behavior falling:
    assumes e->gate == 0;
    ensures e->val <= \old(e->val);
*/
void update_env(ar_env* e, unsigned int dt);

/*@
  requires 0 <= gate <= 1;
  assigns e->gate;
*/
void set_gate(ar_env* e, unsigned char gate);

/*@
  requires 0 <= max;
  requires 0 <= vel;
  requires max * vel <= 0xffff * 0xff;
  assigns \nothing;
  ensures 1 <= \result <= max;
  ensures vel == 0xff ==> \result == max;
*/
unsigned int vel_to_duty(char vel, unsigned int max);

/*@

  requires 0 <= vel;
  assigns \nothing;
  ensures 0 <= \result;
*/
unsigned int note_to_counter(char vel);

#endif
