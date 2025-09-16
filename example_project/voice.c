#include "voice.h"


void update_env(ar_env* e, unsigned int dt) {
  //@ split e->state;
  switch (e->state) {
  case A:
    if  (e->val >= 0xffffu - (long)e->a*dt) {
      e->val = 0xffff;
      e->state = D;
    } else {
      e->val += e->a*dt;
    }
    return;
  case D:
    if (e->val - (long)e->d*dt <= e->s ) {
      e->val = e->s;
      e->state = S;
    } else {
      e->val -= e->d*dt;
    }
    return;
  case R:
    if (e->val <= (long)e->r*dt) {
      e->val = 0;
    } else {
      e->val -= e->r*dt;
    }
    return;
  case S:
    e->val = e->s;
    return;
  }
}

void set_gate(ar_env* e, unsigned char gate) {
  e->gate = gate;
  if (gate) {
    e->state = A;
  } else {
    e->state = R;
  }
}

void init_env(ar_env* e) {
  e->gate = (char)0;
  e->val = 0;
  e->a = 0xffff/50;
  e->d = 0xffff/1000;
  e->s = (0xffff/10)*6;
  e->r = 0xffff/250;
  e->state = R;
}


void set_a(ar_env* e, unsigned int a) {
  e->a = 0xffff/a;
}
void set_d(ar_env* e, unsigned int d) {
  e->d = 0xffff/d;
}
void set_s(ar_env* e, unsigned int s) {
  e->s = s;
}
void set_r(ar_env* e, unsigned int r) {
  e->r = 0xffff/r;
}


/*@
  assigns \nothing;
*/
unsigned int vel_to_duty(char vel, unsigned int max) {
  if (vel == 0) {
    return 1;
  }
  return ((long)vel * (long)max) / 0x7f;
}

unsigned int counters[12] = {
  0x3029, // counter at middle C aka MIDI note 60/0x3c
  0x2d75,
  0x2ae8,
  0x2880,
  0x263a,
  0x2414,
  0x220e,
  0x2025,
  0x1e57,
  0x1ca3,
  0x1b07,
  0x1983  // Middle B
};

unsigned int note_to_counter(signed char note) {
  char deg = note % 12;
  signed char oct = (note / 12);
  if (oct > 5) {
    return counters[deg] >> (oct-5);
  } else {
    return counters[deg] << (5-oct);
  }
}
