#include "voice.h"


void update_env(ar_env* e, unsigned int dt) {
  unsigned int dv;
  switch (e->state) {
  case A:
    dv = (e->a)*dt;
    if (e->val >= 0xffff - dv) {
      e->val = 0xffff;
      e->state = D;
    } else {
      e->val += dv;
    }
    return;
  case D:
    dv = (e->d)*dt;
    if (e->s >= 0xffff - dv || e->val <= e->s + dv) {
      e->val = e->s;
      e->state = S;
    } else {
      e->val -= dv;
    }
    return;
  case R:
    dv = (e->r)*dt;
    if (e->val <= 0 + dv) {
      e->val = 0;
    } else {
      e->val -= dv;
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
  e->gate = 0;
  e->state = R;
  e->val = 0;
  e->a = 0xffff/50;
  e->d = 0xffff/1000;
  e->s = (0xffff/10)*6;
  e->r = 0xffff/250;
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

unsigned int note_to_counter(char note) {
  unsigned char deg = note % 12;
  char oct = (note / 12);
  if (oct > 5) {
    return counters[deg] >> (oct-5);
  } else {
    return counters[deg] << (5-oct);
  }
}
