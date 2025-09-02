#include "forge_test.h"
#include <stdio.h>

volatile unsigned char sif;
volatile unsigned char sifa;
volatile unsigned char sifaaa;

volatile unsigned char test_status = 0;
volatile unsigned int test_mhay = 0xBABE;
#define message_length 64
volatile char assert_message[message_length];

enum tets_status {
  FAILED =    0b00001,
  PASSED =    0b00010,
  COMPLETE =  0b00100,
  RUNNING =   0b01000,
  ASSERT =    0b10000
};


enum sif_command {
  DETECT_SIGN	        = '!',	// answer to detect command
  SIFCM_DETECT		= '_',	// command used to detect the interface
  SIFCM_COMMANDS	= 'i',	// get info about commands
  SIFCM_IFVER		= 'v',	// interface version
  SIFCM_SIMVER		= 'V',	// simulator version
  SIFCM_IFRESET		= '@',	// reset the interface
  SIFCM_CMDINFO		= 'I',	// info about a command
  SIFCM_CMDHELP		= 'h',	// help about a command
  SIFCM_STOP		= 's',	// stop simulation
  SIFCM_PRINT		= 'p',	// print character
  SIFCM_FIN_CHECK	= 'f',	// check input file for input
  SIFCM_READ		= 'r',	// read from input file
  SIFCM_WRITE		= 'w',	// write to output file
};

void sif_stop(void) {
  sif= SIFCM_STOP;
}

void sif_putchar(char c) {
  sif= SIFCM_PRINT;
  sif= c;
}

void sif_print(char *s) {
  while (*s) {
    sif= SIFCM_PRINT;
    sif= *s++;
  }
}

void sif_write(char *s) {
  while (*s) {
    sif= SIFCM_WRITE;
    sif= *s++;
  }
}

void _assert(char condition, char* message, int line, const char* name) {
  if (!condition) {
    if (test_status & RUNNING) {
      sprintf(assert_message, "%s:%d ASSERT %s", name, line, message);
      test_status |= (FAILED | ASSERT);
    } else {
      sif_print("assert: ");
      sif_print(name);
      sif_print(" ");
      sif_print(message);
      sif_putchar('\n');
      sif_stop();
    }
  }
}

void _assert_eq(int lhs, char* lhs_text, int rhs, char* rhs_text, int line, const char* name){
  char buf[64];
  if (lhs !=  rhs) {
    sprintf(buf, "%s != %s (0x%x != 0x%x)", lhs_text, rhs_text, lhs, rhs);
    _test_assert(0, buf, line, name);
  }

}

void _test_assert(char condition, char* cond_text, int line, const char* name) {
  if (!condition) {
    sprintf(assert_message, "%s:%d  %s", name, line, cond_text);
    test_status |= FAILED;
  }
}

void test_complete(void) {
    test_status |= COMPLETE;
}

void test_start(void) {
    test_status |= RUNNING;
}
