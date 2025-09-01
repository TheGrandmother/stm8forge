#include "forge_test.h"
#include <stdio.h>

volatile unsigned char sif;

volatile unsigned char test_status;

enum tets_status {
  FAILED = 1,
  PASSED = 2,
  COMPLETE = 4
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

void _assert(char condition, char* message) {
  if (!condition) {
    sif_print("ASSERT FAILED: ");
    sif_print(message);
    sif_putchar('\n');
    test_status |= FAILED;
    // test_status |= COMPLETE;
    // sif_stop();
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
  char buf[64];
  if (!condition) {
    sif_write(name);
    sif_write(":");
    sprintf(buf, "%d\t", line);
    sif_write(buf);
    sif_write(cond_text);
    sif_write("\n");
    sif_write("\0");
    test_status |= FAILED;
  }
}

void test_pass(void) {
    sif_write("TEST PASSED\n");
    test_status |= COMPLETE | PASSED;
    sif_stop();
}
