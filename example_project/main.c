#include "stm8s.h"
#include "stm8s_conf.h"
#include "midi.h"

#define CONFIG_UNUSED_PINS_STM8S001 \
{ \
 GPIOA->DDR |= GPIO_PIN_2; \
 GPIOB->DDR |= GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_2 | GPIO_PIN_3 | GPIO_PIN_6 | GPIO_PIN_7; \
 GPIOC->DDR |= GPIO_PIN_1 | GPIO_PIN_2 | GPIO_PIN_7; \
 GPIOD->DDR |= GPIO_PIN_0 | GPIO_PIN_2 | GPIO_PIN_4 | GPIO_PIN_7;\
 GPIOE->DDR |= GPIO_PIN_5; \
 GPIOF->DDR |= GPIO_PIN_4; \
}


typedef unsigned int size_t;

void debug_on() {
  GPIO_WriteLow(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5);
}

void debug_off() {
  GPIO_WriteHigh(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5);
}

void debug_flash() {
  char flashes = 10;
  while(flashes--) {
    long int d = 8000;
    debug_on();
    while (d--) {}
    debug_off();
    d = 8000;
    while (d--) {}
  }
}



static void UART_Config(void)
{
  UART1_DeInit();
  UART1_Init((uint32_t)31250, UART1_WORDLENGTH_8D, UART1_STOPBITS_1, UART1_PARITY_NO,
             UART1_SYNCMODE_CLOCK_DISABLE, UART1_MODE_RX_ENABLE);

  /* Enable UART1 Half Duplex Mode*/
  UART1_Cmd(ENABLE);
}

void main(void)
{

#ifdef STM8S001
  CONFIG_UNUSED_PINS_STM8S001;
#endif

  GPIO_Init(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5, GPIO_MODE_OUT_OD_LOW_SLOW);

  debug_flash();

  CLK_DeInit();

  CLK_HSIPrescalerConfig(CLK_PRESCALER_HSIDIV1);
  CLK_SYSCLKConfig(CLK_PRESCALER_HSIDIV1);
  CLK_HSICmd(ENABLE);

  UART_Config();
  UART1_ReceiveData8();
  UART1_ClearFlag(UART1_FLAG_RXNE);


  MidiMessage m;
  parser_state s = M_INIT;

  while (1)
  {

    if (UART1_GetFlagStatus(UART1_FLAG_RXNE) != RESET) {

      char b = UART1_ReceiveData8();
      s = parser(&m, s, b);

      if (s == M_COMPLETE) {
        s = M_INIT;
        if (m.type == M_NOTE_ON) {
          GPIO_WriteHigh(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5);
        }
        if (m.type == M_NOTE_OFF) {
          GPIO_WriteLow(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5);
        }
      }

      UART1_ClearFlag(UART1_FLAG_RXNE);
    }
  }
}
