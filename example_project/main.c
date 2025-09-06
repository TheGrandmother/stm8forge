#include "stm8s.h"
#include "stm8s_conf.h"
#include "midi.h"


#define BUTTON_PORT GPIOB
#define BUTTON_PIN GPIO_PIN_7
#define LED_PORT GPIOD
#define LED_PIN GPIO_PIN_0
#define POINTS_PER_VOLT 205

/**
  * @addtogroup GPIO_Toggle
  * @{
  */

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Evalboard I/Os configuration */


#define CONFIG_UNUSED_PINS_STM8S001 \
{ \
 GPIOA->DDR |= GPIO_PIN_2; \
 GPIOB->DDR |= GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_2 | GPIO_PIN_3 | GPIO_PIN_6 | GPIO_PIN_7; \
 GPIOC->DDR |= GPIO_PIN_1 | GPIO_PIN_2 | GPIO_PIN_7; \
 GPIOD->DDR |= GPIO_PIN_0 | GPIO_PIN_2 | GPIO_PIN_4 | GPIO_PIN_7;\
 GPIOE->DDR |= GPIO_PIN_5; \
 GPIOF->DDR |= GPIO_PIN_4; \
}


#define LED_GPIO_PORT  (GPIOA)
#define FUNDAMENTAL  (GPIO_PIN_1 | GPIO_PIN_3)



/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
void Delay (uint16_t nCount);
void TIMER_Configuration(void);

/* Private functions ---------------------------------------------------------*/
/* Public functions ----------------------------------------------------------*/



unsigned int f1 = 0xFF0F;



//TIM2_Prescaler_TypeDef prescale = TIM2_PRESCALER_16;
TIM2_Prescaler_TypeDef prescale = TIM2_PRESCALER_2;
uint16_t something = 1024;
void init_TIM2(void) {
  TIM2_DeInit();
  TIM2_TimeBaseInit(prescale, something);
  TIM2_PrescalerConfig(prescale, TIM2_PSCRELOADMODE_IMMEDIATE);
  // TIM2_SetAutoreload(0xfff);
  TIM2_OC3Init(TIM2_OCMODE_PWM1,
               TIM2_OUTPUTSTATE_ENABLE,
               512,
               TIM2_OCPOLARITY_HIGH
              );

  TIM2_OC3PreloadConfig(DISABLE);
  TIM2_ARRPreloadConfig(ENABLE);

  TIM2_Cmd(ENABLE);

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
  /* UART1 and UART3 configured as follow:
        - BaudRate = 230400 baud
        - Word Length = 8 Bits
        - One Stop Bit
        - No parity
        - Receive and transmit enabled
  */
  UART1_DeInit();
  UART1_Init((uint32_t)31250, UART1_WORDLENGTH_8D, UART1_STOPBITS_1, UART1_PARITY_NO,
             UART1_SYNCMODE_CLOCK_DISABLE, UART1_MODE_RX_ENABLE);

  /* Enable UART1 Half Duplex Mode*/
  UART1_Cmd(ENABLE);
}

char uart_read_byte;
/**
  * @brief  Main program.
  * @param  None
  * @retval None
  */
void main(void)
{

  CONFIG_UNUSED_PINS_STM8S001;

  /* set option bytes */
#define OPT2 0x4803
#define AFR2 0b0000100

  //GPIO_Init(GPIOC, (GPIO_Pin_TypeDef)GPIO_PIN_3, GPIO_MODE_OUT_PP_LOW_SLOW);
  GPIO_Init(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_5, GPIO_MODE_OUT_OD_LOW_SLOW);
  // GPIO_Init(GPIOB, (GPIO_Pin_TypeDef)GPIO_PIN_3, GPIO_MODE_OUT_OD_LOW_SLOW);
  // GPIO_Init(GPIOA, (GPIO_Pin_TypeDef)GPIO_PIN_1, GPIO_MODE_OUT_PP_LOW_SLOW);

  debug_flash();


  // char opt_byte = FLASH_ReadByte(OPT2);
  // if(!(opt_byte & AFR2)) {
  //   //   GPIO_WriteHigh(GPIOA, (GPIO_Pin_TypeDef)GPIO_PIN_1);
  //     uint16_t mjau = 5;
  //     while (mjau--) {
  //         Delay(f1);
  //     }
  //     // GPIO_WriteLow(GPIOA, (GPIO_Pin_TypeDef)GPIO_PIN_1);
  //     mjau = 5;
  //     while (mjau--) {
  //         Delay(f1);
  //     }
  //     FLASH_Unlock(FLASH_MEMTYPE_DATA);
  //     FLASH_ProgramOptionByte(OPT2,opt_byte | AFR2);
  //     FLASH_WaitForLastOperation(FLASH_MEMTYPE_DATA);
  // }



  CLK_DeInit();

  // Enable 16MHZ
  CLK_HSIPrescalerConfig(CLK_PRESCALER_HSIDIV1);
  CLK_SYSCLKConfig(CLK_PRESCALER_HSIDIV1);
  CLK_HSICmd(ENABLE);

  UART_Config();
  UART1_ReceiveData8();
  UART1_ClearFlag(UART1_FLAG_RXNE);


  unsigned long int mjau = 10;


  bool high = 0;
  mjau = 0;

  MidiMessage m;
  parser_state s = M_INIT;

  while (1)
  {

    /* Wait the byte is entirely received by UART1 */
    if (UART1_GetFlagStatus(UART1_FLAG_RXNE) != RESET) {


      // there is message
      high = !high;
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
