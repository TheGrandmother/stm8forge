from enum import Enum
import re
import forge.colors as colors


class Peripheral:
    n = 0

    def __hash__(self):
        return f"{self.__class__.__name__}_{self.n}".__hash__()

    def __eq__(self, b):
        return self.__hash__() == b.__hash__()


class Dependency(Peripheral):
    pass


class Adc(Peripheral):
    def __init__(self, n):
        self.n = n
        self.sources = [f"stm8s_adc{n}.c"]


class Awu(Peripheral):
    def __init__(self):
        self.sources = ["stm8s_awu.c"]


class Beep(Peripheral):
    def __init__(self):
        self.sources = ["stm8s_beep.c"]


class Can(Peripheral):
    def __init__(self):
        self.sources = ["stm8s_can.c"]


# Crystall stuff.... not sure how to deal with these
class Rcc(Peripheral):
    def __init__(self):
        self.sources = []  # ?


class Rtc(Peripheral):
    def __init__(self):
        self.sources = ["stm8s_clk.c"]


class Uart(Peripheral):
    def __init__(self, n):
        self.n = n
        self.sources = [f"stm8s_uart{n}.c", "stm8s_clk.c"]


class Tim(Peripheral):
    def __init__(self, n):
        self.n = n
        self.sources = [f"stm8s_tim{n}.c"]


class I2C(Peripheral):
    def __init__(self):
        self.sources = ["stm8s_i2c.c"]


class Spi(Peripheral):
    def __init__(self):
        self.sources = ["stm8s_spi.c"]


class Clk(Peripheral):
    def __init__(self):
        self.sources = ["stm8s_clk.c"]


class Gpio(Peripheral):
    def __init__(self):
        self.sources = ["stm8s_gpio.c"]


class Exti(Dependency):
    def __init__(self):
        self.sources = ["stm8s_exti.c"]


class Flash(Dependency):
    def __init__(self):
        self.sources = ["stm8s_flash.c"]


# These wild bois are missing
# stm8s_awu.c
# stm8s_clk.c
# stm8s_itc.c
# stm8s_iwdg.c
# stm8s_rst.c
# stm8s_wwdg.c

cube_peripherals = {
    "ADC": Adc(1),
    "ADC1": Adc(1),
    "ADC2": Adc(2),
    "AWU": Awu(),
    "BEEP": Beep(),
    "CAN": Can(),
    "RCC": Rcc(),
    "TIM1": Tim(1),
    "TIM2": Tim(2),
    "TIM3": Tim(3),
    "TIM4": Tim(4),
    "TIM5": Tim(5),
    "TIM6": Tim(6),
    "USART1": Uart(1),
    "USART2": Uart(2),
    "USART3": Uart(3),
    "USART4": Uart(4),
    "UART1": Uart(1),
    "UART2": Uart(2),
    "UART3": Uart(3),
    "UART4": Uart(4),
    "I2C1": I2C(),
    "SPI1": Spi(),
    "FLASH": Flash(),
    "EXTI": Exti(),  # This should be passed as a real dependency
}


class State(Enum):
    INFO = "_"
    PERIPHERALS = "PERIPHERALS"
    PINS = "Pin Nb"


def parse_cube_file(file):
    with file as cube_file:
        state = State.INFO
        mcu_type = None
        used_peripherals = set()
        for line in cube_file:
            if line.strip() == "":
                continue
            if state == State.INFO:
                [name, value, *_] = re.split(r"\s+", line)
                if name == "MCU":
                    mcu_type = value.strip()
                    continue
                if name.strip() == "PERIPHERALS":
                    state = State.PERIPHERALS
                    continue
            if state == State.PERIPHERALS:
                [name, *_] = re.split(r"\s+", line)
                if name == "Pin":
                    state = State.PINS
                    continue
                if name in cube_peripherals:
                    perp = cube_peripherals[name]
                    used_peripherals.add(perp)
                elif name != "SYS":
                    colors.warning(
                        "Fyi, Forge does not recognize "
                        + f"{name} as a peripheral"
                    )
            if state == State.PINS:
                [_, _, functions, *_] = re.split(r"\s+", line)
                if functions in ["GPIO_Output", "GPIO_Input"]:
                    used_peripherals.add(Gpio())
    return mcu_type, used_peripherals
