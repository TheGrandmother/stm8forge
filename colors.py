reset = "\033[0m"
red = "\033[31m"
green = "\033[32m"
yellow = "\033[33m"


def warning(s):
    print(f"{yellow}WARN:\t{s}{reset}")


def success(s):
    print(f"{green}PASS:\t{s}{reset}")


def error(s):
    print(f"{red}ERROR:\t{s}{reset}")
