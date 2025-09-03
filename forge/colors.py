import logging

reset = "\033[0m"
colors = {
    "red": "\033[31m",
    "green": "\033[32m",
    "yellow": "\033[33m",
    "grey": "\033[37m",
}

logger = logging.getLogger()


class Formatter(logging.Formatter):

    format_str = "%(message)s"

    FORMATS = {
        logging.DEBUG: colors["grey"] + format_str + reset,
        logging.INFO: format_str,
        logging.WARNING: colors["yellow"] + format_str + reset,
        logging.ERROR: colors["red"] + format_str + reset,
        logging.CRITICAL: colors["red"] + format_str + reset,
    }

    def format(self, record) -> str:
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)


def colorize(s: str, color="green"):
    return f"{colors[color]}{s}{reset}"
