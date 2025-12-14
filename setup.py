from setuptools import setup, find_packages

setup(
    name="stm8forge",
    version="1.0",
    packages=find_packages(),
    entry_points={
        "console_scripts": [
            "forge = forge.forge:forge",
        ],
    },
)
