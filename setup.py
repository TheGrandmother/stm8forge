from setuptools import setup, find_packages

setup(
    name="stm8forge",
    version="1.0",
    packages=find_packages(),
    data_files=[
        ("lib/forge", ["lib/forge.c", "lib/forge.h", "lib/sdcc_stm8s.yaml"])
    ],
    entry_points={
        "console_scripts": [
            "forge = forge.forge:forge",
        ],
    },
)
