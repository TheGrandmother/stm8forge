# stm8forge

So this is a pretty cringe project with a cringe name by someone who does not know anything about embedded development and is pretty shit at software development.
But it may against all odds help someone get started with the STM8 development on a POSIX system for people who don't want to write everything by hand or entertain the notion of using an eclipse based IDE.

I have no understanding of any of this and it is all just things that I managed to get working somehow.

Pull requests are not expected but would be very welcome.

### Acknowledgement
Major thanks goes out to [the dude who wrote this blog post](https://www.codementor.io/@hbendali/getting-started-with-stm8-development-tools-on-gnu-linux-zu59yo35x). The bulk of all the installation steps in the requirements sections are pretty much copied verbatim and a lotr of what was written here was used as the base for this.

## Usage
Just run `forge.py --cube-file my-poject.txt`
And you can then flash your device by running `ninja flash`

Forge will hopefully complain if it can't find the stuff it needs.

## Features
* Generate a ninja build file to build a project using SDCC
* **AUTOMATES DEAD CODE ELIMINATION USING `stm8dce`**
* Automatically resolves the used peripherals from the STM8CubeMx report file (the .txt ones) and include the appropriate files from the `STM8S_StdPeriph`library (not included)
* Setup a build target for flashing a device using stm8flash matching the MCU used
* Support building for debugging
* Will create a file (`serve_openocd`) to start an openocd instance matching the MCU used
* Has cringy colors in the output like some fancy kind of thing
* Pretends to be robust and do some error checking
* Has lofty plans to add code generation
* Can generate a CCLS config file

## To do
* Lose interest, move on to something else and never touch this again
* Add code generation for peripherals
* Better cli interface
* Dockerfile for dependencies

## Requirements
These are the things that you pretty much have to have.

### python
Version 3.something, probably at least 10.
Can be found wherever you get your python installations from  

### [ninja](https://ninja-build.org/)
Used for the actuall building

### [SDCC](https://sdcc.sourceforge.net/)
3.5 or higher i guess.
This is how i got mine, your mileage may vary:
```
# download the latest version
$ wget https://sourceforge.net/projects/sdcc/files/sdcc-linux-amd64/4.3.0/sdcc-4.3.0-amd64-unknown-linux2.5.tar.bz2
$ tar -xjf ./sdcc-4.3.0-amd64-unknown-linux2.5.tar.bz2
$ cd sdcc
$ sudo cp -r * /usr/local
```

### [stm8dce](https://github.com/CTXz/STM8-DCE)
stm8dce is used for the dead code elimination. stm8forge works without it but your artifacts will
unironically be orders of magnitude bigger.
```
$ pip install stm8dce
```

### [STM8CubeMx](https://www.st.com/en/development-tools/stm8cubemx.html)
Whatever version is avaliable, have fun.

### [STM8S_StdPeriph_Lib](https://my.st.com/content/my_st_com/en/products/embedded-software/mcus-embedded-software/stm8-embedded-software/stsw-stm8069.html)
Download the STM8S standard peripheral library which is hidden away behind some moronic license.

You will need to patch the libs to make it compatible with SDCC.
[](https://github.com/gicking/SPL_2.2.0_SDCC_patch)

Your mileage may vary here as well. I had some issues getting rid of a bunch of warnings so i needed to
add `void _assert_failed(void);` to my main file to get SDCC to shut up.

### stm8flash
What forge will use to flash your thing
```
$ git clone https://github.com/vdudouyt/stm8flash.git
$ cd stm8flash
$ make
$ sudo make install
```

## Optional debug stuff

### stm8-gdb
This is kinda fun if you are into debugging.
But also a bit of a hassle and takes a while.

```
$ wget https://sourceforge.net/projects/stm8-binutils-gdb/files/stm8-binutils-gdb-sources-2021-07-18.tar.gz/download -O stm8-binutils-gdb-sources-2021-07-18.tar.gz

$ tar -xf stm8-binutils-gdb-sources-2021-07-18.tar.gz
$ cd stm8-binutils-gdb-sources
$ ./patch_binutils.sh
$ ./configure_binutils.sh
$ cd binutils-2.30
$ make
$ sudo make install
```
***Note***: To get the TUI working, which is fun, you will have to install the development files for ncursesw. If you don*t do this you will get no indication that TUI is disabled.


### [OpenOCD](https://openocd.org/)
This is neat and sets creates a connection between the MCU and your computer that gdb (or other debuggers i guess) can use.
