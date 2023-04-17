// Copyright (c) 2022 Provatek, LLC.

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "framework.h"
#include "driver.h"
#include "device_emu.h"

#define NAND_POLL_INTERVAL_US 10  /* polling interval in microseconds */

volatile unsigned char* driver_ioregister;

// Resets the nand device to its inital state
/*@
  requires 0 <= offset && offset <= 4;
  requires \valid((unsigned char*) driver_ioregister + offset);
  assigns *((unsigned char*)driver_ioregister+offset);
  behavior wp_typed:
    requires \separated((unsigned char*) driver_ioregister+offset, &driver_ioregister);
 */
void nand_set_register(unsigned char offset, unsigned char value)
{
	*((unsigned char*)driver_ioregister + offset) = value;
}

// Waits for device status to be ready for an action
int nand_wait(unsigned int interval_us)
{
	/* Some explanation on this timeout computation:
	 *
	 * We're trying to mimic what real Linux device drivers see: a
	 * volatile jiffies variable whose value increases
	 * monotonically with clock ticks.  The clock() function has
	 * similar behavior.  My Linux's bits/time.h indicates that
	 * clock_t ticks are always microseconds, so rather than
	 * converting microseconds to ticks using CLOCKS_PER_SEC /
	 * 1000000, I'm just adding.  Although I worry that I'm losing
	 * POSIX points by doing so, the simple addition mimics the
	 * pattern real Linux device drivers would use.
	 */
	clock_t timeout = clock() + interval_us;
	
	while(clock() < timeout) {
		if (gpio_get(PN_STATUS) == DEVICE_READY) {
			return 0;
		}
		usleep(NAND_POLL_INTERVAL_US);
	}
	return -1;
}

// Reads the data in to buffer in the nand device at offset with length of size
// Returns 0 on success
/*@
  requires \valid(buffer + (0 .. length-1));
  behavior ok:
    assumes length <= NUM_BYTES;
    assigns buffer[0 .. length-1];
    ensures \result == 0;
  behavior error:
    assumes length > NUM_BYTES;
    assigns \nothing;
    ensures \result == -1;
 */
int nand_read(unsigned char *buffer, unsigned int length)
{
	unsigned int page_size = NUM_BYTES;
	if (length > page_size) {
		return -1;
	}
  /*@
   loop invariant 0 <= length <= \at(length, Pre);
   loop invariant buffer == \at(buffer, Pre) + \at(length, Pre) - length;
   loop invariant \forall unsigned int i; 0 <= i < \at(length,Pre)-length ==> \initialized(\at(buffer, Pre)+i);
   loop assigns length, buffer, *(\at(buffer, Pre) + (0 .. \at(length, Pre)-length-1));
   loop variant length;
   */
	while (length--) {
    //@ assert \valid(\at(buffer, Pre) + (0 .. \at(length, Pre)-1));
    //@ assert \valid(buffer);
		*buffer++ = *(driver_ioregister + IOREG_DATA);
	}

	//return length;    // length is not 0 here
	return 0;
}

// Writes the data in buffer to the nand device at offset with length of size
// Returns 0 on success
/*@
  requires \valid_read(buffer + (0 .. length - 1));
  requires \valid(driver_ioregister+IOREG_DATA);
  requires \separated(buffer + (..), &driver_ioregister);
  requires \separated(buffer + (0 .. length-1), &driver_ioregister);
  requires \initialized(buffer + (0 .. length-1));
  behavior ok:
    assumes length <= NUM_BYTES;
    assigns *(driver_ioregister+IOREG_DATA);
    ensures \result == 0;
  behavior error:
    assumes length > NUM_BYTES;
    assigns \nothing;
    ensures \result == -1;
 */
int nand_program(unsigned char *buffer, unsigned int length)
{
	unsigned int page_size = NUM_BYTES;
	if (length > page_size) {
		return -1;
	}

  /*@
   loop invariant 0 <= length <= \at(length, Pre);
   loop invariant buffer == \at(buffer, Pre) + \at(length, Pre) - length;
   loop assigns length, buffer, *(driver_ioregister+IOREG_DATA);
   loop variant length;
   */
	while (length--) {
    //@ assert \valid_read(\at(buffer, Pre) + (0 .. \at(length, Pre)-1));
    //@ assert \valid_read(buffer);
    //@ assert \initialized {Pre}(buffer);
		*((unsigned char*)driver_ioregister + IOREG_DATA) = 
			*buffer++;
	}

	// return length;    // length is not 0 here
	return 0;
}

struct nand_driver get_driver()
{
	struct nand_jump_table njt = {
		.read_buffer = nand_read,
		.set_register = nand_set_register,
		.wait_ready = nand_wait,
		.write_buffer = nand_program
	};

	struct nand_driver nd = {
		.type = NAND_JUMP_TABLE,
		.operation.jump_table = njt,
	};
	return nd;
}

// Initalizes the private device information
struct nand_device *init_nand_driver(volatile unsigned long *ioregister,
	struct nand_device *old_dib) 
{
	printf("ALPHA 0 DRIVER\n");
	driver_ioregister = (unsigned char *) ioregister;
	return old_dib;  /* This driver does not use DIB. */
}

/*
volatile unsigned char driver_io[4] = {0, 0, 0, 0};
int main() {
  unsigned char buff[512];
  driver_ioregister = driver_io;
  nand_read(buff, NUM_BYTES);
}
*/
