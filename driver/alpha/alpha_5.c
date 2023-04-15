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
// Intended BUG: Read will not stop if not a multiple of 8
/*@
  requires \valid(buffer + (0 .. length-1));
  requires \separated(buffer + (0 .. length-1), &driver_ioregister);
  requires \separated(buffer + (0 .. length-1), &buffer);
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
	int i = 0;

	if (length > page_size) {
		return -1;
	}

  /*@
   loop invariant 0 <= i <= length;
   loop assigns i, buffer[0 .. length-1];
   loop variant length-i;
  */
	while (i != length) {
    /*@
     loop invariant 0 <= j <= 8;
     loop invariant i + j <= length;
     loop invariant \forall int k; 0 <= k < j ==> \initialized(buffer + i+k);
     loop invariant \forall int k; 0 <= k < length ==> \initialized(buffer + k);
     loop assigns j, buffer[i .. i+7];
     loop variant 8 - j;
     */
		for (int j = 0; j < 8; j++) {
      //@ assert \valid(buffer + (0 .. length-1));
      //@ assert \valid(buffer);
			*(buffer+i+j) = *((unsigned char*)driver_ioregister + 
				IOREG_DATA);
		}
		i += 8;
	}

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
    //@ ghost unsigned char *old_buffer = buffer;
    //@ assert \initialized {Pre}(buffer);
		*((unsigned char*)driver_ioregister + IOREG_DATA) = 
			*buffer++;
    //@ assert buffer == old_buffer + 1;
	}

	// return length;  // Length is not zero here
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
struct nand_device *init_nand_driver(volatile unsigned char *ioregister,
	struct nand_device *old_dib)
{
	printf("ALPHA 5 DRIVER\n");
	driver_ioregister = ioregister;
	return old_dib;  /* This driver does not use DIB. */
}
