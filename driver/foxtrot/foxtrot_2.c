// Copyright (c) 2022 Provatek, LLC.

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
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
// Returns number of bytes read
/*@
  requires \valid(buffer + (0 .. length-1));
  requires \separated(buffer + (0 .. length-1), &driver_ioregister);
  behavior ok:
    assumes length <= NUM_BYTES;
    assigns buffer[0 .. length-1];
    ensures \result == 0;
  behavior error:
    assumes length > NUM_BYTES;
    assigns \nothing;
    ensures \result == -1;
 */
int nand_read(unsigned char* buffer, unsigned int length)
{
	unsigned int page_size = NUM_BYTES;
	if (length > page_size) {
		return -1;
	}

  /*@
   loop invariant 0 <= i <= length;
   loop invariant \forall unsigned int j; 0 <= j < i ==> \initialized(buffer+j);
   loop assigns length, *(buffer + (0 .. length-1));
   loop variant length-i;
   */
	for (unsigned int i = 0; i < length; i++) {
    //@ assert \valid(buffer + (0 .. length-1));
    //@ assert \valid(buffer);
		buffer[i] = *((unsigned char*)driver_ioregister + IOREG_DATA);
	}

	return length;
}

// Writes the data in buffer to the nand device at offset with length of size
// Returns number of bytes wrote
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
int nand_program(const unsigned char* buffer, unsigned int length)
{
	unsigned int page_size = NUM_BYTES;
	if (length > page_size) {
		return -1;
	}

  /*@
   loop invariant 0 <= i <= length;
   loop invariant \forall unsigned int j; 0 <= j < i ==> \initialized(buffer+j);
   loop assigns i, *(driver_ioregister+IOREG_DATA);
   loop variant length-i;
   */
	for (unsigned int i = 0; i < length; i++) {
    //@ assert \valid_read(buffer + (0 .. length-1));
    //@ assert \valid_read(buffer);
    //@ assert \initialized {Pre} (buffer);
		*((unsigned char*)driver_ioregister + IOREG_DATA) = buffer[i];
	}

	return length;
}

// Performs functionality simular to exec_op in linux kernal
// Returns 0 on success
// Intended BUG: Modulo the amount of instructions we handle
/*@
 requires \valid(commands);
 */
int exec_op(struct nand_operation *commands)
{
	struct nand_op_instr command;
	unsigned int addr_len;
  //@ ghost unsigned int num_cmds = 0;
  /*@
   loop invariant 0 <= i <= commands->ninstrs;
   loop invariant 0 <= num_cmds <= commands->ninstrs;
   loop invariant num_cmds == i;
   loop variant commands->ninstrs - i;
   */
//	for (int i = 0; i < commands->ninstrs; i = i + 1) {
	for (int i = 0; i < commands->ninstrs; i = (i+1) % 8) {

    //@ ghost num_cmds++;
		command = commands->instrs[i];
		switch (command.type)
		{
		case NAND_OP_CMD_INSTR:
			nand_set_register(IOREG_COMMAND, 
				command.ctx.cmd.opcode);
			break;
		case NAND_OP_ADDR_INSTR:
			addr_len = command.ctx.addr.naddrs;
      /*@
       loop invariant 0 <= j <= addr_len;
       loop assigns j, *(driver_ioregister + IOREG_ADDRESS);
       loop variant addr_len - j;
      */
			for(int j = 0; j < addr_len; j++) {
				nand_set_register(IOREG_ADDRESS, 
					command.ctx.addr.addrs[j]);
			}
			break;
  /*
		case NAND_OP_DATA_IN_INSTR:
			if (command.ctx.data.len !=
				nand_program(command.ctx.data.buf.in, 
				command.ctx.data.len))
				return -1;  / * exceeded page * /
			break;
		case NAND_OP_DATA_OUT_INSTR:
			if (command.ctx.data.len !=
				nand_read(command.ctx.data.buf.out,
				command.ctx.data.len))
				return -1;  / * exceeded page * /
			break;
		case NAND_OP_WAITRDY_INSTR:
			if (nand_wait(command.ctx.waitrdy.timeout_ms))
				return -1;  / * timeout * /
			break;
		default:
			printf("Unknown exec_op data.\n");
			return -1;
    */
		}
	}
	return 0;
}

struct nand_driver get_driver()
{
	struct nand_driver nd = {
		.type = NAND_EXEC_OP,
		.operation.exec_op = exec_op,
	};
	return nd;
}

// Initalizes the private device information
struct nand_device *init_nand_driver(volatile unsigned long *ioregister,
	struct nand_device *old_dib)
{
	printf("FOXTROT 2 DRIVER\n");
	driver_ioregister = (unsigned char *) ioregister;
	return old_dib;  /* This driver does not use DIB. */
}
