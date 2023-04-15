#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "framework.h"
#include "driver.h"
#include "device_emu.h"

extern void nand_set_register(unsigned char offset, unsigned char value);
extern int nand_wait(unsigned int interval_us);
extern int nand_read(unsigned char *buffer, unsigned int length);
extern int nand_program(unsigned char *buffer, unsigned int length);
extern int exec_op(struct nand_operation *);
extern struct nand_device *init_nand_driver(volatile unsigned char *ioregister,
                                     struct nand_device *old_dib);

volatile unsigned char ioregister[4] = { 0, 0, 0, 0};

unsigned char read_buff[NUM_BYTES];
unsigned char write_buff[NUM_BYTES];
#define NUM_OPS 10

int main()
{
  const unsigned char addrtmp[1] = { 'a'};
  unsigned char addr_buff[3] = { 0, 0, 0};

  init_nand_driver(ioregister, NULL);

  /*@
   loop invariant 0 <= i <= NUM_BYTES;
   loop assigns i, write_buff[0 .. NUM_BYTES-1];
   loop variant NUM_BYTES-i;
   */
  for (int i=0; i < NUM_BYTES; i++) {
    write_buff[i] = 0;
  }

  /*@
   loop invariant 0 <= i <= NUM_BYTES;
   loop assigns i, read_buff[0 .. NUM_BYTES-1];
   loop variant NUM_BYTES-i;
   */
  for (int i=0; i < NUM_BYTES; i++) {
    read_buff[i] = 0;
  }
  struct nand_op_cmd_instr cmd = { 0 };
  struct nand_op_instr cmd_instr = { NAND_OP_CMD_INSTR, { cmd, addr, data_in, waitrdy }};
  //@ assert \initialized {Here} (&cmd_instr);
  struct nand_op_instr instrs[NUM_OPS] = {
    cmd_instr, cmd_instr, cmd_instr, cmd_instr, cmd_instr,
    cmd_instr, cmd_instr, cmd_instr, cmd_instr, cmd_instr
  };

  struct nand_operation op = { instrs, NUM_OPS };
  //@ assert \initialized {Here} (&instrs[0 .. NUM_OPS-1]);
  //@ assert \initialized {Here} (op.instrs + (0 .. NUM_OPS-1));
  exec_op(&op);
}
