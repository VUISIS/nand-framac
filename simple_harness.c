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
extern struct nand_device *init_nand_driver(volatile unsigned long *ioregister,
                                     struct nand_device *old_dib);

volatile unsigned long ioregister = 0;

int main()
{
  unsigned char temp_buff[NUM_BYTES];

  init_nand_driver(&ioregister, NULL);
  nand_set_register(0, 0);
  nand_wait(100);
  nand_read(temp_buff, NUM_BYTES-4);
  /*@
    loop invariant 0 <= i <= sizeof(temp_buff);
    loop assigns i, temp_buff[0 .. sizeof(temp_buff)-1];
    loop invariant \forall int j; 0 <= j < i ==> \initialized((unsigned char*) temp_buff+j);
    loop variant sizeof(temp_buff)-i;
   */
  for (int i=0; i < sizeof(temp_buff); i++) {
    temp_buff[i] = 0;
  }
  //@ assert \initialized {Here} ((unsigned char *)temp_buff + (0 .. sizeof(temp_buff)-1));
  nand_program(temp_buff, NUM_BYTES-4);
}
