#include "nrf_drv_twi.h"
#include "nrf_drv_gpiote.h"
#include "nrf_delay.h"
#include "app_util_platform.h"

static ret_code_t twi_master_init(void);

bool init_i2c(void);
void initBosch(void);
uint8_t* readEuler();