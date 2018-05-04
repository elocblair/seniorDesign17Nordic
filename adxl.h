#include "nrf_drv_spi.h"
#include "nrf_drv_gpiote.h"
#include "app_util_platform.h"


ret_code_t init_gpiote(void);

void spi_event_handler(nrf_drv_spi_evt_t const * p_event);

void spiWrite(int cs, uint8_t ADXLregister, uint8_t dataToWrite);

void spiRead(int cs, uint8_t txbuff, uint8_t* rxbuffer);
uint8_t testADXL(void);
void initADXLfor1600(void);
uint8_t* readFIFO(void);