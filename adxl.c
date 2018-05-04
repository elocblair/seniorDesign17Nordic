#include "nrf_drv_spi.h"
#include "nrf_drv_gpiote.h"
#include "app_util_platform.h"
#include "adxl.h"



#define SPI_INSTANCE  2 /**< SPI instance index. */
#define CS_ADXL2_PIN  6 /**< SPI CS Pin.*/
#define CS_ADXL1_PIN  17
#define CS_ADXL1_PIN_EVAL 3
#define CS_ADXL2_PIN_EVAL 8

static const nrf_drv_spi_t spi = NRF_DRV_SPI_INSTANCE(SPI_INSTANCE);
static volatile bool spi_xfer_done; 
nrf_drv_spi_config_t spi_config = {
	11, 					  	//sck  
	13, 							//mosi 
	12, 							//miso
	NRF_DRV_SPI_PIN_NOT_USED, 	//slave select
	APP_IRQ_PRIORITY_HIGH,		//app_button_disable interrupt priority with soft device
	0xFF,
	NRF_DRV_SPI_FREQ_4M,
	NRF_DRV_SPI_MODE_0,
	NRF_DRV_SPI_BIT_ORDER_MSB_FIRST, 
};

/****************************
*
*   spi event handler   
*		 called after contents of spi buffer have been transferred
*		 sets chip select pin high 
*		 allows the application to continue past __WFE(); 
*												   wait for event
*
****************************/
void spi_event_handler(nrf_drv_spi_evt_t const * p_event)
{
	spi_xfer_done = true;
}


ret_code_t init_gpiote(void){
	ret_code_t err_code;
	if(!nrf_drv_gpiote_is_init())
	{
		err_code = nrf_drv_gpiote_init();
	}
	if (err_code == 8){
		return err_code;
	}
	else{return 0;}
}

void spiWrite(int cs, uint8_t ADXLregister, uint8_t dataToWrite){
	uint8_t txBuffer[2] = {ADXLregister << 1, dataToWrite};
	uint8_t* txAddress = &txBuffer[0];	
	nrf_drv_gpiote_out_clear(cs);
	nrf_drv_spi_transfer(&spi, txAddress , 2, NULL, 0);
	while (!spi_xfer_done)
    {
        __WFE();
    }
	nrf_drv_gpiote_out_set(cs);
	spi_xfer_done = false;
}
void spiRead(int cs, uint8_t txbuff, uint8_t* rxbuffer){
	uint8_t txbuffer[2] = {txbuff << 1 | 0x01, 0x00};
	uint8_t* txAddress = &txbuffer[0];
	nrf_drv_gpiote_out_clear(cs);
	nrf_drv_spi_transfer(&spi, txAddress , 2, rxbuffer, 2);
	while (!spi_xfer_done)
    {
        __WFE();
    }
	nrf_drv_gpiote_out_set(cs);
	spi_xfer_done = false;
}

uint8_t testADXL(){
	uint8_t rxBuffer[2];
	spiRead(CS_ADXL1_PIN, 0x00, &rxBuffer[0]);
	
	uint8_t rxBuffer2[2];
	spiRead(CS_ADXL2_PIN, 0x00, &rxBuffer2[0]);
	
	if(rxBuffer[1] == 173 && rxBuffer2[1] ==  173){
		return 0;
	}
	else if(rxBuffer[1] == 173 || rxBuffer2[1] == 173){
		return 1;
	}
	else return 2;
}

void initSPI(void){
		APP_ERROR_CHECK(nrf_drv_spi_init(&spi, &spi_config, spi_event_handler));
}

void initADXLfor1600(){
	 //1600Hz application
	//
	uint8_t fifo_ctl = 0x3A;
	spiWrite(CS_ADXL1_PIN, fifo_ctl, 0x03);

	uint8_t timing = 0x3D;
	spiWrite(CS_ADXL1_PIN, timing, 0x40); // 0x40 = 1600Hz, 0x60 = 3200Hz

	uint8_t measure = 0x3E;
	spiWrite(CS_ADXL1_PIN, measure, 0x0B);

	uint8_t power_ctl = 0x3F;
	spiWrite(CS_ADXL1_PIN, power_ctl, 0x1F);
	
	
}

uint8_t* readFIFO(void){
	uint8_t rxBuffer1[247];
	uint8_t readFifo[1] = {0x85};
	uint8_t* readFifoAddress = &readFifo[0];
	
	uint8_t* rxBufferAddress = &rxBuffer1[0];
	nrf_drv_gpiote_out_clear(CS_ADXL1_PIN);
	nrf_drv_spi_transfer(&spi, readFifoAddress, 1, rxBufferAddress, 247);
	while (!spi_xfer_done)
	{
		__WFE();
	}
	nrf_drv_gpiote_out_set(CS_ADXL1_PIN);
	spi_xfer_done = false;	
	return rxBufferAddress;
}
