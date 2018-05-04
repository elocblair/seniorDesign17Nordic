#include "nrf_drv_spi.h"
#include "nrf_drv_gpiote.h"
#include "app_util_platform.h"
#include "fram.h"
#include "adxl.h"

#define SPI_INSTANCE  2
#define CS_FRAM       4
#define CS_FRAM_EVAL  7

int FramRegister = 0;
int readFramRegister = 0;
bool FRAMFull = false;
bool framReadDone = false;

static const nrf_drv_spi_t spi = NRF_DRV_SPI_INSTANCE(SPI_INSTANCE);
static volatile bool spi_xfer_done; 

void initFRAM1600(){
	uint8_t FRAMtx[1] = {0x06};  								//write enable
	uint8_t* addrFRAMtx = &FRAMtx[0];
	nrf_drv_gpiote_out_clear(CS_FRAM);
	nrf_drv_spi_transfer(&spi, addrFRAMtx,1, NULL,0);
	while (!spi_xfer_done)
	{
		 __WFE();
	}
	nrf_drv_gpiote_out_set(CS_FRAM);
	spi_xfer_done = false;
	
	uint8_t FRAMtx2[2] = {0x01,0x42};
	uint8_t* addrFRAMtx2 = &FRAMtx2[0];
	nrf_drv_gpiote_out_clear(CS_FRAM);
	nrf_drv_spi_transfer(&spi,addrFRAMtx2,2,NULL,0);
	while (!spi_xfer_done)
	{
		 __WFE();
	}
	nrf_drv_gpiote_out_set(CS_FRAM);
	spi_xfer_done = false;
	
	nrf_drv_gpiote_out_clear(CS_FRAM);						 //write enable again
	nrf_drv_spi_transfer(&spi, addrFRAMtx,1, NULL,0);
	while (!spi_xfer_done)
	{
		 __WFE();
	}
	nrf_drv_gpiote_out_set(CS_FRAM);
	spi_xfer_done = false;
	
	uint8_t FRAMtx3[2] = {0x05,0x00};
	uint8_t* addrFRAMtx3 = &FRAMtx3[0];
	uint8_t FRAMrx3[2];
	uint8_t* addrFRAMrx3 = &FRAMrx3[0];
	nrf_drv_gpiote_out_clear(CS_FRAM);					 //read status register
	nrf_drv_spi_transfer(&spi, addrFRAMtx3,1,addrFRAMrx3,2);
	while (!spi_xfer_done)
	{
		 __WFE();
	}
	nrf_drv_gpiote_out_set(CS_FRAM);
	spi_xfer_done = false;


}

uint8_t* readFRAM(){
		if(!framReadDone){
		//SEGGER_RTT_WriteString(0, "HEHRER");
		uint8_t readFRAMBuffer[4];
		readFRAMBuffer[0] = 0x03;
		readFRAMBuffer[1] = readFramRegister >> 16;
		readFRAMBuffer[2] = readFramRegister >> 8;
		readFRAMBuffer[3] = readFramRegister;
		uint8_t receiveBuffer[24];
		receiveBuffer[22] = 0xAA;
		receiveBuffer[23] = 0xBB;
		uint8_t* readFRAMAddy = &readFRAMBuffer[0];
		uint8_t* receiveBufferAddy = &receiveBuffer[0];
		nrf_drv_gpiote_out_clear(CS_FRAM);
		nrf_drv_spi_transfer(&spi, readFRAMAddy, 4, receiveBufferAddy, 22);
		while (!spi_xfer_done)
		{
			__WFE();
		}
		nrf_drv_gpiote_out_set(CS_FRAM);
		spi_xfer_done = false;	
		
		uint8_t* addy = &receiveBuffer[4];
		
		
		
		readFramRegister += 18;
		if(readFramRegister > 261900){
			framReadDone = true;
			nrf_drv_gpiote_out_clear(20);
			nrf_drv_gpiote_out_set(15);
		}
		return addy;
		
	}

	//SEGGER_RTT_printf(0, "this value should be 100 = %d\n", receiveBuffer[252]);
}
