#include "nrf_drv_twi.h"
#include "nrf_drv_gpiote.h"
#include "nrf_delay.h"
#include "app_util_platform.h"
#include "bosch_BNO055.h"


#define TWI_SCL_M                26   //!< Master SCL pin
#define TWI_SDA_M                25   //!< Master SDA pin


#define MASTER_TWI_INST 0
uint8_t buffRx[100];
uint8_t BOSCH_ADDRESS = 0x29;
static const nrf_drv_twi_t m_twi_master = NRF_DRV_TWI_INSTANCE(MASTER_TWI_INST);

uint8_t set_power_mode_normal[2] = {0x3E, 0x01};
uint8_t swap_page1[2] = {0x07, 0x01};
uint8_t swap_page0[2] = {0x07, 0x00};
uint8_t read_acc_settings[1] = {0x08};
uint8_t enable_nm_int[2] = {0x10, 0xC0};
uint8_t int_mask_nm[2] = {0xF0, 0xC0};
uint8_t am_thres[2] = {0x11, 0x12};
uint8_t am_duration[2] = {0x12, 0xFF};
uint8_t nm_40seconds[2] = {0x16, 0x2B};
uint8_t operation_mode_9dof[2] = {0x3D, 0x0C};

/**
 * @brief Initialize the master TWI
 *
 * Function used to initialize master TWI interface that would communicate with simulated EEPROM.
 *
 * @return NRF_SUCCESS or the reason of failure
 */
static ret_code_t twi_master_init(void)
{
    ret_code_t ret;
    const nrf_drv_twi_config_t config =
    {
       .scl                = TWI_SCL_M,
       .sda                = TWI_SDA_M,
       .frequency          = NRF_TWI_FREQ_400K,
       .interrupt_priority = APP_IRQ_PRIORITY_HIGH
    };
	//__nop();
    do
    {
        ret = nrf_drv_twi_init(&m_twi_master, &config, NULL, NULL);
        if(NRF_SUCCESS != ret)
        {
            break;
        }
        nrf_drv_twi_enable(&m_twi_master);
    }while(0);
    return ret;
}

bool init_i2c(){
	
	nrf_delay_ms(500); //on power up the bosch needs this time to initialize
	ret_code_t i2cStatus;
	i2cStatus = twi_master_init();
	if (i2cStatus != NRF_SUCCESS)
	{
			return false;
	}
	else return true;
}

void initBosch(){
		/****************************
	*
	*  normal power
	*
	****************************/
	uint8_t txBuff[2] = {0x3E,0x01};  //Power mode = normal
	uint8_t* addrTx = &txBuff[0];
	uint8_t rxBuff[1];
	uint8_t* addrRx = &rxBuff[0];

	ret_code_t i2cErr;
	//write
	i2cErr = nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,2,false);
	if (i2cErr == NRF_ERROR_INTERNAL)
	{
		//SEGGER_RTT_WriteString(0, "i2cError 1\n");
	}

	//read
	i2cErr = nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,1,false);
	if (i2cErr == NRF_ERROR_INTERNAL)
	{
		//SEGGER_RTT_WriteString(0, "i2cError 3\n");
	}
	i2cErr = nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	if (i2cErr == NRF_ERROR_INTERNAL)
	{
		//SEGGER_RTT_WriteString(0, "i2cError 4\n");
	}

	/****************************
	*
	* change page
	* 	this changes what about half of the registers are for additional configurations
	*
	****************************/
	txBuff[0] = 0x07;				//switch from page 0 to page 1 
	txBuff[1] = 0x01;
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,2,false);
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	
	

	/*
	*  Bosch interrupt settings
	*/
	txBuff[0] = 0x08;      //accelerometer settings to +/- 4G 
	nrf_drv_twi_tx(&m_twi_master, BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	//SEGGER_RTT_printf(0,"13 = %d\n", rxBuff[0]);
	
	txBuff[0] = 0x10; //interrupt enable
	txBuff[1] = 0xC0; // enable no motion int
	nrf_drv_twi_tx(&m_twi_master, BOSCH_ADDRESS, addrTx,2,false);
	nrf_drv_twi_tx(&m_twi_master, BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	//SEGGER_RTT_printf(0,"C0 = %d\n", rxBuff[0]);
	
	txBuff[0] = 0x0F; //interrupt mask, value to write is still 0x40 for any motion 
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,2,false);
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	//SEGGER_RTT_printf(0,"C0 = %d\n", rxBuff[0]);
	
	
	txBuff[0] = 0x11; // any motion threshold
	txBuff[1] = 0x12; // threshold 7.81mg per LSB 
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,2,false);
	nrf_drv_twi_tx(&m_twi_master, BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	//SEGGER_RTT_printf(0,"12 = %d\n", rxBuff[0]);
	
	txBuff[0] = 0x12; // acc interrupt settings 2 LSB == any motion duration
	txBuff[1] = 0xFF;
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,2,false);
	nrf_drv_twi_tx(&m_twi_master, BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	//SEGGER_RTT_printf(0,"1C = %d\n", rxBuff[0]);
	
	txBuff[0] = 0x16;
	uint8_t fiveSeconds = 0x09;
	uint8_t tenSeconds = 0x13;
	uint8_t fifteenSeconds = 0x1C;
	uint8_t twentySeconds = 0x21;
	uint8_t fortySeconds = 0x2B;
	uint8_t eightyEightSeconds = 0x41;
	txBuff[1] = fortySeconds; // no motion 5 seconds will trigger interrupt
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,2,false);
	nrf_drv_twi_tx(&m_twi_master, BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	//SEGGER_RTT_printf(0,"0B = %d\n", rxBuff[0]);
	

	txBuff[0] = 0x15;
	txBuff[1] = 0x12;
	nrf_drv_twi_tx(&m_twi_master, BOSCH_ADDRESS,addrTx,2,false);
	nrf_drv_twi_tx(&m_twi_master, BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	//SEGGER_RTT_printf(0,"12 = %d\n", rxBuff[0]);

	/****************************
	*
	*  change back to default page
	*
	****************************/
	txBuff[0] = 0x07;				//back to page 0
	txBuff[1] = 0x00;
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,2,false);
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);
	/****************************
	*
	*  init complete, sensor can be read 
	*		ADD error check
	*
	****************************/
	txBuff[0] = 0x3D;				//operation mode = gyro only ********sensor powers on in config mode
	txBuff[1] = 0x0C;
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,2,false);
	nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,1,false);
	nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,1);

	if (rxBuff[0] == 0x0C){
		//SEGGER_RTT_WriteString(0, "Main BNO055 initialized\n");
	}
	
	
}

uint8_t* readEuler(){
		
		uint8_t i2cTx[1] = {0x1A};
		uint8_t* addrTx = &i2cTx[0];
		uint8_t* addrRx = &buffRx[7];
		nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,1,true); //i2c read to address located in i2cTx[0]
		nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRx,6);
		/*SEGGER_RTT_printf(0, "%d\t",buffRx[7]);
		SEGGER_RTT_printf(0, "%d\t",buffRx[8]);
		SEGGER_RTT_printf(0, "%d\t",buffRx[9]);
		SEGGER_RTT_printf(0, "%d\t",buffRx[10]);
		SEGGER_RTT_printf(0, "%d\n",buffRx[11]);*/
		uint8_t* addrRxGrav = &buffRx[13];
		i2cTx[0] = 0x08;
		nrf_drv_twi_tx(&m_twi_master,BOSCH_ADDRESS,addrTx,1,true); //i2c read to address located in i2cTx[0]
		nrf_drv_twi_rx(&m_twi_master,BOSCH_ADDRESS,addrRxGrav,6);
		return &buffRx[7];
}