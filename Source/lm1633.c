//*****************************************************************************
//	Design Stellaris Contest Entry LM1633
//	Uninterruptable Solar Power Supply
//*****************************************************************************

// includes
#include "hw_ints.h"
#include "hw_memmap.h"
#include "hw_types.h"
#include "hw_pwm.h"
#include "debug.h"
#include "gpio.h"
#include "pwm.h"
#include "sysctl.h"
#include "diag.h"
#include "osram96x16.h"
#include "watchdog.h"
#include "adc.h"
#include "timer.h"
#include "interrupt.h"
#include <stdio.h>
#include <math.h>
#include <string.h>
  
// types
typedef unsigned int Word32;
typedef signed int SWord32;
typedef unsigned short Word16;
typedef signed short SWord16;
typedef unsigned char BYTE;
typedef BYTE bool;

// defines

// program flag bits
#define FLAG_BUTTON             0           // Debounced state of the button
#define FLAG_DEBOUNCE_LOW       1           // Low bit of the debounce clock
#define FLAG_DEBOUNCE_HIGH      2           // High bit of the debounce clock
#define FLAG_BUTTON_PRESS       3           // The button was just pressed
#define FLAG_SWITCHING			4			// Switching is enabled
#define FLAG_LOCK				5			// Locked to mains waveform
#define FLAG_ZXPHASE			6			// Phase polarity of mains
#define FLAG_RELAY				7			// Mirror of relay state
#define FLAG_NCOPHASE			8			// Phase polarity of NCO
#define FLAG_RATED				9			// At rated voltage
#define FLAG_LOAD_HIGH			10			// Load too high
	
//*****************************************************************************
//
// The GPIOs for the push button, user LED and relay control.
//
//*****************************************************************************
#define PUSH_BUTTON             GPIO_PIN_4
#define USER_LED                GPIO_PIN_5
#define RELAY					GPIO_PIN_4
#define MAINS_ZX				GPIO_PIN_6
 
// Transformer low side voltage RMS
#define TXPRI_VOLTAGE 9
// Transformer high side voltage RMS
#define TXSEC_VOLTAGE 240

// Desired output voltage RMS (before changover)
#define OUTPUT_VOLTAGE 230

// Square root of 2	constant
#define SQRT2 1.41421356237

// Multiplier to convert sum of absolute value to approximate RMS value (PI/(2*Sqrt2))
#define ABS2RMS 1.1107207345

// Full scale DC voltage 
#define VDC_FULLSCALE 23.3

// Minimum DC voltage
#define VDC_MIN 16.0

// Full scale DC current 
#define IDC_FULLSCALE 4.34

// Full scale AC voltage
#define VAC_FULLSCALE 600.0

// Analog channel allocations
#define CHAN_VDC 0
#define CHAN_LOAD_AMPS 1
#define CHAN_VAC 2
#define CHAN_INV_AMPS 3
// Psuedo channel 
#define CHAN_FREQ 4
#define CHAN_MAINS 5
	  
// Minimum duty cycle
#define MINIMUM_DUTY 20

//
// main control interrupt rate
//
#define TIMER_FREQ 20000

/// Nominal AC frequency in Hz
#define NOM_FREQ 50

// Minimum AC lock frequency in Hz
#define MIN_FREQ 45
		   
// Maximum AC lock frequency in Hz
#define MAX_FREQ 65

// Frequency of capture timer in Hz
#define CAPTURE_FREQ 20000000Lu

// Minimum AC lock period in jiffies
#define MIN_PERIOD (CAPTURE_FREQ / MAX_FREQ)
// Maximum AC lock period in jiffies
#define MAX_PERIOD (CAPTURE_FREQ / MIN_FREQ)

// nominal phase velocity as 8.16 fixed point value
#define NOM_STEP (((Word32)NOM_FREQ << 25)/TIMER_FREQ)

// The phase lock range 512 = 360 degrees
// 5 degrees
#define PHASE_LOCK_RANGE 7

/// one second worth of ADC measurements to determine DC offsets
#define INTEGRATIONS 20000

// variables

//*****************************************************************************
//
// A set of flags used to track the state of the application.
//
//*****************************************************************************
static volatile Word32 g_ulFlags;		// Program flag bits
static SWord32 Period;					// 100% PWM duty value
static volatile Word32 index=0;			// NCO phase << 16
static volatile Word32 index_step;		// NCO phase velocity
static Word16 indexb;					// NCO sample index (0..511)
static SWord16 vac_gain;				// Gain of voltage component
static volatile Word32 ticker;			// Timer ticker
static SWord32 MAXIMUM_DUTY;			// Maximum duty cycle
static SWord16 dc_offsets[4];			// DC offsets of AC channels

// Mark position for last zero crossing
static Word32 zx_mark=0;	

// Period of ZX in timer0 ticks
static volatile Word32 zx_period;

// lock decision integrator
static Word16 pll_cnt=128;

// flag indicating mains ZX event to background task
static char mains_zx=0;

// Current output voltage
static SWord16 OutputVoltage=0;

// Current output voltage scaled to raw units
static SWord16 OutputVoltageRaw=0;

// Incoming ADC sample buffer and then some
static unsigned long ulADC[16];

// sum of absolute value ADC accumulators(approx rms)
static Word32 sum_abs[4];
			
// number of ADC samples taken
static Word16 sum_cnt;

// latched average absolute ADC values
static Word16 sum_abs_latched[4];
	   
// 512-entry sine wave lookup normalised to 15 bits
extern const SWord16 sinlut[];

//*****************************************************************************
// The error routine that is called if the driver library encounters an error.
//*****************************************************************************
#ifdef DEBUG
void
__error__(char *pcFilename, unsigned long ulLine)
{
}
#endif
	  
// Control the AC relay open (0) or closed (1)
static void SetRelay(BYTE level)
{ 
	GPIODirModeSet(GPIO_PORTD_BASE, RELAY, GPIO_DIR_MODE_OUT);

	HWREGBITW(&g_ulFlags, FLAG_RELAY)=level;
	
 	if(level)
		GPIOPinWrite(GPIO_PORTD_BASE, RELAY, RELAY);
	else
		GPIOPinWrite(GPIO_PORTD_BASE, RELAY, 0);
}

// Stop switching
static void StopSwitching(void)
{
	HWREGBITW(&g_ulFlags, FLAG_SWITCHING)=0;
}

// Start switching
static void StartSwitching(void)
{
	vac_gain = 0;
	HWREGBITW(&g_ulFlags, FLAG_SWITCHING)=1;
}

					  
// Set the output voltage of the inverter stage (Volts RMS)
static void SetOutputVoltage(SWord16 voltage)
{	 
	SWord32 t;
					
	OutputVoltage = voltage;

	// compute raw level for direct comparison to vac

	t = voltage;

	t <<= 17;

	t = t / (SWord32)(ABS2RMS * 256.0 * VAC_FULLSCALE);

	OutputVoltageRaw = (SWord16) t;
}

// Main UPS control algorithm .. runs every zero crossing
static void ControlLoop(void)
{
   	SWord16 t;

	// is the relay closed (PV supplying load?)
	if(HWREGBITW(&g_ulFlags, FLAG_RELAY))
	{
		// Below minimum voltage?
		if(ulADC[CHAN_VDC] < (Word16)(VDC_MIN * 1024.0 / VDC_FULLSCALE))
		{
			// Yes, connect back to mains
			SetRelay(0);
			// Set output to zero immediately to prevent reset due to supply under voltage
			SetOutputVoltage(0);

			vac_gain=0;
		}		
	}
	else
	{
		HWREGBITW(&g_ulFlags, FLAG_RATED)=0;

		// try to reach request voltage without lowering Vdc below minimum
		if(ulADC[CHAN_VDC] > (Word16)(VDC_MIN * 1024.0 / VDC_FULLSCALE))
		{
			// DC is ok, try increasing AC
			if(OutputVoltage < OUTPUT_VOLTAGE)
				++OutputVoltage;
			else
			{
				// Set flag indicating we at rated voltage
				HWREGBITW(&g_ulFlags, FLAG_RATED)=1;
			}		
			
		}
		else
		{
			// DC is in trouble, lower output voltage
			if(OutputVoltage > 0)
				--OutputVoltage;

		}
		
		// Load new operating point	  
		SetOutputVoltage(OutputVoltage);

		// is dump load current > output load current transformed to primary side
		if(sum_abs_latched[CHAN_INV_AMPS]/(TXSEC_VOLTAGE/TXPRI_VOLTAGE) >= sum_abs_latched[CHAN_LOAD_AMPS])
			HWREGBITW(&g_ulFlags, FLAG_LOAD_HIGH)=0;
		else
  			HWREGBITW(&g_ulFlags, FLAG_LOAD_HIGH)=1;

		// locked to grid?
		if(HWREGBITW(&g_ulFlags, FLAG_LOCK))
		{
			// yes, is voltage at rated?
			if(HWREGBITW(&g_ulFlags, FLAG_RATED))
			{
			 	// yes, is dummy current > load current
				if(HWREGBITW(&g_ulFlags, FLAG_LOAD_HIGH)==0)
				{
					// yes, close relay and start supply load
					SetRelay(1);
			
				}
			}		
		}			 	
	}

   	// closed loop output voltage regulator

	// control error
	t=OutputVoltageRaw - (SWord16)sum_abs_latched[CHAN_VAC];

	// control output
	vac_gain += t;

	// clip gain to allowable limits
	if(vac_gain	< 0)
		vac_gain=0;
	
	if(vac_gain > MAXIMUM_DUTY-20)
		vac_gain=MAXIMUM_DUTY-20; 
}

// Long counter for ZX timer 
static volatile Word16 timer16=0;

// Overflow interrupt for measuring periods exceeding 65535 timer ticks
void Timer1AIntHandler(void) __irq
{
    // Clear the timer interrupt.
    TimerIntClear(TIMER1_BASE, TIMER_TIMA_TIMEOUT);
 
	// bump zx timer most significant word
   	timer16--;
}

// Interrupt for intercepting grid zero crossing captures
void Timer1BIntHandler(void) __irq
{
 	static char toggle=0;
 	Word32 temp;

    // Clear the timer interrupt.
    TimerIntClear(TIMER1_BASE, TIMER_CAPB_EVENT);

	// Compute time point from overflow counter and capture time
	temp = timer16;
	temp <<=16;
	temp |=TimerValueGet(TIMER1_BASE, TIMER_B) & 0xFFFFu;

	// Compute period since last capture expressed in 50ns ticks
    zx_period = zx_mark - temp;

	// Update capture point
	zx_mark = temp;

	// Indicate that a ZX event has occurred
	mains_zx = 1;

	// only allow acceptable frequency range
	if(zx_period < MAX_PERIOD && zx_period > MIN_PERIOD)
	{
		// Toggle the user LED as a diagnostic
		toggle ^= 1;
	
		if(toggle) 	  
			GPIOPinWrite(GPIO_PORTC_BASE, USER_LED, USER_LED);
		else
			GPIOPinWrite(GPIO_PORTC_BASE, USER_LED, 0);

			 // work out ideal NCO velocity based on line period
			 temp =  0xFA000000Lu / (zx_period >> 3);

			 // check for lock condition					  
			 if(indexb > 512-PHASE_LOCK_RANGE || indexb < PHASE_LOCK_RANGE)
			 {
			 	if(pll_cnt < 255)
					pll_cnt++;

				if(pll_cnt > 192)
					HWREGBITW(&g_ulFlags, FLAG_LOCK)=1;
			 }		
			 else
			 {
			 	if(pll_cnt > 0)
					pll_cnt--;

				if(pll_cnt < 64)
				{
					if(HWREGBITW(&g_ulFlags, FLAG_LOCK))
					{
					 // Force frequency back to nominal if coming out of lock
			 		 HWREGBITW(&g_ulFlags, FLAG_LOCK)=0;		 			
					 index_step=NOM_STEP;
					}
				}	
			 }

			 // lock NCO to line period (1st order control)
			 index_step = (index_step + temp)>>1;

			 // lock NCO phase (zero order control)
			 index=0;

	}
			
}

// The interrupt handler for the ADC interrupt.	This runs at 20kHz
void ADCIntHandler(void)  __irq
{
 	SWord16 duty;
	SWord32 temp;
  	char zx_flag;

    // Clear the ADC interrupt.
    ADCIntClear(ADC_BASE, 0);

    // Read the data from the ADC FIFO
    ADCSequenceDataGet(ADC_BASE, 0, ulADC);
   
	// Integrate the AC channels into the respective accumulators 
	temp = ulADC[CHAN_LOAD_AMPS] - dc_offsets[CHAN_LOAD_AMPS];
	if(temp < 0) temp=-temp;
	sum_abs[CHAN_LOAD_AMPS] += temp;
 	temp = ulADC[CHAN_INV_AMPS] - dc_offsets[CHAN_INV_AMPS];
	if(temp < 0) temp=-temp;
	sum_abs[CHAN_INV_AMPS] += temp;
 	temp = ulADC[CHAN_VAC] - dc_offsets[CHAN_VAC];
    if(temp < 0) temp=-temp;
	sum_abs[CHAN_VAC] += temp;
	sum_cnt++;

	// If we are switching
	if(HWREGBITW(&g_ulFlags, FLAG_SWITCHING))
	{
	
	// advance NCO phase
	index += index_step;
	
	// extract sample index
	indexb = (index >> 16) & 511;

	// determine output duty cycle
	temp = ((SWord32)sinlut[indexb] * vac_gain) >> 15;
	duty = (SWord16)temp;

	// Determine standing phase
	if(indexb & 256)
	{
	  	// clip to minimum duty	to stop PWM hardware glitch	from deadtime generator
	  	if(duty > -MINIMUM_DUTY)
			duty=-MINIMUM_DUTY;

		// Standing phase transition at 180 degrees?
		if(HWREGBITW(&g_ulFlags, FLAG_NCOPHASE))
		{
			HWREGBITW(&g_ulFlags, FLAG_NCOPHASE)=0;

			// Force bottom switch on on inactive bridge leg
			HWREG(PWM_BASE + PWM_GEN_1_OFFSET + PWM_O_X_GENA ) = 
			  ((PWM_GEN_ACT_ONE << PWM_GEN_ACT_A_UP_SHIFT) |
               (PWM_GEN_ACT_ZERO <<	PWM_GEN_ACT_A_DN_SHIFT)|
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_ZERO_SHIFT) |
			   (PWM_GEN_ACT_ONE << PWM_GEN_ACT_LOAD_SHIFT));

		   	HWREG(PWM_BASE + PWM_GEN_0_OFFSET + PWM_O_X_GENA ) = 
			  ((PWM_GEN_ACT_ZERO << PWM_GEN_ACT_A_UP_SHIFT) |
               (PWM_GEN_ACT_ZERO <<	PWM_GEN_ACT_A_DN_SHIFT)|
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_ZERO_SHIFT) |
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_LOAD_SHIFT));	  			   	  
	
		}

		// Load duty cycle into active leg
		HWREG(PWM_BASE+PWM_GEN_1_OFFSET+PWM_O_X_CMPA ) = (Period + duty ) >> 1;
			  
	 }
	 else
	 {
	 	// clip to minimum duty	to stop PWM hardware glitch from deadtime generator
		if(duty < MINIMUM_DUTY)
			duty=MINIMUM_DUTY;

		// Standing phase transition at zero degrees?
		if(!HWREGBITW(&g_ulFlags, FLAG_NCOPHASE))
		{
			HWREGBITW(&g_ulFlags, FLAG_NCOPHASE)=1;
 			// Inform control that zero crossing has occurred
 			zx_flag=1;

			// Force bottom switch on inactive bridge leg
			HWREG(PWM_BASE + PWM_GEN_0_OFFSET + PWM_O_X_GENA ) = 
			  ((PWM_GEN_ACT_ONE << PWM_GEN_ACT_A_UP_SHIFT) |
               (PWM_GEN_ACT_ZERO <<	PWM_GEN_ACT_A_DN_SHIFT) |
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_ZERO_SHIFT) |
			   (PWM_GEN_ACT_ONE << PWM_GEN_ACT_LOAD_SHIFT));

		   	HWREG(PWM_BASE + PWM_GEN_1_OFFSET + PWM_O_X_GENA ) = 
			  ((PWM_GEN_ACT_ZERO << PWM_GEN_ACT_A_UP_SHIFT) |
               (PWM_GEN_ACT_ZERO <<	PWM_GEN_ACT_A_DN_SHIFT)|
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_ZERO_SHIFT) |
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_LOAD_SHIFT));
	
		}
		else 
			zx_flag=0;

		// Load duty cycle into active bridge leg
		HWREG(PWM_BASE+PWM_GEN_0_OFFSET+PWM_O_X_CMPA ) = (Period - duty ) >> 1;	

		// Zero crossing event?
		if(zx_flag)
		{
		 // Yes, average sample measurements over the last line cycle, and reset accumulators
		 if(sum_cnt)
		 {
			temp = sum_abs[CHAN_LOAD_AMPS] / sum_cnt;
			if(temp >= 4) temp-=4;
			sum_abs_latched[CHAN_LOAD_AMPS] = (Word16)temp;
			temp = sum_abs[CHAN_INV_AMPS] / sum_cnt;
			if(temp >= 4 ) temp-=4;
			sum_abs_latched[CHAN_INV_AMPS] = (Word16)temp;
			temp = sum_abs[CHAN_VAC]  / sum_cnt;
			sum_abs_latched[CHAN_VAC] = (Word16)temp;
			sum_cnt=0;
			sum_abs[CHAN_LOAD_AMPS]=sum_abs[CHAN_INV_AMPS]=sum_abs[CHAN_VAC]=0;
		 }

		 // run the outer control
		 ControlLoop();
		}
			     
	  }
	 }
	 else
	 {
	 
			// Drive both bottom switches ON if not switching

		   	HWREG(PWM_BASE + PWM_GEN_1_OFFSET + PWM_O_X_GENA ) = 
			  ((PWM_GEN_ACT_ZERO << PWM_GEN_ACT_A_UP_SHIFT) |
               (PWM_GEN_ACT_ZERO <<	PWM_GEN_ACT_A_DN_SHIFT)|
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_ZERO_SHIFT) |
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_LOAD_SHIFT));

		   	HWREG(PWM_BASE + PWM_GEN_0_OFFSET + PWM_O_X_GENA ) = 
			  ((PWM_GEN_ACT_ZERO << PWM_GEN_ACT_A_UP_SHIFT) |
               (PWM_GEN_ACT_ZERO <<	PWM_GEN_ACT_A_DN_SHIFT)|
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_ZERO_SHIFT) |
			   (PWM_GEN_ACT_ZERO << PWM_GEN_ACT_LOAD_SHIFT));
	}

    //
    // Increment the clock count.
    //
	ticker++;
}


// Measure the DC offsets of the relevant AC input channels
static void MeasureOffsets(void)
{
	Word32 sums[4],mark;
	Word16 count,index;

	// reset integrators
	for(index=0;index<4;index++)
		sums[index]=0;

	// wait 2 seconds for supplies to come up
	mark=ticker;
	while((ticker - mark) < (TIMER_FREQ*2)) 	   	
		WatchdogIntClear(WATCHDOG_BASE);

	// Integrate measurements to determine DC offset
	for(count=0;count<INTEGRATIONS;count++)
	{
	   	WatchdogIntClear(WATCHDOG_BASE);
 
		while(ticker == mark)  ;
		
		mark=ticker;
		
		for(index=0;index<4;index++)
			sums[index] += ulADC[index];	
			
	}

	// take averages and load offsets
 	for(index=0;index<4;index++)
	{
		dc_offsets[index] = (Word16)(sums[index] / INTEGRATIONS);
	}
}


//*****************************************************************************
//
// Design Stellaris Contest Entry LM1633. Main line
//
//*****************************************************************************
int
main(void)
{

 	static char str[64];
	char chan ;
    Word32 ulData,mark;
	
     //
    // Set the clocking to run at 24MHz from the PLL.
    //
    SysCtlClockSet(SYSCTL_SYSDIV_10  | SYSCTL_USE_PLL | SYSCTL_OSC_MAIN |
                   SYSCTL_XTAL_6MHZ);

    SysCtlPWMClockSet(SYSCTL_PWMDIV_1);

    //
    // Initialize the OLED display.
    //
    OSRAMInit(false);

    //
    // Bail out if there is not a PWM peripheral on this part.
    //
    if(!SysCtlPeripheralPresent(SYSCTL_PERIPH_PWM))
    {
        OSRAMStringDraw("This part has no", 0, 0);
        OSRAMStringDraw("PWM", 36, 1);
        DiagExit(0);
    }

    //
    // Clear the screen and tell the user what is happening.
    //
    OSRAMStringDraw("Entry LM1633", 6, 0);
  
    //
    // Enable the peripherals used by this project
    //
    SysCtlPeripheralEnable(SYSCTL_PERIPH_ADC);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_PWM);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOA);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOB);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOD);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_WDOG);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOC);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_TIMER1);

    //
    // Set GPIO as PWM pins.  They are used to output the PWM0, PWM1, PWM2 and PWM3
    // signals.
    //
    GPIOPinTypePWM(GPIO_PORTD_BASE, GPIO_PIN_0 | GPIO_PIN_1);
    GPIOPinTypePWM(GPIO_PORTB_BASE, GPIO_PIN_0 | GPIO_PIN_1);

    //
    // Compute 20kHz PWM period based on the system clock.
    //
    Period = SysCtlClockGet() / TIMER_FREQ;
    // Set maximum duty cycle
	MAXIMUM_DUTY = Period-1;

	index=0;
	// set PLL to 50Hz nominal
	index_step=NOM_STEP;
	// initialise phase detector 
	HWREGBITW(&g_ulFlags, FLAG_ZXPHASE)=0;
	// not locked
	HWREGBITW(&g_ulFlags, FLAG_LOCK)=0;

	// reset integrators
	sum_abs[CHAN_VAC]=sum_abs[CHAN_LOAD_AMPS]=sum_abs[CHAN_INV_AMPS]=0;
	sum_cnt=0;
	sum_abs_latched[CHAN_VAC]=sum_abs_latched[CHAN_LOAD_AMPS]=sum_abs_latched[CHAN_INV_AMPS]=0;
   	
	// Set output voltage and stop switching
	SetOutputVoltage(0);

	StopSwitching();

    //
    // Set the PWM period
    //
    PWMGenConfigure(PWM_BASE, PWM_GEN_0,
                    PWM_GEN_MODE_UP_DOWN | PWM_GEN_MODE_NO_SYNC);
    PWMGenPeriodSet(PWM_BASE, PWM_GEN_0, Period);

	// Configure half-bridge mode with 1 us deadtime
	PWMDeadBandEnable(PWM_BASE, PWM_GEN_0, 5, 5);

    PWMGenConfigure(PWM_BASE, PWM_GEN_1,
                    PWM_GEN_MODE_UP_DOWN | PWM_GEN_MODE_NO_SYNC);

    PWMGenPeriodSet(PWM_BASE, PWM_GEN_1, Period);
								
	// Set dead time	    
   	PWMDeadBandEnable(PWM_BASE, PWM_GEN_1, 5, 5);

	// Disable fault driven output disables
   	PWMOutputFault(PWM_BASE, PWM_OUT_0_BIT | PWM_OUT_1_BIT | PWM_OUT_2_BIT | PWM_OUT_3_BIT, false);
	
	// Synchronise generator 0 and 1 timebases
	PWMSyncTimeBase(PWM_BASE, PWM_GEN_0_BIT | PWM_GEN_1_BIT);
	
	// Set up ADC triggering at midpoint of centred PWM output
	PWMGenIntTrigEnable(PWM_BASE, PWM_GEN_0, PWM_TR_CNT_LOAD);
		 
    //
    // Set PWM to a duty cycle of 0% 
    //
    PWMPulseWidthSet(PWM_BASE, PWM_OUT_0, 20);
    PWMPulseWidthSet(PWM_BASE, PWM_OUT_2, 20);


    //
    // Enable the PWM output signals.
    //
    PWMOutputState(PWM_BASE, PWM_OUT_0_BIT | PWM_OUT_1_BIT | PWM_OUT_2_BIT | PWM_OUT_3_BIT, true);

    //
    // Enable the PWM generator.
    //
    PWMGenEnable(PWM_BASE, PWM_GEN_0);
    PWMGenEnable(PWM_BASE, PWM_GEN_1);
	
    //
    // Set the period of the watchdog timer.
    //
    WatchdogReloadSet(WATCHDOG_BASE, SysCtlClockGet());
    //
    // Enable reset generation from the watchdog timer.
    //
    WatchdogResetEnable(WATCHDOG_BASE);
    //
    // Enable the watchdog timer.
    //
    WatchdogEnable(WATCHDOG_BASE);
   
    //
    // Configure the ADC to sample the input channels when the PWM period expires.
    // After sampling, the ADC will interrupt the processor
    //
    ADCSequenceConfigure(ADC_BASE, 0, ADC_TRIGGER_PWM0, 0);
    ADCSequenceStepConfigure(ADC_BASE, 0, 0,
                             ADC_CTL_CH0 );
    ADCSequenceStepConfigure(ADC_BASE, 0, 1,
                             ADC_CTL_CH1 );
    ADCSequenceStepConfigure(ADC_BASE, 0, 2,
                             ADC_CTL_CH2 );
    ADCSequenceStepConfigure(ADC_BASE, 0, 3,
                             ADC_CTL_CH3 | ADC_CTL_IE | ADC_CTL_END);
    ADCSequenceEnable(ADC_BASE, 0);
    ADCIntEnable(ADC_BASE, 0);
    IntEnable(INT_ADC0);


    //
    // Configure the timer1B to capture the mains line period and handle overflows
	// with timer1A
    //
	TimerDisable(TIMER1_BASE, TIMER_B);
    TimerConfigure(TIMER1_BASE, TIMER_CFG_16_BIT_PAIR | TIMER_CFG_B_CAP_TIME | TIMER_CFG_A_PERIODIC);
    TimerControlEvent(TIMER1_BASE, TIMER_B, TIMER_EVENT_POS_EDGE );
	TimerLoadSet(TIMER1_BASE, TIMER_A, 0xFFFF);
 	IntEnable(INT_TIMER1B);
	IntEnable(INT_TIMER1A);
	TimerIntEnable(TIMER1_BASE, TIMER_CAPB_EVENT | TIMER_TIMA_TIMEOUT );
    TimerEnable(TIMER1_BASE, TIMER_BOTH);

	// Set I/O pin states
    GPIODirModeSet(GPIO_PORTC_BASE, MAINS_ZX, GPIO_DIR_MODE_HW);
    GPIODirModeSet(GPIO_PORTC_BASE, PUSH_BUTTON, GPIO_DIR_MODE_IN);
    GPIOPinWrite(GPIO_PORTC_BASE, USER_LED, 0);
    GPIODirModeSet(GPIO_PORTC_BASE, USER_LED, GPIO_DIR_MODE_OUT);

	// Open relay
	SetRelay(0);

	// Measure DC offsets
	MeasureOffsets();

	// Start the inverter controller
	StartSwitching();

    //
    // Throw away any button presses that may have occurred 
    //
    HWREGBITW(&g_ulFlags, FLAG_BUTTON_PRESS) = 0;

	// Reset channel display number
	chan=0;

	// Reset timer
	mark=ticker;

    //
    // Loop forever while the inverter operates
    //
    while(1)
    {

    	// Clear the watchdog 
    	WatchdogIntClear(WATCHDOG_BASE);
     
	 	//
    	// Read the push button.
    	//
    	ulData = GPIOPinRead(GPIO_PORTC_BASE, PUSH_BUTTON) ? 1 : 0;

    	//
    	// See if the push button state doesn't match the debounced push button
    	// state.
    	//
    	if(ulData != HWREGBITW(&g_ulFlags, FLAG_BUTTON))
    	{
        //
        // Increment the debounce counter.
        //
        HWREGBITW(&g_ulFlags, FLAG_DEBOUNCE_LOW) ^= 1;
        if(!HWREGBITW(&g_ulFlags, FLAG_DEBOUNCE_LOW))
        {
            HWREGBITW(&g_ulFlags, FLAG_DEBOUNCE_HIGH) = 1;
        }

        //
        // See if the debounce counter has reached three.
        //
        	if(HWREGBITW(&g_ulFlags, FLAG_DEBOUNCE_LOW) &&
           		HWREGBITW(&g_ulFlags, FLAG_DEBOUNCE_HIGH))
        	{
            //
            // The button has been in the new state for three consecutive
            // samples, so it has been debounced.  Toggle the debounced state
            // of the button.
            //
            HWREGBITW(&g_ulFlags, FLAG_BUTTON) ^= 1;

            	//
            	// If the button was just pressed, set the flag to indicate that
            	// fact.
            	//
            	if(HWREGBITW(&g_ulFlags, FLAG_BUTTON) == 0)
            	{
                HWREGBITW(&g_ulFlags, FLAG_BUTTON_PRESS) = 1;
            	}
        	}
    	}
    	else
    	{
        	//
        	// Since the button state matches the debounced state, reset the
        	// debounce counter.
        	//
        	HWREGBITW(&g_ulFlags, FLAG_DEBOUNCE_LOW) = 0;
        	HWREGBITW(&g_ulFlags, FLAG_DEBOUNCE_HIGH) = 0;
    	}

		if(HWREGBITW(&g_ulFlags, FLAG_BUTTON) != 0)
       	{
			// process button press here

		}

		// See if its time to update the LCD (twice per second) 
		if((ticker - mark) > TIMER_FREQ/2)
		{
		   	mark=ticker;
		   
		    // Generate the top status line
		    str[0]=0;
			 
		    if(HWREGBITW(&g_ulFlags, FLAG_RELAY))
				// source if pv
	        	strcat(str,"Sola ");
			else
				// source is grid
				strcat(str,"Grid ");

		    if(HWREGBITW(&g_ulFlags, FLAG_LOCK))
				// locked to grid
	        	strcat(str,"Lck ");
		    else
				// syncing up to grid
				strcat(str,"Syn ");
 
 		    if(HWREGBITW(&g_ulFlags, FLAG_RATED))
				// running at rated voltage
	        	strcat(str,"Vo ");
			else
				// running at reduced voltage
				strcat(str,"Vr ");

		    if(HWREGBITW(&g_ulFlags, FLAG_LOAD_HIGH))
	        	strcat(str,"OL");
			else
				// pv output is ok
				strcat(str,"OK");

			OSRAMStringDraw(str,6,0);

			// Display a channel on the bottom line of the display
		    switch(chan) 
			{
			
				case CHAN_VDC:
					ulData = (Word32)(ulADC[CHAN_VDC] * VDC_FULLSCALE * 10) >> 10;

					sprintf(str,"Vpv %lu.%lu V", ulData/10, ulData%10);
					break;

			   case CHAN_VAC:
 
					ulData =(Word32)(sum_abs_latched[CHAN_VAC] * (Word32)(ABS2RMS * 2560.0 * VAC_FULLSCALE)) >> 17;

					sprintf(str,"Vo  %lu.%lu V", ulData/10, ulData%10);
			   		break;
 
 			   case CHAN_LOAD_AMPS:

					ulData = (Word32)(sum_abs_latched[CHAN_LOAD_AMPS] * (Word16)(ABS2RMS * 2560.0 * IDC_FULLSCALE)) >> 17;

					sprintf(str,"Iac %lu.%lu A", ulData/10, ulData%10);
			   		break;
 
			   case CHAN_INV_AMPS:

 					ulData = (Word32)(sum_abs_latched[CHAN_INV_AMPS] * (Word16)(ABS2RMS * 2560.0 * IDC_FULLSCALE)) >> 17;

					sprintf(str,"Io  %lu.%lu A", ulData/10, ulData%10);
			   		break;

				case CHAN_FREQ:

					ulData = (index_step * ((TIMER_FREQ * 10)>>4)) >> (25-4);

					sprintf(str,"Fo  %lu.%lu Hz", ulData/10, ulData%10);
					break;

				case CHAN_MAINS:
					 
					if(mains_zx)
					{
						mains_zx=0;

						ulData = (Word32)(200000000Lu / zx_period);

					   	if(ulData > 450 && ulData < 650)
							sprintf(str,"Fac %lu.%lu Hz", ulData/10, ulData%10);
						else
						{

			 				HWREGBITW(&g_ulFlags, FLAG_LOCK)=0;	
							pll_cnt=128;
							index_step=NOM_STEP;
					

							sprintf(str,"Fac ?     ");
						}
					}
					else
					{

		 				HWREGBITW(&g_ulFlags, FLAG_LOCK)=0;	
						pll_cnt=128;
						index_step=NOM_STEP;


						sprintf(str,"Fac ?     ");
					}

					break;
					
			}

			if(++chan >= 6)
				chan=0;


			OSRAMStringDraw("            ",6,1);

	 		OSRAMStringDraw(str, 6, 1);
			
		}


    }
}
