Module ok_1 {
    ResetPort RST;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL0;
    SelectPort SEL1;
	TCKPort TCK;

    ScanInPort  SI[1:0];
    ScanOutPort SO[1:0] {
        Source ScanReg1[0], ScanReg0[0];
    }

    ScanInterface s_0 {
        Port RST;
        Port SE;
        Port SEL0;
        Chain c0 {
            Port SI[0];
            Port SO[0];
        }
        Chain c1 {
            Port SI[1];
            Port SO[1];
        }        
    }
  
    ScanRegister ScanReg0[7:0] {
        ScanInSource SI[0];
    }

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI[1];
    }
}

Module ok_2 {
    ResetPort RST;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	TCKPort TCK;

    ScanInPort  SI;

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI;
    }
    ScanRegister ScanReg0[7:0] {
        ScanInSource ScanReg1;
    }
    ScanOutPort SO {
        Source ScanReg0;
    }
}

Module ok_3 {
    ResetPort RST;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	TCKPort TCK;

    ScanInPort  SI;

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI;
    }
    ScanRegister ScanReg0[7:0] {
        ScanInSource ScanReg1[0];
    }
    ScanOutPort SO {
        Source ScanReg0[0];
    }
}

Module ok_4 {
    ResetPort RST;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	TCKPort TCK;

    ScanInPort  SI;

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI;
    }
    ScanRegister ScanReg0[0:7] {
        ScanInSource ScanReg1[0];
    }
    ScanOutPort SO {
        Source ScanReg0[7];
    }
}

Module ok_5 {
    ResetPort RST;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	TCKPort TCK;

    ScanInPort  SI;

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI;
    }
    ScanRegister ScanReg0[0:7] {
        ScanInSource ScanReg1[0];
    }
    ScanOutPort SO {
        Source ScanReg0;
    }
}

Module not_ok_1 {
    ResetPort RST;    
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL0;
    SelectPort SEL1;
	TCKPort TCK;

    ScanInPort  SI[1:0];
    ScanOutPort SO[1:0] {
        Source ScanReg1[0], ScanReg0[0];
    }

    ScanInterface s_0 {
        Port RST;
        Port SE;
        Port SEL0;
        Chain c0 {
            Port SI[0];
            Port SO[0];
        }
        Chain c1 {
            Port SI[1];
            Port SO[1];
        }        
    }
  
    ScanRegister ScanReg0[7:0] {
        ScanInSource SI[0];
    }

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI;
    }
}

Module not_ok_2 {
    ResetPort RST;    
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL0;
    SelectPort SEL1;
	TCKPort TCK;

   ScanInPort  SI[1:0];
    ScanOutPort SO[1:0] {
        Source ScanReg1[0], ScanReg0[0];
    }
 
    ScanInterface s_0 {
        Port RST;
        Port SE;
        Port SEL0;
        Chain c0 {
            Port SI[0];
            Port SO[0];
        }
        Chain c1 {
            Port SI[1];
            Port SO[1];
        }        
    }
  
    ScanRegister ScanReg1[1:0] {
        ScanInSource SI[1:0];
    }
}

Module not_ok_3 {
    ResetPort RST;    
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL0;
    SelectPort SEL1;
	TCKPort TCK;

    ScanInPort  SI[1:0];
    ScanOutPort SO[1:0] {
        Source ScanReg1[0], ScanReg0[0];
    }

    ScanInterface s_0 {
        Port RST;
        Port SE;
        Port SEL0;
        Chain c0 {
            Port SI[0];
            Port SO[0];
        }
        Chain c1 {
            Port SI[1];
            Port SO[1];
        }        
    }
  
    ScanRegister ScanReg0[7:0] {
        ScanInSource SI[0];
    }

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI[3];
    }
}

Module not_ok_4 {
    ResetPort RST;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	TCKPort TCK;

    ScanInPort  SI;

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI;
    }
    ScanRegister ScanReg0[7:0] {
        ScanInSource ScanReg1[0];
    }
    ScanOutPort SO {
        Source ScanReg0[1];
    }
}

Module not_ok_5 {
    ResetPort RST;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL0;
    SelectPort SEL1;
	TCKPort TCK;

    ScanInPort  SI[1:0];
    ScanOutPort SO[1:0] {
        Source ScanReg1[1:0];
    }

    ScanInterface s_0 {
        Port RST;
        Port SE;
        Port SEL0;
        Chain c0 {
            Port SI[0];
            Port SO[0];
        }
        Chain c1 {
            Port SI[1];
            Port SO[1];
        }        
    }
  
    ScanRegister ScanReg0[7:0] {
        ScanInSource SI[0];
    }

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI[1];
    }
}

Module not_ok_6 {
    ResetPort RST;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	TCKPort TCK;

    ScanInPort  SI;

    ScanRegister ScanReg1[7:0] {
        ScanInSource SI;
    }
    ScanRegister ScanReg0[0:7] {
        ScanInSource ScanReg1[0];
    }
    ScanOutPort SO {
        Source ScanReg0[0];
    }
}