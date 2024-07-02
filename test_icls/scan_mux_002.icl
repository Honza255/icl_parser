
Module scan_mux_002 {

    ScanInPort TDI[0];


	ScanRegister A[1:0] { 
		ScanInSource TDI[0];
		ResetValue 2'b10; 
	}
	
    ScanRegister B[1:0] { 
		ScanInSource A[0];
		ResetValue 'b1; 
		RefEnum result;
	}
	
    ScanRegister C[1:0] { 
		ScanInSource B[0];
		ResetValue 'b0; 
	}

    ScanMux mux_1 SelectedBy A[1:0] {
        1'b0,1'b1 | 1'b1,1'b0 : B[0];
        1'b1,1'b1 | 1'b0,1'b0 : C[0];
    }
    
    ScanRegister D[3:0] { 
		ScanInSource mux_1[0];
		ResetValue 'b0; 
	}

    ScanMux mux_2 SelectedBy B[1:0] {
        1'b0,1'b1 | 1'b1,1'b0 : mux_1[0];
        1'b1,1'b1 | 1'b0,1'b0 : D[0];
    }  

	Instance reg8 Of SReg {
		InputPort SI = mux_3[0]; 
		Parameter Size = 5;
	}


	Enum result {
		good = 2'b00;
		bad = 2'b01;
		ugly = 1'b1,1'b0;
		unk = 2'b11;
	}


	LogicSignal logic_0  { reg8.SR[1:0] == 2'b10 || C == 2'b11; }
	LogicSignal logic_1  { |(~(reg8.SR[0]), reg8.SR[1]); }
	LogicSignal logic_2  { reg8.SR[0], reg8.SR[1] == 2;}
	LogicSignal logic_3  { reg8.SR[1] & ~reg8.SR[0] | reg8.SR[1] & reg8.SR[0];}
	LogicSignal logic_4  { ~reg8.SR[1:0] == 3;}	
	LogicSignal logic_5  { (reg8.SR[1:0] & ~reg8.SR[1:0]) == 3;}	
	LogicSignal logic_6  { (reg8.SR[1:0] & ~reg8.SR[1:0]) == 3  | reg8.SR[1] & reg8.SR[0];}	
	LogicSignal logic_7  { C[0] ^ reg8.SR[0];}	
	LogicSignal logic_8  { C[0] ^ reg8.SR[0] ^ reg8.SR[1] ;}	
	LogicSignal logic_9  { (2 ^ (reg8.SR[0], reg8.SR[1])) == 1;}	
	LogicSignal logic_10 { (|reg8.SR[1:0]) ^ (^reg8.SR[1:0]) ^ (&reg8.SR[1:0]) ;}	
	LogicSignal logic_11 { (|3) ^ (^2) ^ (&0) ;}	
	LogicSignal logic_12 { C[0] ;}
	LogicSignal logic_13 { 1 ;}
	LogicSignal logic_14 { |(( C[0] ^ reg8.SR[0]),1, C[0]) ;}
	LogicSignal logic_15 { B[1:0] == ugly; }

	Enum enumn_three {
		lol  = 3'b110;
		olol = 3'b101;
	}

	Enum PassFail {
		Pass = 1'b1;
		Fail = 1'b0;
	}

	Enum YesNo { 
		Yes = 1'b1;
		No	= 1'b0; 
	}

	Enum Modes { 
		red = 4'b0011;
		blue = 4'b1000;
		green = 4'b0100;
	}

	Alias MyName1[2:0] = reg8.SR[1], D[1:0];
	Alias MyName2[1:0] = A[1], C[0] { RefEnum result;}
	Alias RE = A[0] { iApplyEndState 1'b0;}
	// Alias MyName3[2:0] = RE, MyName2[0], MyName1[0]

	Alias CNTL[2:0] = reg8.SR[1], A[1], C[0] { AccessTogether; Attribute kol = 'h 10; Attribute lic = 'h 5; RefEnum enumn_three; iApplyEndState 1'b0;}
	
	// Unsized tests
	ScanRegister UnSized_0[4:0] { 
		ScanInSource TDI[0];
		CaptureSource reg8.SR[1], D[1:0], 0;
	}
	ScanRegister UnSized_1[4:0] { 
		ScanInSource TDI[0];
		CaptureSource reg8.SR[1], 0, D[1:0];
	}
	ScanRegister UnSized_2[4:0] { 
		ScanInSource TDI[0];
		CaptureSource 0, reg8.SR[1], D[1:0];
	}
	ScanRegister UnSized_3[4:0] { 
		ScanInSource TDI[0];
		CaptureSource reg8.SR[1], D[1:0], 3;
	}
	ScanRegister UnSized_4[4:0] { 
		ScanInSource TDI[0];
		CaptureSource reg8.SR[1], 3, D[1:0];
	}
	ScanRegister UnSized_5[4:0] { 
		ScanInSource TDI[0];
		CaptureSource 3, reg8.SR[1], D[1:0];	
	}
	ScanRegister UnSized_6[4:0] { 
		ScanInSource TDI[0];
		CaptureSource reg8.SR[1], 2, D[1:0];
	}

	// Sized tests
	ScanRegister Sized_0[4:0] { 
		ScanInSource TDI[0];
		CaptureSource reg8.SR[1], 2'b10, D[1:0];
	}
	ScanRegister Sized_1[4:0] { 
		ScanInSource TDI[0];
		CaptureSource reg8.SR[1], 3'b100, D[0];
	}

	ScanRegister Sized_2[4:0] { 
		ScanInSource TDI[0];
		CaptureSource C, 4;
		ResetValue 'b0; 
	}

    ScanMux mux_3 SelectedBy  reg8.SR[3:0] {
        4'b0000 | 4'b1011 | 4'b1100 | 4'b1101 | 4'b1110 | 4'b1111 : mux_2[0];
        4'b0001 :UnSized_0[0];
        4'b0010 :UnSized_1[0];
        4'b0011 :UnSized_2[0];
        4'b0100 :UnSized_3[0];
        4'b0101 :UnSized_4[0];
        4'b0110 :UnSized_5[0];
        4'b0111 :UnSized_6[0];
        4'b1000 :Sized_0[0];
        4'b1001 :Sized_1[0];
        4'b1010 :Sized_2[0];
    }  

	ScanOutPort TDO[0] { 
		Source reg8.SO;
	}


}