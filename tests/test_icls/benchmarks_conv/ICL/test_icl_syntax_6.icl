Module test_icl_syntax_6_bad {
	Parameter Size = 8;
	Parameter MSB = $Size-1;

	ScanInPort SI;
	ScanOutPort SO { 
		Source SR_1[$MSB];
	}
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	ResetPort RST;
	TCKPort TCK;

	ScanInterface scan_client { 
		Port SI; 
		Port SO; 
		Port SEL; 
	}
	ScanRegister SR_0[$MSB:0] { 
		ScanInSource SI;
		CaptureSource SR_0;
		ResetValue 'b10;
        DefaultLoadValue 'b11;
	}

	ScanRegister SR_1[0:$MSB] { 
		ScanInSource SR_0[0];
		CaptureSource SR_1;
		ResetValue 'b10;
        DefaultLoadValue 'b11;
	}

}

Module test_icl_syntax_6 {
	Parameter Size = 8;
	Parameter MSB = $Size-1;

	ScanInPort SI;
	ScanOutPort SO { 
		Source SR_1[$MSB];
	}
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	ResetPort RST;
	TCKPort TCK;

	ScanInterface scan_client { 
		Port SI; 
		Port SO; 
		Port SEL; 
	}

	ScanRegister SR_0[$MSB:0] { 
		ScanInSource SI;
		CaptureSource SR_0;
		ResetValue       'b1x00x01x;
        DefaultLoadValue 'bxx0x1010;
	}

	ScanRegister SR_1[0:$MSB] { 
		ScanInSource SR_0[0];
		CaptureSource SR_1;
		ResetValue       'bxx10x101;
        DefaultLoadValue 'bxx10010x;
	}

}




