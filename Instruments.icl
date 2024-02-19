/*
* This file contains code snippets from IEEE Standard 1687-2014 Appendix E
*
* -------------+------------+-------------------------+------------------------
*   Version    |  Date      | Author                  | Organization
* -------------+------------+-------------------------+------------------------
*          1.0 | 8.03.2016  | Anton Tsertov           | Testonica Lab
*--------------+------------+-------------------------+------------------------
*          2.1 | 2.11.2016  | Dmitri Mihhailov        | Testonica Lab
*--------------+------------+-------------------------+------------------------
* 
*/

Module Instrument {
   Attribute lic = 'h ef931832;
	Parameter size = 8;
	DataInPort DI[$size-1:0];
	DataOutPort DO[$size-1:0] {
		Source dr[$size-1:0];
	}
	
	Alias enable = DI[$size-1] {
		RefEnum YesNo;
	}
	Alias mode[3:0] = DI[6:5],DI[3:2] {
		RefEnum Modes;
	}
	Alias data[2:0] = DI[4],DI[1:0];
	Alias okay = DO[0] {
		RefEnum PassFail;
	}
	Alias done = DO[1] {
		RefEnum YesNo;
	}
	Alias count[5:0] = DO[7:2];
	Enum PassFail {
		Pass = 1'b1;
		Fail = 1'b0;
	}
	Enum YesNo {
		Yes = 1'b1;
		No = 1'b0;
	}
	Enum Modes {
		red = 4'b0011;
		blue = 4'b1000;
		green = 4'b0100;
	}
	
	DataRegister dr[$size-1:0] {
		WriteDataSource DI[$size-1:0];
		WriteEnSource enable;
	}
}


Module LoopDIDO {
	Attribute lic = 'h e281323e;
	Parameter width = 1;
	DataInPort DI[$width-1 : 0];
	DataOutPort DO[$width-1 : 0] {
		Source DI [$width-1 : 0];
	}
}

Module SReg {
	Attribute lic = 'h 748d74c9;
	Parameter Size = 7;
	Parameter MSB = $Size-1;
	ScanInPort SI;
	ScanOutPort SO { 
		Source SR[0];
	}
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	ResetPort RST;
	TCKPort TCK;
	DataInPort DI[$MSB:0];
	DataOutPort DO[$MSB:0] {
		Source SR; 
	}
	ScanInterface scan_client { 
		Port SI; 
		Port SO; 
		Port SEL; 
	}
	ScanRegister SR[$MSB:0] { 
		ScanInSource SI;
		CaptureSource DI;
		ResetValue 'b0; 
	}
}


Module SBit {
	Attribute lic = 'h 18534558;
	Parameter Size = 1;
	Parameter MSB = $Size-1;
	ScanInPort SI;
	ScanOutPort SO { 
		Source SR[0];
	}
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	ResetPort RST;
	TCKPort TCK;
	DataOutPort DO[$MSB:0] {
		Source SR; 
	}
	ScanInterface scan_client { 
		Port SI; 
		Port SO; 
		Port SEL; 
	}
	ScanRegister SR[$MSB:0] { 
		ScanInSource SI;
		ResetValue 'b0; 
	}

}

Module WrappedInstr {
	Attribute lic = 'h 16a33867;
	Parameter Size = 8;
	ScanInPort SI;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	ResetPort RST;
	TCKPort TCK;
	ScanOutPort SO { 
		Source reg8.SO;
	}
	
	ScanInterface scan_client { 
		Port SI; 
		Port SO; 
		Port SEL; 
	}
	Instance I1 Of Instrument { 
		InputPort DI = reg8.DO; 
		Parameter size = $Size;
	}
	Instance reg8 Of SReg {
		InputPort SI = SI; 
		InputPort DI = I1.DO; 
		Parameter Size = $Size;
	}
}

Module SRegToDReg {
    Attribute lic = 'h a212eb8a;
    Parameter Size = 8;
    ScanInPort SI;
    ShiftEnPort SE;
    CaptureEnPort CE;
    UpdateEnPort UE;
    SelectPort SEL;
    ResetPort RST;
    TCKPort TCK;
    ScanOutPort SO { 
        Source reg8.SO;
    }
    Alias enable = reg8.DO[$size-1] {
        RefEnum YesNo;
    }
    Enum YesNo {
        Yes = 1'b1;
        No = 1'b0;
    }
    ScanInterface scan_client { 
        Port SI; 
        Port SO; 
        Port SEL; 
    }
    DataRegister dr[$size-1:0] {
        WriteDataSource reg8.DO;
        WriteEnSource enable;
    }
    Instance reg8 Of SReg {
        InputPort SI = SI; 
        InputPort DI = dr[$size-1:0]; 
        Parameter Size = $Size;
    }
}


Module WrappedScan {
	Attribute lic = 'h e790dea8;
	Parameter dataWidth = 1;
	ScanInPort SI;
	ShiftEnPort SE;
	CaptureEnPort CE;
	UpdateEnPort UE;
	SelectPort SEL;
	ResetPort RST;
	TCKPort TCK;
	ScanOutPort SO { 
		Source reg.SO;
	}
	
	ScanInterface scan_client { 
		Port SI; 
		Port SO; 
		Port SEL; 
	}
	Instance I1 Of LoopDIDO { 
		InputPort DI = reg.DO;
		Parameter width = $dataWidth;
	}
	Instance reg Of SReg {
		InputPort SI = SI; 
		InputPort DI = I1.DO; 
		Parameter Size = $dataWidth;
	}
	
}

UseNameSpace myNameSpace;

Module x {
	Attribute lic = 'h e790dea8;
}

NameSpace X;
Module x {
	Attribute lic = 'h e790dea8;
}

NameSpace;
Module x {
	LocalParameter ABC = 4;	
	LocalParameter XXX = 0;	
	LocalParameter LOC_DEC_0 = 0;	

	Parameter UN_DEC_0 = 051;
	Parameter UN_DEC_1 = 10_51;	
	Parameter UN_DEC_2 = 0_51;	
	Parameter UN_DEC_3 = 'd 0_51;		


	Parameter SIZ_DEC_0 = 5'd 051;
	Parameter SIZ_DEC_1 = 10'd 10_51;	
	Parameter SIZ_DEC_2 = 1'd 0_51;		
	Parameter SIZ_DEC_3 = 3'D3;		
	Parameter SIZ_DEC_4 = 1'd3;	

	Parameter SIZ_BIN_0 = 5'b 000;
	Parameter SIZ_BIN_1 = 10'b 00_01;	
	Parameter SIZ_BIN_2 = 1'b 11_11;		
	Parameter SIZ_BIN_3 = 3'b010;		
	Parameter SIZ_BIN_4 = 1'b1111;
	//Parameter SIZ_BIN_5 = 5'b1xx1;		

	Parameter SIZ_BIN_HEX_1= 4'h7;
	Parameter SIZ_BIN_HEX_2 = 3'h07;
	Parameter SIZ_BIN_HEX_3 = 1'hf7;
	Parameter SIZ_BIN_HEX_4 = 2'hbb;
	//Parameter SIZ_BIN_HEX_5 = 2'hxb;

	Parameter EXPR_0 = 5+5;
	Parameter EXPR_1 = 5*5;
	Parameter EXPR_2 = 5/5;
	Parameter EXPR_3 = 5-5;
	Parameter EXPR_4 = 5%8;
	Parameter EXPR_5 = (((5+5)*2)+2);

	Parameter EXPR_6 = 3'd002 , 3'h0006 , ~3'b011;
	Parameter EXPR_7 = 4'b100 , 6'h0001 , ~12'b111;
	Parameter EXPR_8 = 3'b100 , 6'b100001 , ~2'b01;
	Parameter EXPR_9 =  $EXPR_5*$EXPR_5*$EXPR_2;


	Parameter str_0 = "Hello", $dum;
	Parameter kla = "Hello", $dum, "Ell", $asd,"Sakana";
	Parameter dum = "Good";	
	Parameter asd = "Bye";
	Parameter umpa = "Boom", $kla, $kla;	

	/*	
	*Parameter xorr = "Ouch", $umpa, $kla, $umpa, $kla;	
	*/

	Attribute lic = 'h e790dea8;

		
	ScanInPort SI;
	ScanOutPort SO { 
		Source reg.SO;
	}
	
	 
	Instance reg Of WrappedScan {
		InputPort SI = SI; 
		Parameter dataWidth=10;
	}

	/*
	Instance aa Of X::x {
		InputPort SI = SI; 
		InputPort DI = I1.DO;
		InputPort DI[3:2] = I1.DO[3:2]; 
		InputPort DI[4:15] = I1.DO,I1.DO[2:8],2; 
		InputPort DI[16] = I1.DO;
		InputPort XX[10:0] = 3,I1.DO,I1.DO[2:8]; 
		InputPort XY[10:0] = I1.DO,3,I1.DO[4:8]; 

		Parameter Size = $EXPR_5;
		Parameter A = 0;
		Attribute LOL = "ALA"
	}	
	*/


}