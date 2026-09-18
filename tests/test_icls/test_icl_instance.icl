Module ScanReg {
    ScanInPort SI[1:0];
    ScanOutPort SO[1:0] {
        Source SI[1], SR[0];
    }
    DataInPort DI[7:0];
    ScanRegister SR[7:0] {
        ScanInSource SI[0];
        CaptureSource DI;
        ResetValue 'b0;
    }
}

Module ok_icl_instace_0 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI = 'b0, tdi; // <-Test
        InputPort DI = 0;
    }
}

Module ok_icl_instace_1 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI[1:0] = 'b0, tdi; // <-Test
        InputPort DI = 0;
    }
}

Module ok_icl_instace_2 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI[1] = 'b0; // <-Test
        InputPort SI[0] = tdi; // <-Test
        InputPort DI = 0;
    }
}

Module ok_icl_instace_3 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI[1] = 'b0; // <-Test
        InputPort SI[0] = tdi[0]; // <-Test
        InputPort DI = 0;
    }
}



Module not_ok_icl_instace_0 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI = 'b0, tdi;
        InputPort DI = 0;
        InputPort SI[1] = 'b0, tdi; // <-Test
    }
}

Module not_ok_icl_instace_1 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI = 'b0, tdi;
        InputPort DI = 0;
        InputPort SI[2] = 'b0, tdi; // <-Test
    }
}

Module not_ok_icl_instace_2 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI = 'b0, tdi;
        InputPort DI = 0;
        InputPort SI = 'b0, tdi; // <-Test
    }
}

Module not_ok_icl_instace_3 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI = 1'b0, tdi, 1'b0; // <-Test
        InputPort DI = 0;
    }
}

Module not_ok_icl_instace_4 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI[0] = tdi; // <-Test
        InputPort DI = 0;
    }
}

Module not_ok_icl_instace_5 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        InputPort SI = 'b0, tdi; 
        // <-Test
    }
}

Module not_ok_icl_instace_6 {
    ScanInPort tdi;
    ScanOutPort tdo {
        Source A.SO[0];
    }
    TCKPort tck;
    TMSPort tms;
    TRSTPort trst_n;

    Instance A Of ScanReg { 
        // <-Test
        InputPort DI = 0;
    }
}