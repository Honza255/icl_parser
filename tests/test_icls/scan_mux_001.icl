Module scan_mux_001 {

    ScanInPort SI[1:0];
    DataInPort lol[1:0];

	ScanOutPort A { 
		Source compare_out_2[0];
	}

	ScanOutPort B[1:0] { 
		Source compare_out_1[1:0];
	}

    ScanMux compare_out_0 SelectedBy lol[1:0] {
        1'b0,1'b1 | 1'b1,1'b0 : SI[0];
        1'b1,1'b1 | 1'b0,1'b0 : SI[1];
    }
    
    ScanMux compare_out_1[1:0] SelectedBy lol[1],lol[0] {
        1'b0,1'b1 | 1'b1,1'b0 |  1'b1,1'b1 | 1'b0,1'b0 : SI[1:0];
    }

    ScanMux compare_out_2[1:0] SelectedBy lol {
        1'b0,1'b1 | 1'b1,1'b0 |  1'b1,1'b1 | 1'b0,1'b0 : SI;
    }

}