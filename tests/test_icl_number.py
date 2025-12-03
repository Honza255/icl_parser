import unittest
from src.icl_items import IclNumber

class TestIclNumber(unittest.TestCase):

    def test_all(self):
        x = IclNumber("xx", "bin", -1)
        print(x)
        self.assertEqual("xx", x.get_bin_str())
        x.resize(4)
        print(x)
        self.assertEqual("xxxx", x.get_bin_str())
        try:
            x.resize(3,1)
        except:
            pass
        else:
            raise ValueError("Function did not fail")
        x.resize(3, 0)
        print(x)
        self.assertEqual("xxx", x.get_bin_str())
        
        x = IclNumber("0", "bin", -1)
        print(x)
        self.assertEqual("0", x.get_bin_str())
        x.resize(5)
        print(x)
        self.assertEqual("00000", x.get_bin_str())

        x = IclNumber("'b11_00", "bin", -1)
        print(x)
        self.assertEqual("1100", x.get_bin_str())
        x.resize(6)
        print(x)
        self.assertEqual("001100", x.get_bin_str())
        try:
            x.resize(3,1)
        except:
            pass
        else:
            raise ValueError("Function did not fail")
        x.resize(3,0)
        print(x)
        self.assertEqual("100", x.get_bin_str())

        x = IclNumber("'B11", "bin", 10)
        print(x)
        self.assertEqual("0000000011", x.get_bin_str())

        x = IclNumber("xx01_x11", "bin", 10)
        print(x)
        self.assertEqual("xxxxx01x11", x.get_bin_str())

        x = IclNumber("'d13", "dec", -1)
        print(x)
        self.assertEqual("1101", x.get_bin_str())
        x.resize(6)
        print(x)
        self.assertEqual("001101", x.get_bin_str())

        x = IclNumber("'HE", "hex", -1)
        print(x)
        self.assertEqual("1110", x.get_bin_str())

        x = IclNumber("1_2_3", "dec", -1)
        print(x)
        self.assertEqual("1111011", x.get_bin_str())
                
        x = IclNumber("0235", "dec", -1)
        print(x)
        self.assertEqual("11101011", x.get_bin_str())
                
        x = IclNumber("'d 134", "dec", -1)
        print(x)
        self.assertEqual("10000110", x.get_bin_str())

        x = IclNumber("'h 23ff", "hex", -1)
        print(x)
        self.assertEqual("10001111111111", x.get_bin_str())

        try:
            x = IclNumber("3fa", "dec", -1)
        except:
            pass
        else:
            raise ValueError("Function did not fail")

        try:
            x = IclNumber("0xa", "dec", -1)
        except:
            pass
        else:
            raise ValueError("Function did not fail")
        
        x = IclNumber("'b0101", "bin", 4)
        print(x)
        self.assertEqual("0101", x.get_bin_str())    

        x = IclNumber("'D 3", "dec", 5)
        print(x)
        self.assertEqual("00011", x.get_bin_str())    

        x = IclNumber("'b0_1x", "bin", 3)
        print(x)
        self.assertEqual("01x", x.get_bin_str())

        x = IclNumber("'hx", "hex", 7)
        print(x)
        self.assertEqual("xxxxxxx", x.get_bin_str())
                                    
        x = IclNumber("'h3", "hex", 2)
        print(x)
        self.assertEqual("11", x.get_bin_str())

        try:
            x = IclNumber("'hF", "hex", 2)
        except:
            pass
        else:
            raise ValueError("Function did not fail")

        #try:
        #    x = IclNumber("' hx", "hex", 7)
        #except:
        #    pass
        #else:
        #    raise ValueError("Function did not fail")

        try:
            x = IclNumber("'b", "bin", 0)
        except:
            pass
        else:
            raise ValueError("Function did not fail")

        try:
            x = IclNumber("'30", "hex", 5)
        except:
            pass
        else:
            raise ValueError("Function did not fail")

        x = IclNumber("' x", "hex", -1)
        print(x)
        self.assertEqual("xxxx", x.get_bin_str())
        x.resize(9)
        print(x)
        self.assertEqual("xxxxxxxxx", x.get_bin_str())

        x = IclNumber("' 3x", "hex", -1)
        print(x)
        self.assertEqual("11xxxx", x.get_bin_str())
        x.resize(9)
        print(x)
        self.assertEqual("00011xxxx", x.get_bin_str())

        x = IclNumber("'x3", "hex", -1)
        print(x)
        self.assertEqual("xxxx0011", x.get_bin_str())
        x.resize(9)
        print(x)
        self.assertEqual("xxxxx0011", x.get_bin_str())

        a = IclNumber("'b00101", "bin", 5)
        b = IclNumber("'b1111", "bin", 4)
        print(a, b)
        x = a.concat(b)
        print(x)
        self.assertEqual("001011111", x.get_bin_str())

        a = IclNumber("'b00101", "bin", 5)
        b = IclNumber("'b111x", "bin", 4)
        print(a, b)
        x = a.concat(b)
        print(x)
        self.assertEqual("00101111x", x.get_bin_str())

        x = IclNumber("'b111x", "bin", 4)
        x.resize(1,0)
        x.resize(4,0)
        print(x)                      
        self.assertEqual("xxxx", x.get_bin_str())

        x = IclNumber("'bx100", "bin", 4)
        x.resize(1,0)
        x.resize(4,0)
        print(x)                      
        self.assertEqual("0000", x.get_bin_str())

        x = IclNumber("'bx100", "bin", 4)
        y = x.copy()
        self.assertEqual(x.get_bin_str(), y.get_bin_str())
        
        x = IclNumber("x100", "hex", -1)
        y = x.copy()
        self.assertEqual(x.get_bin_str(), y.get_bin_str())
            
        x = IclNumber("x101", "bin", -1)
        print(x)
        self.assertEqual(x.get_bin_bit_str(0), "1")
        self.assertEqual(x.get_bin_bit_str(1), "0")
        self.assertEqual(x.get_bin_bit_str(2), "1")
        self.assertEqual(x.get_bin_bit_str(3), "x")

        x.set_bit(0,0)
        x.set_bit(0,1)
        print(x)

        self.assertEqual(x.get_bin_bit_str(0), "0")
        self.assertEqual(x.get_bin_bit_str(1), "0")

        x.set_bit(1,0)
        print(x)

        self.assertEqual(x.get_bin_bit_str(0), "1")
        self.assertEqual(x.get_bin_bit_str(1), "0")

        x.set_bit(1,1)
        print(x)
        self.assertEqual(x.get_bin_bit_str(0), "1")
        self.assertEqual(x.get_bin_bit_str(1), "1")

        #def test_isupper(self):
        #    self.assertTrue('FOO'.isupper())
        #    self.assertFalse('Foo'.isupper())

        #def test_split(self):
        #    self.assertEqual('foo'.upper(), 'FOO')
        #    s = 'hello world'
        #    self.assertEqual(s.split(), ['hello', 'world'])
        #    # check that s.split fails when the separator is not a string
        #    with self.assertRaises(TypeError):
        #        s.split(2)

if __name__ == '__main__':
    unittest.main()