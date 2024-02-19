class IclNumber:
    def __init__(self, in_value, value_type, size=-1):
        self.r_number = 0
        self.x_numer = 0
        self.size = size

        source = in_value
        source = source.replace("_", "")        
        source = source.replace("'", "")          
        source = source.replace(" ", "")

        if(value_type == "dec"):
            source = source.replace("d", "")          
            source = source.replace("D", "")               
            self.r_number = int(source)
            # TODO: Add size check

        elif(value_type == "hex"):
            source = source.replace("h", "")          
            source = source.replace("H", "")               
            for index, value in enumerate(reversed(source)):
                if((value == "X") or (value == "x")):
                    self.x_number += 1 << index*4 
                else:
                    self.r_number +=  int(value, 16) << index*4
            # TODO: Add size check            

        elif(value_type == "bin"):
            source = source.replace("b", "")          
            source = source.replace("B", "")  
            for index, value in enumerate(reversed(source)):
                if((value == "X") or (value == "x")):
                    self.x_number += 1 << index
                else:
                    self.r_number += int(value, 2) << index                  
            # TODO: Add size check            

    def concat(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be concated with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.size == -1) or (obj_2.size == -1)):
            raise ValueError("Unsized variables cannot be concated")
        number = (self.r_number <<  obj_2.size) + obj_2.r_number
        size = self.size + obj_2.size
        return IclNumber(str(number), "dec", size) 

    def get_size(self):
        return self.size
    
    def get_number(self):
        if(self.x_numer > 0):
            raise ValueError("{}:number cannot be converted to pure number, it contrains x".format(self.__str__()))
        return self.r_number
        
    def sized_number(self):
        return 1 if self.size > -1 else 0

    def get_bit(self, index):
        if((index >= self.size) and (self.size != -1)):
            raise ValueError("Index {} is bigger than size {}".format(index, self.size))
        else:
            num = IclNumber("0", "dec",1)
            num.r_number = (self.r_number >> index) & 1
            num.x_numer = (self.x_numer >> index) & 1
            return num
    
    def __str__(self):
        return "Size:{0}, 0x{1:x}, 0x{2:x}".format(self.size, self.r_number, self.x_numer)

    def __repr__(self):
        num_repr = str(bin(self.r_number))
        return num_repr
    
    def __add__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be added with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_numer > 0) or (obj_2.x_numer > 0)):
            raise ValueError("Numbers with x(UNKNOWN) cannot be added")
        return IclNumber(str(self.r_number + obj_2.r_number), "dec") 


    def __sub__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be substracted with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_numer > 0) or (obj_2.x_numer > 0)):
            raise("Numbers with x(UNKNOWN) cannot be substracted")
        return IclNumber(str(self.r_number - obj_2.r_number), "dec") 

    def __mul__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be multiplayed with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_numer > 0) or (obj_2.x_numer > 0)):
            raise ValueError("Numbers with x(UNKNOWN) cannot be substracted")
        return IclNumber(str(self.r_number * obj_2.r_number), "dec") 

    def __truediv__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be divided with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_numer > 0) or (obj_2.x_numer > 0)):
            raise ValueError("Numbers with x(UNKNOWN) cannot be divided")
        return IclNumber(str(self.r_number // obj_2.r_number), "dec") 

    def __floordiv__(self, obj_2):
        return self.__truediv__(self, obj_2)
    
    def __mod__(self, obj_2):
        if(not isinstance (obj_2, IclNumber)):
            raise ValueError("Object of class {0} can not be modulo with object of class {1}".format(type(self).__name__ , type(obj_2).__name__))
        if((self.x_numer > 0) or (obj_2.x_numer > 0)):
            raise ValueError("Numbers with x(UNKNOWN) cannot be modulo")
        return IclNumber(str(self.r_number % obj_2.r_number), "dec") 

    def __invert__(self):
        if(self.size == -1):
            bit_len  = self.r_number.bit_length()
            number = (~self.r_number) & ((1<< bit_len) - 1)            
        else:
            number = (~self.r_number) & ((1<< self.size) - 1)
        
        return IclNumber(str(number), "dec", self.size) 
    