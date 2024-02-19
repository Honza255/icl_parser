
class IclSignal:
    
    def fill_numbers(self, index_l: int, index_h: int) -> list:
        if index_l <= index_h:
            return list(range(index_l, index_h + 1))
        else:
            return list(range(index_l, index_h - 1, -1))
            
    def __init__(self, name,  index_l=None, index_h = None):
        self.hier = []
        self.name = name
        self.neg = 0
        if((index_h is not None) and (index_l is not None)):
            self.indexes = self.fill_numbers(index_l, index_h)
        elif((index_h is None) and (index_l is not None)):
            self.indexes = [index_l]
        elif((index_h is not None) and (index_l is None)):            
            raise ValueError("Index high defined but index low is not defined")
        else:
            self.indexes = []


    def add_hiearachy(self, hier_lvl):
        self.hier.append(hier_lvl)

    def has_hier(self):
        if(self.hier):
            return 1
        else:
            return 0
        
    def ovveride_indexes(self, indexes):
        self.indexes = indexes
       
    def get_indexes(self):
        return self.indexes
    
    def get_name(self):
        return self.name
    
    def get_relative_name(self):
        str = ""
        for item in self.hier:
            str += item + "."
        str += self.name
        return str

    def get_size(self):
        return len(self.indexes)

    def __invert__(self):
        self.neg = self.neg ^ 1

    def __str__(self) -> str:
        str = "~" if self.neg else ""
        for item in self.hier:
            str += item + "."
        str += self.name
        if(self.indexes):
            str += "{}".format(self.indexes)
        return str
    
    def __repr__(self):
        return self.__str__()
