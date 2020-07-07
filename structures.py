import sys
from slither.slither import Slither

from slither.core.solidity_types\
import UserDefinedType, MappingType, FunctionType, ArrayType, ElementaryType, ArrayType

def vars(decl):
    try: # If contract
        return decl.variables
    except: # If struct
        return decl.elems.values()

def structs(decl):
    try: # If contract
        return decl.structures
    except: # If struct
        return []

class StructGraph:
    def __init__(self):
        self.processed = set()
        self.graph = {}

    def add(self, decl):
        if decl.name in self.processed:
            return self

        self.processed.add(decl.name)
        self.graph[decl.name] = set()

        for var in vars(decl):
            print('{},{},{}'.format(decl.name,var,var.type))
            self.add_type_edge(decl.name, var.type)

        for struct in structs(decl):
            self.add(struct)

        return self

    def add_type_edge(self, src, dst_type):
        if isinstance(dst_type, ElementaryType):
            self.add_edge(src, dst_type.type)
        elif isinstance(dst_type, UserDefinedType):
            self.add_edge(src, dst_type.type.name)
        elif isinstance(dst_type, MappingType):
            self.add_type_edge(src, dst_type.type_from)
            self.add_type_edge(src, dst_type.type_to)
        elif isinstance(dst_type, FunctionType):
            for param in dst_type.params:
                self.add_type_edge(src, param.type)

            for return_var in dst_type.return_values:
                self.add_type_edge(src, return_var.type)
        elif isinstance(dst_type, ArrayType):
            self.add_type_edge(src, dst_type.type)
        else:
            raise Exception('Unknown type: {} ({})'.format(dst_type, type(dst_type)))

    def add_edge(self, src, dst):
        self.graph[src].add(dst)

def main(args):
    if len(args) < 2:
        print("Usage: python get-conditions.py FILENAME")
        exit(1)

    slither = Slither(args[1])
    g = StructGraph()
    for c in slither.contracts:
        g.add(c)
    print(g.graph)

if __name__ == '__main__':
    main(sys.argv)

