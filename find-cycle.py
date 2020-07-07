import ast
import itertools
import sys

# From Slither
Int = ['int', 'int8', 'int16', 'int24', 'int32', 'int40', 'int48', 'int56', 'int64', 'int72', 'int80', 'int88', 'int96', 'int104', 'int112', 'int120', 'int128', 'int136', 'int144', 'int152', 'int160', 'int168', 'int176', 'int184', 'int192', 'int200', 'int208', 'int216', 'int224', 'int232', 'int240', 'int248', 'int256']

Uint = ['uint', 'uint8', 'uint16', 'uint24', 'uint32', 'uint40', 'uint48', 'uint56', 'uint64', 'uint72', 'uint80', 'uint88', 'uint96', 'uint104', 'uint112', 'uint120', 'uint128', 'uint136', 'uint144', 'uint152', 'uint160', 'uint168', 'uint176', 'uint184', 'uint192', 'uint200', 'uint208', 'uint216', 'uint224', 'uint232', 'uint240', 'uint248', 'uint256']

Byte = ['byte', 'bytes', 'bytes1', 'bytes2', 'bytes3', 'bytes4', 'bytes5', 'bytes6', 'bytes7', 'bytes8', 'bytes9', 'bytes10', 'bytes11', 'bytes12', 'bytes13', 'bytes14', 'bytes15', 'bytes16', 'bytes17', 'bytes18', 'bytes19', 'bytes20', 'bytes21', 'bytes22', 'bytes23', 'bytes24', 'bytes25', 'bytes26', 'bytes27', 'bytes28', 'bytes29', 'bytes30', 'bytes31', 'bytes32']

# https://solidity.readthedocs.io/en/v0.4.24/types.html#fixed-point-numbers
M = list(range(8, 257, 8))
N = list(range(0, 81))
MN = list(itertools.product(M,N))

Fixed = ['fixed{}x{}'.format(m,n) for (m,n) in MN] + ['fixed']
Ufixed = ['ufixed{}x{}'.format(m,n) for (m,n) in MN] + ['ufixed']

ElementaryTypeName = set(['address', 'bool', 'string', 'var'] + Int + Uint + Byte + Fixed + Ufixed)

def find_cycle(g, start, seen, node):
    if len(seen) > 0 and node == start:
        return [node]

    if node in seen:
        return None

    # This will happen for primitive types
    if not node in g:
        return None

    seen = set(seen)
    seen.add(node)

    for next_node in g[node]:
        res = find_cycle(g, start, seen, next_node)
        if res is not None:
            return [node] + res

    return None

def max_depth(g, seen, node, cur_depth):
    if node in seen:
        return cur_depth

    if node in ElementaryTypeName:
        return cur_depth - 1

    if not node in g:
        return cur_depth

    seen = set(seen)
    seen.add(node)

    cur_max = cur_depth
    for next_node in g[node]:
        cur_max = max(cur_max, max_depth(g, seen, next_node, cur_depth + 1))

    return cur_max

def big_cat(t):
    if 'function' in t:
        return 'builtin'
    elif t in ElementaryTypeName:
        return 'builtin'
    elif 'mapping' in t:
        return 'builtin'
    elif '[]' in  t:
        return 'builtin'
    else:
        return 'user'

def type_cat(t):
    # TODO: Include this data in the output from "structures.py" so this is unnecessary
    # NOTE: Important function comes first, because it will have other type names in it usually
    if 'function' in t:
        return 'function'
    elif t in ElementaryTypeName:
        return 'prim'
    elif 'mapping' in t:
        return 'mapping'
    elif '[]' in  t:
        return 'array'
    else:
        return 'user'

def process(fname):
    with open(fname, 'r') as f:
        content = f.read().strip()

    if content == '':
        return

    res = {}

    lines = content.split('\n')
    for line in lines[:-1]:
        d,v,t = line.split(',')
        if not d in res:
            res[d] = {}
        res[d][type_cat(t)] = True
        res[d][big_cat(t)] = True

    g = ast.literal_eval(lines[-1])

    skip = []
    for node in g:
        if not node in res:
            res[node] = {}
        res[node]['max_depth'] = max_depth(g, set(), node, 0)

        if node in skip:
            continue

        temp = find_cycle(g, node, set(), node)
        if temp is not None:
            skip.extend(res)
            res[node]['cycle'] = True

    # filename, Contract num, uses built-ins, uses mapping, uses arrays, uses functions, uses user-defined, has-cycles
    data = [fname,
            len(res),
            len([d for d in res if res[d].get('builtin', False)]),
            len([d for d in res if res[d].get('mapping', False)]),
            len([d for d in res if res[d].get('array', False)]),
            len([d for d in res if res[d].get('function', False)]),
            len([d for d in res if res[d].get('user', False)]),
            len([d for d in res if res[d].get('cycle', False)])]

    print(','.join(map(str, data)))
    print(';'.join(map(str, (res[d].get('max_depth', 0) for d in res))))

import os

directory = os.fsencode(sys.argv[1])

for i in os.listdir(directory):
     filename = os.fsdecode(i)
     if filename.endswith(".sol"):
         process(sys.argv[1] + filename)

