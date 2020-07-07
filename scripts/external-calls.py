import sys
from slither.slither import Slither

def main(args):
    if len(args) < 2:
        print("Usage: python3 external-calls.py FILENAME")
        exit(1)

    fname = args[1]
    slither = Slither(fname)

    calls_external = False

    for c in slither.contracts:
        # print('Contract: {}'.format(c.name))

        for function in c.functions:
            # print('Function: {}'.format(function.name))

            # From: https://github.com/crytic/slither/blob/master/slither/core/declarations/function.py
            external_calls = [x.external_calls_as_expressions for x in function.nodes]
            external_calls = [x for x in external_calls if x]
            external_calls = [item for sublist in external_calls for item in sublist]
            external_calls = list(set(external_calls))

            calls_external |= len(external_calls) > 0

            # print('External calls: {}'.format(external_calls))

    print('{},{}'.format(fname, calls_external))

if __name__ == '__main__':
    main(sys.argv)

