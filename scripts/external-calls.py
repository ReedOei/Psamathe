import sys
from slither.slither import Slither

from collections import Counter

def main(args):
    if len(args) < 2:
        print("Usage: python3 external-calls.py FILENAME")
        exit(1)

    fname = args[1]
    slither = Slither(fname)

    res = {
        'fname': fname,
        'call_counter': Counter()
    }

    for c in slither.contracts:
        # print('Contract: {}'.format(c.name))

        for function in c.functions:
            # print('Function: {}'.format(function.name))

            all_high_level_calls = set((str(con), str(func)) for con, func in function.all_high_level_calls() if str(con) != "SafeMath")
            all_library_calls = set((str(con), str(func)) for con, func in function.all_library_calls())

            external_calls = all_high_level_calls - all_library_calls

            for con, func in external_calls:
                res['call_counter'][func] += 1

            # print('External calls: {}'.format(external_calls))

    res['call_counter'] = dict(res['call_counter'])
    print(res)

if __name__ == '__main__':
    main(sys.argv)

