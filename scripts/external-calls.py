import sys
from slither.slither import Slither

from collections import Counter

def record_call_set(res, call_set_name, it):
    for con, func in [(str(con), str(func)) for con, func in it]:
        res[call_set_name + '_func'][func] += 1
        res[call_set_name + '_call'][(con, func)] += 1

def analyze(fname):
    res = {
        'fname': fname,
        'external_func': Counter(),
        'external_call': Counter(),
        'internal_func': Counter(),
        'internal_call': Counter(),
        'library_func': Counter(),
        'library_call': Counter(),
        'success': False
    }

    try:
        slither = Slither(fname, disable_solc_warnings=True)

        for c in slither.contracts:
            # print('Contract: {}'.format(c.name))

            for function in c.functions:
                # print('Function: {}'.format(function.name))

                record_call_set(res, 'external', function.all_high_level_calls())
                record_call_set(res, 'internal', [(c, f) for f in function.all_internal_calls()])
                record_call_set(res, 'library', function.all_library_calls())

                # print('External calls: {}'.format(external_calls))
        res['success'] = True
    except Exception as e:
        # raise e
        pass

    for k in res:
        if isinstance(res[k], Counter):
            res[k] = dict(res[k])

    print(res)

def main(args):
    if len(args) < 2:
        print("Usage: python3 external-calls.py FILENAME")
        exit(1)

    for fname in args[1:]:
        analyze(fname)

if __name__ == '__main__':
    main(sys.argv)

