import sys

from collections import Counter

from tqdm import tqdm

def aggregate_counter(results, counter_name, counter):
    counter_name_unique = counter_name + '_unique'
    counter_name_uses = counter_name + '_uses'

    if not counter_name in results:
        results[counter_name] = Counter()
        results[counter_name_unique] = Counter()
        results[counter_name_uses] = 0

    results[counter_name] += counter
    for k in counter.items():
        results[counter_name_unique][k] += 1
    results[counter_name_uses] += 1 if len(counter) > 1 else 0

def main(args):
    if len(args) < 2:
        print("Usage: python3 analyze-external-calls.py RESULTS_FILE")
        exit(1)

    fname = args[1]

    total = 0

    counts = {
        'success': 0,
        'writes_after_internal_call': 0,
        'writes_after_internal_state_change_call': 0,
        'writes_after_external_call': 0,
        'writes_after_non_library_call': 0,
        'reads_after_internal_call': 0,
        'reads_after_internal_state_change_call': 0,
        'reads_after_external_call': 0,
        'reads_after_non_library_call': 0
    }

    results = {
        'counts': counts
    }

    uses_external_calls = 0
    call_counter = Counter()
    unique_call_counter = Counter()
    func_counter = Counter
    unique_func_counter = Counter()

    with open(fname, 'r') as f:
        for line in tqdm(f):
            res = eval(line)

            total += 1

            for k in counts:
                if res[k]:
                    counts[k] += 1

            for k in res:
                if isinstance(res[k], dict):
                    res[k] = Counter(res[k])
                    aggregate_counter(results, k, res[k])

                    # It only makes sense to do this part for the Counter that count (contract, function) pairs, because
                    # we need to know if the call is being made to the SafeMath library
                    if k.endswith('call'):
                        non_safe_math_calls = Counter({(con, func): count for (con, func), count in res['external_call'].items() if con != 'SafeMath'})
                        aggregate_counter(results, 'non_safe_math_call', non_safe_math_calls)

            non_library_calls = res['external_call'] - res['library_call']
            aggregate_counter(results, 'non_library_call', non_library_calls)

    # print(results)
    print('Counts ({} total): {}'.format(total, counts))
    print('Uses external calls: {}'.format(results['external_call_uses']))
    print('Uses non-library calls: {}'.format(results['non_library_call_uses']))
    print('Uses non-SafeMath calls: {}'.format(results['non_safe_math_call_uses']))
    print('Uses internal calls: {}'.format(results['internal_call_uses']))
    print('Uses internal state change calls: {}'.format(results['internal_state_change_call_uses']))

    for k in results:
        if isinstance(results[k], Counter):
            print(k, ':', results[k].most_common(10))

if __name__ == '__main__':
    main(sys.argv)

