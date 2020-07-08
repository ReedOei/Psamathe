import sys

from collections import Counter

from tqdm import tqdm

def main(args):
    if len(args) < 2:
        print("Usage: python3 analyze-external-calls.py RESULTS_FILE")
        exit(1)

    fname = args[1]

    total = 0
    successes = 0
    results = {
        'non_library_call': Counter()
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

            if res['success']:
                successes += 1

            for k in res:
                if isinstance(res[k], dict):
                    res[k] = Counter(res[k])
                    if not k in results:
                        results[k] = Counter()
                        results[k + '_unique'] = Counter()
                        results[k + '_uses'] = 0

                    results[k] += res[k]
                    for call in res[k].items():
                        results[k + '_unique'][call] += 1
                    results[k + '_uses'] += 1 if len(res[k]) > 1 else 0

            non_library_calls = res['external_call'] - res['library_call']
            results['non_library_call'] += non_library_calls

    print(results)
    print('Success: {} of {}'.format(successes, total))
    print('Uses external calls: {}'.format(results['uses_external_call']))
    print('Uses internal calls: {}'.format(results['uses_internal_call']))

if __name__ == '__main__':
    main(sys.argv)

