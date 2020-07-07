import ast
import sys

from collections import Counter

def main(args):
    if len(args) < 2:
        print("Usage: python3 analyze-external-calls.py RESULTS_FILE")
        exit(1)

    fname = args[1]

    uses_external_calls = 0
    call_counter = Counter()
    unique_call_counter = Counter()

    with open(fname, 'r') as f:
        results = [ast.literal_eval(line) for line in f]

    for res in results:
        c = Counter(res['call_counter'])
        uses_external_calls += 1 if sum(c.values()) > 0 else 0
        call_counter += c
        unique_call_counter += Counter({k: 1 for k, _ in c.items()})

    print('Uses external calls: {} of {}'.format(uses_external_calls, len(results)))
    print(call_counter.most_common(50))
    print(unique_call_counter.most_common(50))

if __name__ == '__main__':
    main(sys.argv)


