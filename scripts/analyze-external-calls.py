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

def find_recursive(call_graph, current_path, current_node):
    if len(current_path) > 0 and current_node == current_path[0]:
        yield frozenset(current_path)
    elif current_node in current_path:
        return
    else:
        current_path = current_path + [current_node]

        if current_node in call_graph:
            for next_node in call_graph[current_node]:
                yield from find_recursive(call_graph, current_path, next_node)

def read_file(f):
    for line in f:
        # Sometimes two lines will get output at the same time, leading to stuff like {A}{B}, which we just need to split
        split = line.split('}{')
        for part in split:
            part = part.strip()
            if len(part) == 0:
                continue
            if not part.startswith('{'):
                part = '{' + part
            if not part.endswith('}'):
                part = part + '}'
            yield part

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
        'counts': counts,
    }

    internal_state_change_or_non_library_uses = 0
    recursive_funcs = 0
    recursive_loops =0
    has_recursive_func = 0
    has_recursive_loop = 0
    external_call_num = 0
    external_call_checked_num = 0

    with open(fname, 'r') as f:
        for line in tqdm(read_file(f)):
        # for line in f:
            if len(line) == 0:
                continue

            res = eval(line)

            total += 1

            used = set()
            recursive = set()
            for node in res['call_graph']:
                recursive = recursive.union(find_recursive(res['call_graph'], [], node))

            recursive_funcs_list = [loop for loop in recursive if len(loop) == 1]
            recursive_loops_list = [loop for loop in recursive if len(loop) > 1]

            if len(recursive_loops_list) > 0:
                print(res['fname'], recursive_funcs_list, recursive_loops_list)

            recursive_funcs += len(recursive_funcs_list)
            recursive_loops += len(recursive_loops_list)
            has_recursive_func += 1 if len(recursive_funcs_list) > 0 else 0
            has_recursive_loop += 1 if len(recursive_loops_list) > 0 else 0

            external_call_num += res['external_call_num']
            external_call_checked_num += res['external_call_checked_num']

            for k in counts:
                if res[k]:
                    counts[k] += 1

            for k in res:
                if k != 'call_graph' and isinstance(res[k], dict):
                    res[k] = Counter(res[k])
                    aggregate_counter(results, k, res[k])

                    # It only makes sense to do this part for the Counter that count (contract, function) pairs, because
                    # we need to know if the call is being made to the SafeMath library
                    if k.endswith('call'):
                        non_safe_math_calls = Counter({(con, func): count for (con, func), count in res['external_call'].items() if con != 'SafeMath'})
                        aggregate_counter(results, 'non_safe_math_call', non_safe_math_calls)

            non_library_calls = res['external_call'] - res['library_call']
            aggregate_counter(results, 'non_library_call', non_library_calls)
            internal_state_change_or_non_library_uses += 1 if len(res['internal_state_change_call']) > 0 or len(non_library_calls) > 0 else 0

    # print(results)
    print('Counts ({} total): {}'.format(total, counts))
    print('Uses external calls: {}'.format(results['external_call_uses']))
    print('Uses non-library calls: {}'.format(results['non_library_call_uses']))
    print('Uses non-SafeMath calls: {}'.format(results['non_safe_math_call_uses']))
    print('Uses internal calls: {}'.format(results['internal_call_uses']))
    print('Uses internal state change calls: {}'.format(results['internal_state_change_call_uses']))
    print('Uses internal state change calls or non-library external calls: {}'.format(internal_state_change_or_non_library_uses))
    print('Recursive functions: {}'.format(recursive_funcs))
    print('Recursive loops: {}'.format(recursive_loops))
    print('Uses recursive functions: {}'.format(has_recursive_func))
    print('Uses recursive loops: {}'.format(has_recursive_loop))
    print('External calls: {}'.format(external_call_num))
    print('Checked external calls: {}'.format(external_call_checked_num))

    # for k in results:
    #     if isinstance(results[k], Counter):
    #         print(k, ':', results[k].most_common(10))

if __name__ == '__main__':
    main(sys.argv)

