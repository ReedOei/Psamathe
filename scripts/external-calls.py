import sys
from slither.slither import Slither
from slither.exceptions import SlitherError
from slither.core.declarations import Function

from collections import Counter

def record_call_set(res, call_set_name, it):
    for con, func in [(str(con), str(func)) for con, func in it]:
        # require(E) doesn't really count as an internal call...
        if not 'require(bool)' in func:
            res[call_set_name + '_func'][func] += 1
            res[call_set_name + '_call'][(con, func)] += 1

def explore_call_usage(calls, f, found_call, explored, node):
    to_explore = [node]

    while len(to_explore) > 0:
        node = to_explore.pop(0)

        if node is None:
            continue

        if node in explored:
            continue

        if found_call and len(f(node)) > 0:
            return True

        if not found_call and len(calls(node)) > 0:
            # Reset the explored list because we now know that everything after could be after a call
            return explore_call_usage(calls, f, True, [], node)

        explored.append(node)
        to_explore.extend(node.sons)

    return False

def do_explore(calls, f, node):
    return explore_call_usage(calls, f, False, [], node)

def external_calls(node):
    return node.high_level_calls

def internal_calls(node):
    return node.internal_calls

def internal_state_change_calls(state_changing_func_names):
    def f(node):
        return [func for func in node.internal_calls if func.name in state_changing_func_names]
    return f

def non_library_calls(node):
    return list(set(node.high_level_calls) - set(node.library_calls))

def declarer(default, func):
    if isinstance(func, Function):
        return func.contract_declarer
    else:
        return default

def signature(func):
    name, args, ret = func.signature
    # This can happen when we access some public field using accessor notation (e.g., c.field())
    if not isinstance(ret, list):
        ret = [ret]
    return (name, tuple(map(str, args)), tuple(map(str, ret)))

def analyze(fname):
    res = {
        'fname': fname,
        'external_func': Counter(),
        'external_call': Counter(),
        'internal_func': Counter(),
        'internal_call': Counter(),
        'library_func': Counter(),
        'library_call': Counter(),
        'internal_state_change_call': Counter(),
        'internal_state_change_func': Counter(),
        'writes_after_internal_call': False,
        'writes_after_internal_state_change_call': False,
        'writes_after_external_call': False,
        'writes_after_non_library_call': False,
        'reads_after_internal_call': False,
        'reads_after_internal_state_change_call': False,
        'reads_after_external_call': False,
        'reads_after_non_library_call': False,
        'external_call_num': 0,
        'external_call_checked_num': 0,
        'call_graph': {},
        'success': False
    }

    try:
        slither = Slither(fname, disable_solc_warnings=True)

        for c in slither.contracts:
            # print('Contract: {}'.format(c.name))

            state_changing_func_names = set(func.name for func in c.functions if len(func.all_state_variables_written()) > 0)

            for function in c.functions:
                record_call_set(res, 'external', function.all_high_level_calls())
                record_call_set(res, 'internal', [(declarer(c, f), f) for f in function.all_internal_calls()])
                record_call_set(res, 'internal_state_change', [(declarer(c, f), f) for f in function.all_internal_calls() if f.name in state_changing_func_names])
                record_call_set(res, 'library', function.all_library_calls())

                this_func = (c.name, signature(function))

                res['call_graph'][this_func] = set()

                for con, func in function.all_high_level_calls():
                    if func is not None:
                        res['call_graph'][this_func].add((str(con), signature(func)))

                for func in function.all_internal_calls():
                    if func is not None and isinstance(func, Function):
                        res['call_graph'][this_func].add((str(func.contract_declarer), signature(func)))

                res['writes_after_internal_call'] |= do_explore(internal_calls, lambda n: n.state_variables_written, function.entry_point)
                res['writes_after_internal_state_change_call'] |= do_explore(internal_state_change_calls(state_changing_func_names), lambda n: n.state_variables_written, function.entry_point)
                res['writes_after_external_call'] |= do_explore(external_calls, lambda n: n.state_variables_written, function.entry_point)
                res['writes_after_non_library_call'] |= do_explore(non_library_calls, lambda n: n.state_variables_written, function.entry_point)

                res['reads_after_internal_call'] |= do_explore(internal_calls, lambda n: n.state_variables_read, function.entry_point)
                res['reads_after_internal_state_change_call'] |= do_explore(internal_state_change_calls(state_changing_func_names), lambda n: n.state_variables_read, function.entry_point)
                res['reads_after_external_call'] |= do_explore(external_calls, lambda n: n.state_variables_read, function.entry_point)
                res['reads_after_non_library_call'] |= do_explore(non_library_calls, lambda n: n.state_variables_read, function.entry_point)

                for node in function.nodes:
                    num = len(node.high_level_calls)
                    if num > 0:
                        res['external_call_num'] += num
                        if node.is_conditional():
                            res['external_call_checked_num'] += num

                # print('External calls: {}'.format(external_calls))

        res['success'] = True
    except SlitherError as e:
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

