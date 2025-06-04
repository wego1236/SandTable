import sys
import os
import jq
import json
import argparse
import shutil

show_status=True

def set_path():
    script_dir = os.path.dirname(os.path.realpath(__file__))
    deps_dir = os.path.join(os.path.dirname(os.path.dirname(script_dir)), 'deps')
    sys.path.append(os.path.realpath(os.path.join(deps_dir, 'tlc-cmd')))
    # print(sys.path)

set_path()

from trace_reader import TraceReader

# def sigint_handler(signum, frame):
#     print('TC-Gen Caught SIGINT, Ctrl+C again to exit')
#     signal.signal(signal.SIGINT, signal.SIG_DFL)
#
#
# signal.signal(signal.SIGINT, sigint_handler)

default_config = 'config.txt'
default_output = 'traces.txt'
default_conn_fd = 1022
default_node_port = 9000
default_debug = False
nodes = dict()
node_port = None


def parse_args():
    parser = argparse.ArgumentParser(description="Test case generator for PySyncObj")
    parser.add_argument(dest='trace_file', action='store', help='Trace file')
    parser.add_argument('-c', dest='config', action='store', required=True, help='Config file',
                        default=default_config)
    parser.add_argument('-o', dest='output', action='store', required=False, help='Output trace file',
                        default=default_output)
    parser.add_argument('-f', dest='conn_fd', action='store', required=False,
                        help='Interceptor<->Controller connection fd', default=default_conn_fd)
    parser.add_argument('-n', dest='node_port', action='store', required=False, help='Port of test nodes',
                        default=default_node_port)
    parser.add_argument('-d', dest='debug', action='store_true', required=False, help='Print debug msg',
                        default=default_debug)
    parser.add_argument('-i', dest='in_place', action='store_true', required=False, help='Generate in current dir',
                        default=False)
    parser.add_argument('-I', dest='in_dir', action='store', required=False,
                        help='Generate in the specific dir under trace dir', default='')
    arg_parser = parser.parse_args()
    if not arg_parser.in_place:
        arg_parser.trace_file = os.path.realpath(arg_parser.trace_file)
        arg_parser.config = os.path.realpath(arg_parser.config)

        if arg_parser.in_dir:
            dir_name = os.path.join(os.path.dirname(arg_parser.trace_file), arg_parser.in_dir)
            os.makedirs(dir_name, mode=0o755, exist_ok=True)
        else:
            dir_name = os.path.dirname(arg_parser.trace_file)
        base_name = os.path.basename(arg_parser.trace_file)
        test_case_dir = base_name + '.dir'
        # new_name = os.path.join(test_case_dir, base_name)

        os.chdir(dir_name)
        os.makedirs(test_case_dir, mode=0o755, exist_ok=True)
        # os.mkdir(test_case_dir, mode=0o755)
        # os.rename(arg_parser.trace_file, new_name)
        # arg_parser.trace_file = new_name
        os.chdir(test_case_dir)

    return arg_parser


def eprint(*largs, **kvargs):
    if args.debug:
        print(*largs, **kvargs, file=sys.stderr)


def read_config():
    global nodes, node_port
    with open(args.config) as f:
        map_cidr = dict()
        for line in f:
            line = line.strip()
            if line.startswith('map-cidr'):
                _, fake, real = [cidr.replace('.0/24', '') for cidr in line.split(' ', 3)]
                map_cidr[real] = fake
                eprint('Read cmd:', 'map-cidr', fake + '.0/24', real + '.0/24')
            elif line.startswith('node'):
                _, name, ip = line.split(' ', 3)
                for k, v in map_cidr.items():
                    if k in ip:
                        nodes[name] = ip.replace(k, v)
                        eprint('Read cmd:', 'node', name, nodes[name])
                        break
            elif line.startswith('router'):
                _, router_addr = line.split(' ', 2)
                _, router_port = router_addr.split(':', 2)
                try:
                    router_port = int(router_port)
                    node_port = router_port
                except Exception:
                    eprint('Router port is invalid')
                    pass
            else:
                eprint('Ignored cmd:', line)
    if node_port is None:
        node_port = args.node_port


def check_test_code_is_generated(config_file, testcase_in_parent_dir):
    if args.in_place:
        return False
    for i in nodes.keys():
        if os.path.exists(os.path.join(os.path.dirname(config_file) if testcase_in_parent_dir else '.', i + '.py')):
            return True
    return False


def yield_trace(states):
    model_value = ''
    model_value_replace = {"Follower": "1", "PreCandidate": "2", "Candidate": "3", "Leader": "4"}
    # for k,v in nodes.items():
    #     model_value_replace["TCPNode('{}:{}')".format(v, node_port)] = k
    def get_converted_model_value(n, model_var_name):
        nonlocal model_value
        if model_var_name == 'log':
            model_value = list(map(lambda t: tuple(t.values()), model_value))
        elif model_var_name == 'raftState':
            model_value = model_value_replace[model_value]
        elif model_var_name in {'nextIndex', 'matchIndex', 'progress', 'pr_pending'}:
            if n in model_value:
                model_value.pop(n)
            
        return str(model_value)
    def compare(n, code_var_name, model_var_name, no_compare=False):
        nonlocal model_value
        yield ['execute', n, 'get {}'.format(code_var_name)]
        model_value = cur_state[model_var_name][n]
        yield ['#', 'variable', model_var_name, n, get_converted_model_value(n, model_var_name)]
        if not no_compare:
            yield ['compare', 'variable']
        else:
            yield ['compare', 'none']

    def do_tick(n, is_compare=True):
        nonlocal model_value
        yield ['execute', n, 'raft periodic']
        yield ['nop']
        if is_compare:
            yield from compare(n, 'commit_idx', 'commitIndex')
            yield from compare(n, 'current_term', 'currentTerm')
            yield from compare(n, 'pending_snapshot', 'pending_snapshot')
            yield from compare(n, 'log', 'log')
            yield from compare(n, 'state', 'raftState')
            if model_value == "4":  # leader
                yield from compare(n, 'progress', 'progress', no_compare=True)   
                yield from compare(n, 'pr_pending', 'pr_pending')   
                yield from compare(n, 'next_idx', 'nextIndex')
                yield from compare(n, 'match_idx', 'matchIndex')
                
    def deliver(src, dst):
        yield ['deliver', src, dst]
        # yield ['loop', 'intercept', dst, 'check_has_recv_queue', nodes[src]+':0']
        yield ['loop', 'intercept', dst, 'check_has_recv_queue', src]
        yield ['execute', dst, 'raft recvfrom {}'.format(src)]
        yield from do_tick(dst)
    partitioned_nodes = []
    jq_trace = jq.compile('.[].netcmd')
    jq_msgs = jq.compile('.[].msgs')
    states_counter = 0
    for i, msg, cur_state in zip(jq_trace.input(states), jq_msgs.input(states), states):
        states_counter += 1
        
        if len(i) > 1:      
            comment = i[0]
            netcmd = i[1]
            cmd, *parameters = netcmd
            # print("comment\n", comment)
            # print("cmd\n", cmd)
            # print("parameters\n", parameters)

            yield ['#', '[' + str(states_counter) + ']'] + [str(comment)]
            yield ['#', json.dumps(netcmd)]
            if cmd == 'conn_part_flush':  # network partition
                # TODO: currently only one node is partitioned
                partitioned_nodes.append(parameters[0][0])
                yield ['partition', parameters[0][0]]
            elif cmd == 'conn_cure':  # network cure
                for n in partitioned_nodes:
                    yield ['recover', n]
                    for _ in range(2):
                        for j in nodes:
                            yield ['execute', j, 'net connectall']
                            # yield ['intercept', j, 'inc_time_ms', '60']  # > 0.05s reconnection
                            yield from do_tick(j)
                    yield ['wait-recover']
                    for j in nodes:
                        yield ['loop', 'execute', j, 'net isallconnected']
                partitioned_nodes = []
            elif cmd == 'msg_del':  # recv msg (deliver to node)
                # yield ['deliver', parameters[0], parameters[1]]
                yield from deliver(parameters[1], parameters[0])
            elif cmd == 'msg_add':  # send msg (enqueued in controller)
                if comment[0] == 'DoSnapRequest':
                    # yield from batch_tick(election_tick)
                    yield ['execute', comment[1], 'raft askSnap'] 
                    yield ['nop'] 
                yield from do_tick(comment[1])
                # assert False
                # pass  # not used
            elif cmd == 'msg_add_dropped':  # send msg but dropped due to partition
                assert False
                pass  # not used
            elif cmd == 'msg_reply':  # recv (deliver) msg and send (enqueue) msg
                # yield ['deliver', parameters[1], parameters[0]]
                yield from deliver(parameters[1], parameters[0])
            elif cmd == 'msg_reply_dropped':  # reply but dropped
                # yield ['deliver', parameters[1], parameters[0]]
                yield from deliver(parameters[1], parameters[0])
            elif cmd == 'msg_do_nothing':
                if comment[0] == 'RecvEntry':
                    yield ['execute', comment[1], "raft cli {}".format(comment[2])]
                    yield ['nop'] 
                elif comment[0] == 'DoBecomeLeader':
                    yield ['execute', comment[1], 'raft BecomeLeader'] 
                    yield ['nop'] 
                yield from do_tick(comment[1])
            elif cmd == 'msg_batch_add':  # batch send msgs
                def batch_tick(n) :
                    for _ in range(n):
                       yield ['execute', comment[1], 'raft periodic']
                    # yield ['execute', comment[1], 'raft periodic']
                # election_tick heart_beat_tick 都是和rust相统一
                election_tick = 11
                heart_beat_tick = 4
                if comment[0] == 'BecomePrecandidate':
                    # yield from batch_tick(election_tick)
                    yield ['execute', comment[1], 'raft campaign pre'] 
                    yield ['nop'] 
                elif comment[0] == 'ElectionTimeout':
                    yield ['execute', comment[1], 'raft campaign normal'] 
                    yield ['nop'] 
                    # yield ['execute', comment[1], 'raft campaign normal']  
                elif comment[0] == 'BecomeCandidate':
                    yield ['execute', comment[1], 'raft campaign normal'] 
                    yield ['nop'] 
                    # yield ['execute', comment[1], 'raft campaign normal']  
                elif comment[0] == 'DoBecomeLeader':
                    yield ['execute', comment[1], 'raft BecomeLeader'] 
                    yield ['nop'] 
                elif comment[0] == 'SendAppendentriesAll':
                    yield ['execute', comment[1], 'raft bcast_append'] 
                    yield ['nop'] 
                elif comment[0] == 'SendHeartBeatAll':
                    yield ['execute', comment[1], 'raft heartBeat'] 
                    yield ['nop'] 
                    # yield ['intercept', comment[1], 'inc_time_ms', '300']  # > 0.2s
                elif comment[0] == 'RecvEntry':
                    yield ['execute', comment[1], "raft cli {}".format(comment[2])]
                yield from do_tick(comment[1])
            elif cmd == 'msg_batch_add_reply':  # recv msg and batch send msgs
                # yield ['deliver', parameters[1], parameters[0]]
                yield from deliver(parameters[1], parameters[0])
        else:
            yield ['init', str(i[0][1])]
            for j in nodes:
                yield ['execute', j, 'net connectall']
                yield ['execute', j, 'raft init']
                # yield from do_tick(j)
            yield ['wait-init', str(i[0][1])]
            # yield ['deliver-all', str(len(nodes))]
            for j in nodes:
                yield ['loop', 'execute', j, 'net isallconnected']
            for j in nodes:
                yield from do_tick(j)
        if show_status:
            yield ['status']
            for src in nodes:
                msgs_info_str = 'msgs {}:'.format(src)
                for dst in nodes:
                    if src != dst:
                        msgs_info_str += ' {}({})'.format(dst, len(msg[src][dst]))
                yield ['#', msgs_info_str]
            yield ['compare', 'net']
        yield ['finish one step']
    for i in nodes:
        yield ['execute', i, "raft statemachine"]
    eprint("Finish write:", args.output)

def copy_config_file(config_file, testcase_in_parent_dir):
    try:
        if testcase_in_parent_dir:
            os.symlink(os.path.dirname(config_file), 'config')
        else:
            shutil.copy2(config_file, os.path.join('..' if testcase_in_parent_dir else '.', os.path.basename(config_file)))
    except:
        pass

def gen_trace():
    tr = TraceReader(True)
    try:
        os.symlink(args.trace_file, 'tlc_trace.txt')
    except:
        pass
    states = list(tr.trace_reader(args.trace_file))
    eprint('Read states:', len(states))
    traces = list(yield_trace(states))
    # for index, trace in enumerate(traces):
    #     for sub_index, item in enumerate(trace):
    #         if not isinstance(item, str):
    #             print(f"在 traces 的第 {index} 项的第 {sub_index} 个元素是非字符串类型，其值为 {item}，类型为 {type(item)}")

    # print('\n'.join(' '.join(i) for i in traces))
    with open('traces.txt', 'w') as f:
        f.write('\n'.join(' '.join(i) for i in traces))


if __name__ == '__main__':
    args = parse_args()
    read_config()
    copy_config_file(args.config, not args.in_place)
    gen_trace()
