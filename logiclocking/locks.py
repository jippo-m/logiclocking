"""Apply logic locks to circuits."""
import random
from itertools import product, zip_longest
from random import choice, choices, randint, sample, shuffle

import circuitgraph as cg
import re

def replace_lut(gate: str, cl, locked_gates: int, key_prefix: str) -> tuple[dict, list, str]:
    key = {}
    m = cg.logic.mux(2 ** len(cl.fanin(gate)))
    fanout = list(cl.fanout(gate))
    fanin = list(cl.fanin(gate))

    # create LUT
    cl.add_subcircuit(m, f"lut_{gate}")

    # create subcircuit containing just gate for simulation
    simc = cg.Circuit()
    for i in fanin:
        simc.add(i, "input")
    simc.add(gate, cl.type(gate), fanin=fanin)

    # connect keys
    for i, vs in enumerate(product([False, True], repeat=len(fanin))):
        assumptions = dict(zip(fanin, vs[::-1]))
        cl.add(
            f"{key_prefix}{locked_gates:04}{i:02}",
            "input",
            fanout=f"lut_{gate}_in_{i}",
        )
        result = cg.sat.solve(simc, assumptions)
        if not result:
            key[f"{key_prefix}{locked_gates:04}{i:02}"] = False
        else:
            key[f"{key_prefix}{locked_gates:04}{i:02}"] = result[gate]

    # connect out
    cl.disconnect(gate, fanout)
    cl.connect(f"lut_{gate}_out", fanout)

    # connect sel
    for i, f in enumerate(fanin):
        cl.connect(f, f"lut_{gate}_sel_{i}")

    # delete gate
    cl.remove(gate)
    # print(gate)
    # print(key)
    return key, [f"lut_{gate}_{n}" for n in m.nodes()], f"lut_{gate}_out"

def inputs_in_fanincone(c, gate):
    inputs = c.inputs()
    transitive_fanin = c.transitive_fanin(gate)
    transitive_fanin_only_input = tuple(inputs & transitive_fanin)
    return transitive_fanin_only_input


def delete_lut_gates_in_paths(c, paths: list[tuple[str]]) -> list[tuple[str]]:
    paths_without_lut = set() # setにすることで重複しているパスを削除
    for path in paths:
        path_without_lut = [] # もとはpath_with_modularized_lutという名前だった
        # 名前が"mux"で始まるゲートを除外
        # lutは内部的にはmuxを使って実装されている
        for gate in path:
            match = re.match("mux", gate)
            if not match:
                path_without_lut.append(gate)
        paths_without_lut.add(tuple(path_without_lut))
    return list(paths_without_lut)


# startからendまでの最長パスを計算する
def calc_longest_path(c, start: str, end: str) -> tuple[str]:
    # circuitgraph の paths メソッドは、start から end までの全ての単純パスを返す
    paths = {tuple(path) for path in c.paths(start, end)}
    paths_without_lut = tuple(delete_lut_gates_in_paths(c, paths))
    return max(paths_without_lut, key=len)


# 各PIからgateまでの最長パスの中で最も長いものを返す
def calc_longest_path_from_pi_to_gate(c, gate) -> tuple[str]:
    inputs = inputs_in_fanincone(c, gate)
    longest_paths = []
    for input in inputs:
        longest_paths.append(calc_longest_path(c, input, gate))
    if not longest_paths:
        return tuple()  # 空のタプルを返す
    return max(longest_paths, key=len)


def align_paths_length(paths: list[tuple[str]], length: int) -> list[tuple[str]]:
    paths_alined = []
    for path in paths:
        if len(path) - 1 < length:
            continue
        if path[-length-1:] in paths_alined:
            continue
        paths_alined.append(path[-length-1:])  # 最後のlength個の要素を取得
    return paths_alined

# 指定された数、長さ、end_gatesのループパスを生成する
def generate_loop_paths_from_endgates(
        c, num_loops, length_loops, end_gates: list[str]
    ) -> list[tuple]:
    all_longest_paths = []
    for end_gate in end_gates:
        all_longest_paths.append(calc_longest_path_from_pi_to_gate(c, end_gate))
    
    # 長さでソート
    all_longest_paths.sort(key=len)
    
    # 長さの条件を満たすパスに絞り込む
    aligned_paths = align_paths_length(all_longest_paths, length_loops)
    
    selected_paths = []
    selected_start_gate_pairs = set()

    for path in aligned_paths:
        if len(selected_paths) >= num_loops:
            break
        
        # パスが十分な長さを持つことを確認
        if len(path) < length_loops + 1: # pathの長さがlength_loopsより1大きい必要がある（例：長さ2なら3つのゲート）
            continue

        current_start_gate_pair = (path[0], path[1])
        if current_start_gate_pair not in selected_start_gate_pairs:
            selected_paths.append(path)
            selected_start_gate_pairs.add(current_start_gate_pair)
    
    return selected_paths

def have_same_start_gates(paths: list[tuple[str]]) -> bool:
    start_gates = set()
    for path in paths:
        if (path[0], path[1]) in start_gates:
            return True
        start_gates.add((path[0], path[1]))
    return False

# path: [ (A, B, C, D), ... ] -> pair_path: [ ((A, B), (B, C), (C, D)), ... ]
def convert_paths_to_pair_paths(paths: list[tuple[str]]) -> list[tuple[tuple[str, str]]]:
    pair_paths = []
    for path in paths:
        pair_path = []
        for i in range(len(path) - 1):
            pair_path.append((path[i], path[i+1]))
        pair_paths.append(tuple(pair_path))
    return pair_paths

# 複数の経路に含まれるすべてのユニークなゲートを抽出する
# [(A, B, C), (B, D, E)] -> [A, B, C, D, E]
def paths_to_gates(paths: list[tuple[str]]) -> list[str]:
    gates = set()
    for path in paths:
        gates |= set(path)
    return list(gates)


def get_gates_fanout_1(c, paths: list[tuple[str]]) -> list[str]:
    paths = [path[1:] for path in paths] # ループに含まれるゲートのみ考える
    gates = paths_to_gates(paths)
    gates_fanout_1 = []
    for gate in gates:
        if len(c.fanout(gate)) == 1:
            gates_fanout_1.append(gate)
    return gates_fanout_1

# faninが0は含まない
def get_gates_no_mux(c, paths):
    all_gates = c.nodes()
    gates_lut = set(paths_to_gates(paths))
    gates_no_mux = []
    for gate in all_gates - gates_lut:
        if len(c.fanin(gate)) >= 1:
            gates_no_mux.append(gate)
    return gates_no_mux

def get_mux_connections(c, paths) -> list[tuple[str, str, str]]:
    mux_connections = []
    gates_no_mux = get_gates_no_mux(c, paths) # gates_no_mux の取得は変更しない
    
    # ensure gates_no_mux has enough elements for pop() later
    if len(gates_no_mux) < len(get_gates_fanout_1(c, paths)):
        print("Warning: Not enough gates in gates_no_mux for all fanout_1 gates. Adjusting list length.")
        # ここで gates_no_mux を増やすか、get_gates_fanout_1 の結果を減らすか検討
        # 簡単な方法としては、get_gates_fanout_1 の結果を gates_no_mux の数に合わせる
        # または、mux_connections を構築する際に gates_no_mux の枯渇をチェックし、スキップする

    processed_in_out_pairs = set()

    # 最初のパスの処理
    for pair_path in convert_paths_to_pair_paths(paths):
        if len(pair_path) == 0: # 空のpair_pathをスキップ
            continue
        in1 = pair_path[0][0]
        # 修正: MUXの第2入力は、gates_no_muxからランダムに選択するのではなく、
        # パスの終端ゲートのファンインを使用する意図であれば、そのように変更。
        # 現在のコードでは pair_path[-1][1] が in2 に相当しますが、これは
        # 実際には MUX の in1 と in2 のどちらになるかによって MUX のキーで制御されます。
        # ここでの in2 は、MUX のもう一方の入力に接続されるゲートを指します。
        # HCLLL の意図が MUX の片方の入力を回路の別の部分に接続することであれば、
        # `random.choice(gates_no_mux)` が適切です。
        # 今回のエラーは `out` が `not` ゲートであることなので、`out` の選定に注目します。
        out = pair_path[0][1] # out はパスの2番目のゲート
        
        # out が 'not' ゲートでないことを確認
        if c.type(out) == 'not':
            print(f"Skipping potential MUX insertion to 'not' gate: {out}")
            continue

        if (in1, out) not in processed_in_out_pairs:
            # ここでは in2 には何を接続したいのか？もしループの概念を適用するなら、
            # ループパスの異なる部分からのゲートになるはず。
            # 既存のコードでは in2 が定義されていませんが、HCLLL の元のロジックでは
            # random.choice(gates_no_mux) が使われていました。
            # 暫定的に random.choice(gates_no_mux) を使用しますが、枯渇に注意が必要です。
            if not gates_no_mux:
                print("Error: gates_no_mux is empty for first loop, cannot choose random gate for mux_connection.")
                # ここでエラーをraiseするか、空リストを返すか、適切なエラーハンドリングを行う
                # 暫定的に空リストを返してTypeErrorを回避
                return [] 
            in2_candidate = random.choice(gates_no_mux)
            
            # 修正: MUXのin2がoutのファンアウトコーンに属していないことを確認（ループ回避のため）
            if in2_candidate in c.transitive_fanin(out) or out in c.transitive_fanin(in2_candidate):
                 print(f"Skipping MUX insertion to avoid loop for ({in1}, {in2_candidate}, {out})")
                 continue

            mux_connections.append((in1, in2_candidate, out))
            processed_in_out_pairs.add((in1, out))

    # 二重切断対策のロジック: pair_gates_added を使用
    for pair_path in convert_paths_to_pair_paths(paths):
        for pair_gate in pair_path[1:]: # 最初のペア (path[0], path[1]) 以外を対象
            in1 = pair_gate[0]
            out = pair_gate[1]

            if c.type(out) == 'not': # out が 'not' ゲートならスキップ
                print(f"Skipping potential MUX insertion to 'not' gate: {out}")
                continue

            if (in1, out) not in processed_in_out_pairs:
                if not gates_no_mux:
                     print("Error: gates_no_mux is empty for second loop, cannot choose random gate for mux_connection.")
                     return [] 
                in2_candidate = random.choice(gates_no_mux)

                if in2_candidate in c.transitive_fanin(out) or out in c.transitive_fanin(in2_candidate):
                     print(f"Skipping MUX insertion to avoid loop for ({in1}, {in2_candidate}, {out})")
                     continue

                mux_connections.append((in1, in2_candidate, out))
                processed_in_out_pairs.add((in1, out))
    
    # get_gates_fanout_1 での処理
    # gates_no_mux の枯渇対策と c.fanin(out) のチェック
    gates_fanout_1_list = get_gates_fanout_1(c, paths)
    
    # pop() を使う前に gates_no_mux のサイズと必要な pop 回数を比較
    if len(gates_no_mux) < len(gates_fanout_1_list):
        print("Warning: gates_no_mux might get exhausted. Reducing gates_fanout_1_list.")
        gates_fanout_1_list = gates_fanout_1_list[:len(gates_no_mux)] # 利用可能な数に制限

    for gate_fanout_1 in gates_fanout_1_list:
        if not gates_no_mux:
            print("Error: gates_no_mux is empty for third loop, cannot pop gate for mux_connection.")
            return []
        out = gates_no_mux.pop() # pop() されているので、同じゲートは二度使われない
        
        if c.type(out) == 'not': # out が 'not' ゲートならスキップし、popしたゲートを戻さない
            print(f"Skipping potential MUX insertion to 'not' gate: {out} (from gates_no_mux.pop())")
            continue # このoutはスキップされるため、gates_no_muxからは除外されたまま

        if not c.fanin(out):
            print(f"WARNING: Gate {out} has no fanin for mux_connection. Skipping.")
            continue
        
        # in1 の選択ロジックを慎重に
        # list(c.fanin(out)).pop() は元の回路のファンインを1つ取り出すが、
        # どのファンインが選ばれるかは保証されない。
        # 目的によっては random.choice(list(c.fanin(out))) の方が良い場合も。
        in1 = list(c.fanin(out))[0] # pop() ではなくインデックスでアクセス
        in2 = gate_fanout_1
        
        if (in1, out) not in processed_in_out_pairs:
            # ループ回避チェック
            if in2 in c.transitive_fanin(out) or out in c.transitive_fanin(in2):
                 print(f"Skipping MUX insertion to avoid loop for ({in1}, {in2}, {out})")
                 continue

            mux_connections.append((in1, in2, out))
            processed_in_out_pairs.add((in1, out))
    
    return mux_connections

# 既存の回路の接続を切断 -> その間に新しいMUXを挿入して再接続
# sel = selecter. "key_prefixXXXX" の形になっている
def insert_mux(c, in1: str, in2: str, out: str, sel: str):
    m = cg.logic.mux(2)
    
    # 変更点: サブサーキット名を sel から派生させて一意にする
    # sel が既に一意のキー名であることを利用する
    mux_subcircuit_name = sel.replace("keyinput", "mux_key_") # 例: "keyinput0000" -> "mux_key_0000"
    
    # print(f"  Adding subcircuit {mux_subcircuit_name}")
    c.add_subcircuit(m, mux_subcircuit_name) # サブサーキット名を変更

    ### connect sel ###
    # print(f"  Connecting {sel} to {mux_subcircuit_name}_sel_0")
    c.connect(sel, f"{mux_subcircuit_name}_sel_0")

    ### connect in ###
    # print(f"  Disconnecting {in1} from {out}")
    c.disconnect(in1, out)
    # print(f"  Connecting {in1} to {mux_subcircuit_name}_in_0")
    c.connect(in1,f"{mux_subcircuit_name}_in_0")
    # print(f"  Connecting {in2} to {mux_subcircuit_name}_in_1")
    c.connect(in2,f"{mux_subcircuit_name}_in_1")

    ### connect out ###
    # print(f"  Connecting {mux_subcircuit_name}_out to {out}")
    c.connect(f"{mux_subcircuit_name}_out", out)
    # print(f"  insert_mux finished for {out}")

def loop_lock(
        c, num_loops, length_loops, 
        start_gates: set[str]=None, 
        end_gates:   set[str]=None, 
        lut_pair_candidates: set[str]=None, 
        key_prefix="key_"
    ) -> tuple[cg.Circuit, list[tuple[str]]]:
    paths = []
    cl = c.copy()

    if start_gates and end_gates:
        raise ValueError("Both start_gates and end_gates cannot be provided simultaneously for loop_lock.")
    # elif start_gates:
    #     paths = loop_paths_from_gates_to_outputs(c, num_loops, length_loops, start_gates)
    elif end_gates: # 既存の動作
        paths = generate_loop_paths_from_endgates(c, num_loops, length_loops, end_gates)
    else:
        raise ValueError("Either start_gates or end_gates must be provided for loop_lock.")
    
    # パスが取得できない場合のハンドリング
    if not paths:
        raise ValueError(
            f"No suitable paths found for loop locking with "
            f"num_loops={num_loops}, length_loops={length_loops}, "
            f"start_gates={start_gates}, end_gates={end_gates}"
        )

    while have_same_start_gates(paths) and len(paths) > num_loops: # 無限ループ防止のため条件追加
        paths = generate_loop_paths_from_endgates(c, num_loops, length_loops, end_gates)
        if not paths: # 再試行してもパスが見つからない場合
            raise ValueError(f"Could not find diverse enough paths for loop locking after retry.")
        if len(paths) <= num_loops:
            paths = paths[:num_loops] # 必要数に絞る

    print("\033[34m" + f"{len(paths)} loop paths:" + "\033[0m")
    print(paths)
    mux_connections = get_mux_connections(c, paths)

    for count_idx, mux_connection in enumerate(mux_connections):
        # print(f"Processing mux_connection {count_idx+1}: {mux_connection}")
        cl.add(f"{key_prefix}{count_idx:04}", "input")
        insert_mux(cl, mux_connection[0], mux_connection[1], mux_connection[2], f"{key_prefix}{count_idx:04}")
    return cl, paths

# 置換することにより保護できる出力の集合を返す
def get_affected_outputs(c, locked_gates_list: list[str]) -> set[str]:
    affected_outputs = set()
    for replaced_gate in locked_gates_list:
        if c.is_output(replaced_gate):
            affected_outputs.add(replaced_gate)
        for gate in c.transitive_fanout(replaced_gate):
            if c.is_output(gate):
                affected_outputs.add(gate)
    return affected_outputs

# 引数のゲートに影響を与えている入力の集合を返す
def get_affecting_inputs(c, locked_gates_list: list[str]) -> set[str]:
    affected_inputs = set()
    for replaced_gate in locked_gates_list:
        for gate in c.transitive_fanin(replaced_gate):
            if c.is_input(gate):
                affected_inputs.add(gate)
    return affected_inputs

######################################################
# 実際のロック処理を行う関数群
######################################################

# Fan In Fan Out Lock (FIFO Lock)
def FIFO_lock(
    c, num_gates, count_keys=False, skip_fi1=False, key_prefix="key_"
):
    """

    Parameters
    ----------
    circuit: circuitgraph.CircuitGraph
            Circuit to lock.
    num_gates: int
            The number of gates to lock.
    count_keys: bool
            If true, continue locking until at least `num_gates` keys are
            added instead of `num_gates` gates.
    skip_fi1: int
            If True, nodes with a fanin of 1 (i.e. buf or inv) will not
            be considered for locking.
    key_prefix: string
            prefix for key
    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input

    """

    cl = c.copy()
    pos = list(cl.outputs())
    # print(f"There are {len(pos)} outputs in the circuit.") # ibex_decoder については269個だった

    def calc_skew(gate, cl):
        d = {False: 0, True: 0}
        fanin = list(cl.fanin(gate))

        # create subcircuit containing just gate for simulation
        simc = cg.Circuit()
        for i in fanin:
            simc.add(i, "input")
        simc.add(gate, cl.type(gate), fanin=fanin)

        # simulate
        for i, vs in enumerate(product([False, True], repeat=len(fanin))):
            assumptions = dict(zip(fanin, vs[::-1]))
            result = cg.sat.solve(simc, assumptions)
            if not result:
                d[False] += 1
            else:
                d[result[gate]] += 1
        num_combos = 2 ** len(fanin)
        return abs(d[False] / num_combos - d[True] / num_combos)

    def continue_locking(locked_gates, num_gates, keys, count_keys):
        if count_keys:
            return len(keys) < num_gates
        return locked_gates < num_gates

    def rank_output(x):
        return len(cl.transitive_fanin(x))

    # sort pos on fanincone in descending order
    pos.sort(key=rank_output, reverse=True)

    keys = {}
    candidates = []
    forbidden_nodes = set()
    locked_gates = 0
    locked_list = []
    affected_outputs = set()

    while continue_locking(locked_gates, num_gates, keys, count_keys):
        if not candidates: # ファンインコーンを探索し終わったら次のpoを追加
            pos = [o for o in pos if o not in forbidden_nodes]
            try:
                new_po = pos.pop(0)
                candidates.append(new_po)
                affected_outputs.add(new_po)
                affected_outputs |= c.transitive_fanout(new_po)

                # add replaceable fanincone into candidates
                for gate in c.transitive_fanin(new_po): # c or cl?
                    if gate in forbidden_nodes:  # skip forbidden nodes
                        continue
                    fanout_po_list = get_affected_outputs(c, [gate])  # get all the po in fanoutcone
                    if (fanout_po_list <= affected_outputs):  # if all the po in fanoutcone are replaced
                        candidates.append(gate)

            except IndexError as e:
                raise ValueError(
                    "Ran out of candidate gates at " f"{locked_gates} gates."
                ) from e
            
        else: # ファンインコーン探索中
            candidate = candidates.pop(0)

            # skip forbidden nodes
            if candidate in forbidden_nodes:
                continue

            # skip buf/not (optional)
            if skip_fi1 and len(cl.fanin(candidate)) == 1:
                forbidden_nodes.add(candidate)
                continue

            # do the replacment
            key, nodes, output_to_relabel = replace_lut(candidate, cl, locked_gates, key_prefix)
            keys.update(key)
            cl = cg.tx.relabel(cl, {output_to_relabel: candidate})
            if c.is_output(candidate):
                cl.set_output(candidate)
            locked_gates += 1
            locked_list.append(candidate)
            forbidden_nodes.add(candidate)

        # affected_outputs = get_affected_outputs(c, locked_list)
    return cl, keys, locked_list, affected_outputs

# FIFO Lock with Loop
def FIFOL_lock(c, num_gates, num_loops, length_loops, count_keys=False, skip_fi1=False, key_prefix="key_"):

    # まずはFIFOのみ実行し、LUTに置換する論理ゲート（locked_list）を把握
    _, _, locked_list, _ = FIFO_lock(c, num_gates, count_keys, skip_fi1, key_prefix)
    # LUTに置換する場所をフィードバック起点 (end_gates) としてループを作る
    c_loop_only = loop_lock(c, num_loops, length_loops, end_gates=locked_list, key_prefix=key_prefix)
    
    cl = c_loop_only.copy()
    locked_gates = 0
    for locked_gate in locked_list:
        locked_gate_is_output = c.is_output(locked_gate)
        key, nodes, output_to_relabel = replace_lut(locked_gate, cl, locked_gates, key_prefix)
        cl = cg.tx.relabel(cl, {output_to_relabel: locked_gate})
        if locked_gate_is_output:
            cl.set_output(locked_gate)
        # print(locked_gate, locked_gates)
        # print(key)
        locked_gates += 1
    
    affected_outputs = get_affected_outputs(c, locked_list)
    return cl, c_loop_only, locked_list, affected_outputs


# 広い範囲の出力に影響を与えるように置換する High Corruptibility LUT (Loop) Lock = HC-LLL
def HCLL(
    c, num_gates, count_keys=False, skip_fi1=False, key_prefix="key_"
):
    cl = c.copy()
    pos = list(c.outputs())
    pis = list(c.inputs())
    # print(f"There are {len(pis)} inputs in the circuit.") # ibex_decoder については69個だった
    # print(f"There are {len(pos)} outputs in the circuit.") # ibex_decoder については269個だった

    def calc_skew(gate, cl):
        d = {False: 0, True: 0}
        fanin = list(cl.fanin(gate))

        # create subcircuit containing just gate for simulation
        simc = cg.Circuit()
        for i in fanin:
            simc.add(i, "input")
        simc.add(gate, cl.type(gate), fanin=fanin)

        # simulate
        for i, vs in enumerate(product([False, True], repeat=len(fanin))):
            assumptions = dict(zip(fanin, vs[::-1]))
            result = cg.sat.solve(simc, assumptions)
            if not result:
                d[False] += 1
            else:
                d[result[gate]] += 1
        num_combos = 2 ** len(fanin)
        return abs(d[False] / num_combos - d[True] / num_combos)

    def continue_locking(locked_gates, num_gates, keys, count_keys):
        if count_keys:
            return len(keys) < num_gates
        return locked_gates < num_gates

    def rank_gate_by_affected_outputs(gate):
        return len(get_affected_outputs(c, [gate]))

    # pis.sort(key=rank_gate_by_affected_outputs, reverse=True)
    keys = {}
    candidates = []
    forbidden_nodes = set()
    locked_gates = 0
    locked_list = []
    affected_outputs = set()

    # 
    # for pi in pis:
    #     for gate in c.fanout(pi):
    #         if gate in forbidden_nodes:  # skip forbidden nodes
    #             continue
    #         candidates.append(gate)
    # candidates = list(set(candidates))  # 重複を削除
    # candidates.sort(key=rank_gate_by_affected_outputs, reverse=True)
    # for pi in pis:
    #     # add replaceable fanout into candidates
    #     current_pi_fanout_gates = set()
    #     for gate in c.fanout(pi):
    #         if gate in forbidden_nodes:  # skip forbidden nodes
    #             continue
    #         current_pi_fanout_gates.add(gate)

    #     current_pi_fanout_gates = list(current_pi_fanout_gates)
    #     current_pi_fanout_gates.sort(key=rank_gate_by_affected_outputs, reverse=True)
    #     for gate in current_pi_fanout_gates:
    #         candidates.insert(0, gate)

    fanouts_of_pis = set()
    for pi in pis:
        for gate in c.fanout(pi):
            if gate in forbidden_nodes:  # skip forbidden nodes
                continue
            fanouts_of_pis.add(gate)

    fanouts_of_pis = list(fanouts_of_pis)
    fanouts_of_pis.sort(key=rank_gate_by_affected_outputs, reverse=True)
    for gate in fanouts_of_pis:
        candidates.insert(0, gate)

    while continue_locking(locked_gates, num_gates, keys, count_keys):
        if not candidates:
            raise ValueError("No more candidates to lock.")
            
        else:
            candidate = candidates.pop(0)

            # skip forbidden nodes
            if candidate in forbidden_nodes:
                continue

            # skip buf/not (optional)
            if skip_fi1 and len(cl.fanin(candidate)) == 1:
                forbidden_nodes.add(candidate)
                continue

            # do the replacment
            key, nodes, output_to_relabel = replace_lut(candidate, cl, locked_gates, key_prefix)
            keys.update(key)
            cl = cg.tx.relabel(cl, {output_to_relabel: candidate})
            locked_gates += 1
            locked_list.append(candidate)
            forbidden_nodes.add(candidate)

            # NB2: Not-Back-to-Back
            for gate in c.fanout(candidate):
                forbidden_nodes.add(gate)
            for gate in c.fanout(candidate):
                for NB2_gate in c.fanout(gate):
                    if NB2_gate not in forbidden_nodes:
                        candidates.append(NB2_gate)
                        candidates = list(set(candidates))  # 重複を削除

        affected_outputs = get_affected_outputs(c, locked_list)
    return cl, keys, locked_list, affected_outputs

def HCLLL(c, num_gates, num_loops, length_loops, count_keys=False, skip_fi1=False, key_prefix="key_"):

    # まずはHCLLを実行し、LUTに置換する論理ゲート（locked_list）を把握
    _, _, locked_list, _ = NEW_lock(c, num_gates, count_keys, skip_fi1, key_prefix)
    print("\033[34m" + f"{len(locked_list)} replaced gates:" + "\033[0m")
    print(locked_list)
    
    # LUTに置換した箇所をフィードバック起点 (start_gates) としてループを作る
    print("Creating loop-only circuit with locked gates...")
    # c_loop_only = loop_lock(c, num_loops, length_loops, lut_pair_candidates=locked_list, key_prefix=key_prefix)
    c_loop_only, loop_paths = loop_lock(c, num_loops, length_loops, end_gates=locked_list, key_prefix=key_prefix)
    print("Successfully created loop-only circuit with locked gates.")

    cl = c_loop_only.copy()
    locked_gates = 0
    for locked_gate in locked_list:
        locked_gate_is_output = c.is_output(locked_gate) # 元の回路cでの出力判定
        key, nodes, output_to_relabel = replace_lut(locked_gate, cl, locked_gates, key_prefix)
        # replace_lutの結果のキーをここで結合する
        # keys.update(key) # HCLLL関数の返り値にキーが含まれていないため、必要であればここで処理
        cl = cg.tx.relabel(cl, {output_to_relabel: locked_gate})
        if locked_gate_is_output:
            cl.set_output(locked_gate)
        locked_gates += 1
    
    affected_outputs = get_affected_outputs(c, locked_list)
    return cl, c_loop_only, locked_list, affected_outputs, loop_paths


# lut_lock + loop
def lut_loop_lock(c, num_gates, num_loops, length_loops, count_keys=False, skip_fi1=False, key_prefix="key_"):
    # まずはlut_lockのみ実行し、LUTに置換する論理ゲート（locked_list）を把握
    _, _, locked_list, _ = lut_lock(c, num_gates, count_keys, skip_fi1, key_prefix)
    
    # LUTに置換した箇所をフィードバック起点 (start_gates) としてループを作る
    c_loop_only = loop_lock(c, num_loops, length_loops, end_gates=locked_list, key_prefix=key_prefix)

    cl = c_loop_only.copy()
    locked_gates = 0
    for locked_gate in locked_list:
        locked_gate_is_output = c.is_output(locked_gate) # 元の回路cでの出力判定
        key, nodes, output_to_relabel = replace_lut(locked_gate, cl, locked_gates, key_prefix)
        cl = cg.tx.relabel(cl, {output_to_relabel: locked_gate})
        if locked_gate_is_output:
            cl.set_output(locked_gate)
        locked_gates += 1
    
    affected_outputs = get_affected_outputs(c, locked_list)
    return cl, c_loop_only, locked_list, affected_outputs

def new_lock(
    c, num_gates, count_keys=False, skip_fi1=False, key_prefix="key_"
):
    cl = c.copy()
    pis = list(cl.inputs())
    affected_outputs = set()
    # print(f"There are {len(pos)} outputs in the circuit.") # ibex_decoder については269個だった

    def continue_locking(locked_gates, num_gates, keys, count_keys):
        if count_keys:
            return len(keys) < num_gates
        return locked_gates < num_gates

    # そのゲートを置換することで新たに影響を与える出力の集合の大きさをランクとする
    def rank_gate(x):
        new_affected_outputs = get_affected_outputs(c, [x])
        new_affected_outputs -= affected_outputs
        return len(new_affected_outputs)

    keys = {}
    candidates = []
    forbidden_nodes = set()
    locked_gates = 0
    locked_list = []

    fanouts_of_pis = set()
    for pi in pis:
        for gate in c.fanout(pi):
            if gate in forbidden_nodes:  # skip forbidden nodes
                continue
            fanouts_of_pis.add(gate)

    fanouts_of_pis = list(fanouts_of_pis)
    fanouts_of_pis.sort(key=rank_gate, reverse=True)
    candidates = fanouts_of_pis.copy()
    # print(rank_gate(candidates[0]))
    # print("There are", len(candidates), "candidates to lock.")

    while continue_locking(locked_gates, num_gates, keys, count_keys):
        if not candidates:
            raise ValueError("No more candidates to lock.")
            
        else:
            candidate = candidates.pop(0)
            # print("pop後: ", rank_gate(candidate))

            # skip forbidden nodes
            if candidate in forbidden_nodes:
                for gate in c.fanout(candidate):
                    if gate not in forbidden_nodes:
                        candidates.append(gate)
                candidates = list(set(candidates))
                candidates.sort(key=rank_gate, reverse=True)
                continue

            # skip buf/not (optional)
            if skip_fi1 and len(cl.fanin(candidate)) == 1:
                forbidden_nodes.add(candidate)
                # print("\033[31m" + "skip buf/not: " + "\033[0m", candidate)
                buf_affected_outputs = get_affected_outputs(c, [candidate])
                # print(f"buf_affected_outputs: {len(buf_affected_outputs)}")
                # print(buf_affected_outputs)
                # print()
                # print("fanout: ", c.fanout(candidate))
                fanouts_affected = set()
                for gate in c.fanout(candidate):
                    # print("gate in forbidden_nodes ", gate in forbidden_nodes)
                    # print("gate in candidiates ", gate in candidates)
                    candidates.append(gate)
                    new_affected = get_affected_outputs(c, [gate])
                    # print("new_affected: ", new_affected)
                    fanouts_affected |= new_affected
                # print(f"fanouts_affected: {len(fanouts_affected)}")
                # print(fanouts_affected)
                # print(f"diff: {len(buf_affected_outputs - fanouts_affected)}")
                # print(buf_affected_outputs - fanouts_affected)
                candidates.sort(key=rank_gate, reverse=True)
                continue

            # do the replacment
            key, nodes, output_to_relabel = replace_lut(candidate, cl, locked_gates, key_prefix)
            # print("replace後: ",candidate, rank_gate(candidate))
            keys.update(key)
            cl = cg.tx.relabel(cl, {output_to_relabel: candidate})
            if c.is_output(candidate):
                cl.set_output(candidate)
            locked_gates += 1
            locked_list.append(candidate)
            forbidden_nodes.add(candidate)
            affected_outputs |= get_affected_outputs(c, [candidate])

            # NB2: Not-Back-to-Back
            for gate in c.fanout(candidate):
                forbidden_nodes.add(gate)
                for NB2_gate in c.fanout(gate):
                    if NB2_gate not in forbidden_nodes:
                        candidates.append(NB2_gate)
            candidates = list(set(candidates))
            
            candidates.sort(key=rank_gate, reverse=True)

    affected_outputs = get_affected_outputs(c, locked_list)

    unaffected_outputs = set(c.outputs()) - affected_outputs
    # print(f"Unaffected outputs: {unaffected_outputs}")
    # print(f"Number of unaffected outputs: {len(unaffected_outputs)}")
    # for output in unaffected_outputs:
    #     print("unaffected output: " + output, " fanin: ", c.transitive_fanin(output))
        
    return cl, keys, locked_list, affected_outputs

def count_candidates(c):
    candidates_from_pis = set()
    candidates_from_pis_fi1 = set()
    po_from_pis = set()
    pis = list(c.inputs())
    for pi in pis:
        for gate in c.transitive_fanout(pi):
            candidates_from_pis.add(gate)
            if len(c.fanin(gate)) == 1:  # if fanin is 1, add to candidates_fi1
                candidates_from_pis_fi1.add(gate)
            if c.is_output(gate):
                po_from_pis.add(gate)
    print("=== Search from inputs ===")
    print(f"There are {len(pis)} inputs in the circuit.")
    print(f"There are {len(candidates_from_pis)} candidates in the circuit.")
    print(f"There are {len(candidates_from_pis_fi1)} candidates with fanin 1 in the circuit.")
    print(f"There are {len(po_from_pis)} outputs from inputs in the circuit.")

    candidates_from_pos = set()
    candidates_from_pos_fi1 = set()
    pi_from_pos = set()
    pos = list(c.outputs())
    for po in pos:
        for gate in c.transitive_fanin(po):
            candidates_from_pos.add(gate)
            if len(c.fanin(gate)) == 1:  # if fanin is 1, add to candidates_fi1
                candidates_from_pos_fi1.add(gate)
            if gate in pis:
                pi_from_pos.add(gate)
    print("=== Search from outputs ===")
    print(f"There are {len(pos)} outputs in the circuit.")
    print(f"There are {len(candidates_from_pos)} candidates in the circuit.")
    print(f"There are {len(candidates_from_pos_fi1)} candidates with fanin 1 in the circuit.")
    print(f"There are {len(pi_from_pos)} inputs from outputs in the circuit.")

    candidates_all = candidates_from_pis | candidates_from_pos
    candidates_all_fi1 = candidates_from_pis_fi1 | candidates_from_pos_fi1
    print("=== Combined candidates ===")
    print(f"There are {len(candidates_all)} candidates in the circuit.")
    print(f"There are {len(candidates_all_fi1)} candidates with fanin 1 in the circuit.")

def NEW_lock(
    c, num_gates, count_keys=False, skip_fi1=False, key_prefix="key_"
):
    cl = c.copy()
    pos = list(cl.outputs())
    pis = list(cl.inputs())
    affected_outputs = set()
    # print(f"There are {len(pos)} outputs in the circuit.") # ibex_decoder については269個だった

    def calc_skew(gate, cl):
        d = {False: 0, True: 0}
        fanin = list(cl.fanin(gate))

        # create subcircuit containing just gate for simulation
        simc = cg.Circuit()
        for i in fanin:
            simc.add(i, "input")
        simc.add(gate, cl.type(gate), fanin=fanin)

        # simulate
        for i, vs in enumerate(product([False, True], repeat=len(fanin))):
            assumptions = dict(zip(fanin, vs[::-1]))
            result = cg.sat.solve(simc, assumptions)
            if not result:
                d[False] += 1
            else:
                d[result[gate]] += 1
        num_combos = 2 ** len(fanin)
        return abs(d[False] / num_combos - d[True] / num_combos)

    def continue_locking(locked_gates, num_gates, keys, count_keys):
        if count_keys:
            return len(keys) < num_gates
        return locked_gates < num_gates

    # そのゲートを置換することで新たに影響を与える出力の集合の大きさをランクとする
    def rank_gate(x):
        new_affected_outputs = get_affected_outputs(c, [x])
        new_affected_outputs -= affected_outputs
        skew = calc_skew(x, cl)
        return len(new_affected_outputs) + skew

    keys = {}
    candidates = []
    forbidden_nodes = c.inputs()
    locked_gates = 0
    locked_list = []

    pos.sort(key=rank_gate, reverse=True)
    candidates = pos.copy()
    # print(rank_gate(candidates[0]))
    # print("There are", len(candidates), "candidates to lock.")

    while continue_locking(locked_gates, num_gates, keys, count_keys):
        if not candidates:
            raise ValueError("No more candidates to lock.")
            
        else:
            candidate = candidates.pop(0)
            # print("pop後: ", rank_gate(candidate))

            # skip forbidden nodes
            if candidate in forbidden_nodes:
                for gate in c.fanin(candidate):
                    if gate not in forbidden_nodes:
                        candidates.append(gate)
                for gate in c.fanout(candidate):
                    if gate not in forbidden_nodes:
                        candidates.append(gate)
                candidates = list(set(candidates))
                candidates.sort(key=rank_gate, reverse=True)
                continue

            # skip buf/not (optional)
            if skip_fi1 and len(cl.fanin(candidate)) == 1:
                forbidden_nodes.add(candidate)
                for gate in c.fanin(candidate):
                    if gate not in forbidden_nodes:
                        candidates.append(gate)
                for gate in c.fanout(candidate):
                    if gate not in forbidden_nodes:
                        candidates.append(gate)
                candidates = list(set(candidates))
                candidates.sort(key=rank_gate, reverse=True)
                continue

            # do the replacment
            key, nodes, output_to_relabel = replace_lut(candidate, cl, locked_gates, key_prefix)
            # print("replace後: ",candidate, rank_gate(candidate))
            keys.update(key)
            cl = cg.tx.relabel(cl, {output_to_relabel: candidate})
            if c.is_output(candidate):
                cl.set_output(candidate)
            locked_gates += 1
            locked_list.append(candidate)
            forbidden_nodes.add(candidate)
            affected_outputs |= get_affected_outputs(c, [candidate])

            # NB2: Not-Back-to-Back
            for gate in c.fanout(candidate):
                forbidden_nodes.add(gate)
                for NB2_gate in c.fanout(gate):
                    if NB2_gate not in forbidden_nodes:
                        candidates.append(NB2_gate)
            # for gate in c.fanin(candidate):
            #     candidates.append(gate)
            #     forbidden_nodes.add(gate)
            #     for NB2_gate in c.fanout(gate):
            #         if NB2_gate not in forbidden_nodes:
            #             candidates.append(NB2_gate)

            candidates = list(set(candidates))
            
            candidates.sort(key=rank_gate, reverse=True)

    affected_outputs = get_affected_outputs(c, locked_list)

    unaffected_outputs = set(c.outputs()) - affected_outputs
    # print(f"Unaffected outputs: {unaffected_outputs}")
    # print(f"Number of unaffected outputs: {len(unaffected_outputs)}")
    # for output in unaffected_outputs:
    #     print("unaffected output: " + output, " fanin: ", c.transitive_fanin(output))
        
    return cl, keys, locked_list, affected_outputs

#######################################################
########## 研究のために追加したコードはここまで ##########
#######################################################


def trll(c, keylen, s1_s2_ratio=1, shuffle_key=True, seed=None):
    """Locks a circuitgraph with Truly Random Logic Locking.

    Limaye, E. Kalligeros, N. Karousos, I. G. Karybali and O. Sinanoglu,
    "Thwarting All Logic Locking Attacks: Dishonest Oracle With Truly Random
    Logic Locking," in IEEE Transactions on Computer-Aided Design of Integrated
    Circuits and Systems, vol. 40, no. 9, pp. 1740-1753, Sept. 2021.

    Parameters
    ----------
    c: circuitgraph.Circuit
            The circuit to lock.
    keylen: int
            The number of key bits to add.
    s1_s2_ratio: int or str
            The ratio between number of key gate locations locked where an
            inverter exists in the original design (s1) or where an inverter
            does not exist in the original design (s2). The paper leaves this
            value at 1 (meaning s1=s2=keylen/2), but they note that this
            could be adjusted based on the ratio of the locations where there
            is an inverter in the original netlist. Setting this parameter
            to the string "infer" will do this adjustment. I.e.
            s1 = keylen*r, s2 = keylen*(1-r), where r is the number of
            inverters in the circuit divided by the total number of gates.
    shuffle_key: bool
            By default, the key input labels are shuffled at the end of the
            algorithm so the labelling does not reveal which portion of the
            algorithm the key input was added during.
    seed: int
            Seed for the random selection of gates and shuffling of the key.

    Returns
    -------
    circuitgraph.Circuit, dict of str:bool
            The locked circuit and the correct key value for each key input.
    """
    rng = random.Random(seed)

    cl = c.copy()

    if keylen % 2 != 0:
        raise NotImplementedError
    if s1_s2_ratio == "infer":
        raise NotImplementedError

    s1 = int((keylen // 2) * s1_s2_ratio)
    if s1 > keylen:
        raise ValueError(f"Unusable s1_s2_ratio: {s1_s2_ratio}")
    s2 = keylen - s1

    s1a = rng.randint(0, s1)
    s1b = s1 - s1a

    s2a = rng.randint(0, s2)
    s2b = s2 - s2a

    inv_gates = list(c.filter_type("not"))
    rng.shuffle(inv_gates)
    rem_gates = list(
        c.nodes()
        - c.io()
        - c.filter_type(("not", "bb_input", "bb_output", "0", "1", "x"))
    )
    rng.shuffle(rem_gates)

    j = 0
    k = {}
    # Replace existing inv_gates with XOR key-gates
    for _ in range(s1a):
        sel_gate = inv_gates.pop()
        ki = f"key_{j}"
        cl.add(ki, "input")
        k[ki] = True
        cl.set_type(sel_gate, "xor")
        cl.connect(ki, sel_gate)
        j += 1

    # Add XOR key-gates before existing inv_gates
    for _ in range(s1b):
        sel_gate = inv_gates.pop()
        ki = f"key_{j}"
        cl.add(ki, "input")
        k[ki] = False
        inv_fanin = cl.fanin(sel_gate)
        assert len(inv_fanin) == 1
        cl.disconnect(inv_fanin, sel_gate)
        cl.add(f"key_gate_{j}", "xor", fanin=inv_fanin | {ki}, fanout=sel_gate)
        j += 1

    # Add XOR key-gates and INV gates after existing rem_gates
    for _ in range(s2a):
        sel_gate = rem_gates.pop()
        ki = f"key_{j}"
        cl.add(ki, "input")
        k[ki] = True
        sel_fanout = cl.fanout(sel_gate)
        cl.disconnect(sel_gate, sel_fanout)
        cl.add(f"key_gate_{j}", "xor", fanin=(sel_gate, ki))
        cl.add(f"key_inv_{j}", "not", fanin=f"key_gate_{j}", fanout=sel_fanout)
        j += 1

    # Add XOR key-gates after existing rem_gates
    for _ in range(s2b):
        sel_gate = rem_gates.pop()
        ki = f"key_{j}"
        cl.add(ki, "input")
        k[ki] = False
        sel_fanout = cl.fanout(sel_gate)
        cl.disconnect(sel_gate, sel_fanout)
        cl.add(f"key_gate_{j}", "xor", fanin=(sel_gate, ki), fanout=sel_fanout)
        j += 1

    # Shuffle keys
    if shuffle_key:
        new_order = list(range(keylen))
        rng.shuffle(new_order)
        shuffled_k = {}
        intermediate_mapping = {}
        final_mapping = {}
        for old_idx, new_idx in enumerate(new_order):
            shuffled_k[f"key_{new_idx}"] = k[f"key_{old_idx}"]
            intermediate_mapping[f"key_{old_idx}"] = f"key_{old_idx}_temp"
            final_mapping[f"key_{old_idx}_temp"] = f"key_{new_idx}"
        cl.relabel(intermediate_mapping)
        cl.relabel(final_mapping)
        return cl, shuffled_k
    return cl, k


def xor_lock(c, keylen, key_prefix="key_", replacement=False):
    """Locks a circuitgraph with a random xor lock.

    J. A. Roy, F. Koushanfar and I. L. Markov, "Ending Piracy of Integrated
    Circuits," in Computer, vol. 43, no. 10, pp. 30-38, Oct. 2010.

    Parameters
    ----------
    c: circuitgraph.CircuitGraph
            Circuit to lock.
    keylen: int
            the number of bits in the key
    replacement: bool
            If True, the same line can be locked twice (resulting in a chain
            of key gates)

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # create copy to lock
    cl = c.copy()

    # randomly select gates to lock
    if replacement:
        gates = choices(tuple(cl.nodes() - cl.outputs()), k=keylen)
    else:
        gates = sample(tuple(cl.nodes() - cl.outputs()), keylen)

    # insert key gates
    key = {}
    for i, gate in enumerate(gates):
        # select random key value
        key[f"{key_prefix}{i}"] = choice([True, False])

        # create xor/xnor,input
        gate_type = "xnor" if key[f"{key_prefix}{i}"] else "xor"
        fanout = cl.fanout(gate)
        cl.disconnect(gate, fanout)
        cl.add(f"key_gate_{i}", gate_type, fanin=gate, fanout=fanout)
        cl.add(f"{key_prefix}{i}", "input", fanout=f"key_gate_{i}")

    cg.lint(cl)
    return cl, key


def mux_lock(c, keylen, avoid_loops=False, key_prefix="key_"):
    """Locks a circuitgraph with a mux lock.

    J. Rajendran et al., "Fault Analysis-Based Logic Encryption," in IEEE
    Transactions on Computers, vol. 64, no. 2, pp. 410-424, Feb. 2015,
    doi: 10.1109/TC.2013.193.

    Note that a random mux selection is used, not fault-based.

    Parameters
    ----------
    c: circuitgraph.CircuitGraph
            Circuit to lock.
    keylen: int
            the number of bits in the key.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # create copy to lock
    cl = c.copy()

    # get 2:1 mux
    m = cg.logic.mux(2)

    # randomly select gates
    gates = sample(tuple(cl.nodes() - cl.outputs()), keylen)
    if avoid_loops:
        decoy_gates = set()
    else:
        decoy_gates = sample(tuple(cl.nodes() - cl.outputs()), keylen)

    # insert key gates
    key = {}
    for i, gate in enumerate(gates):
        # select random key value
        key_val = choice([True, False])

        if avoid_loops:
            decoy_gate = choice(
                tuple(
                    c.nodes()
                    - c.io()
                    - set(gates)
                    - cl.transitive_fanout(gate)
                    - decoy_gates
                )
            )
            decoy_gates.add(decoy_gate)
        else:
            decoy_gate = decoy_gates[i]

        # create and connect mux
        fanout = cl.fanout(gate)
        cl.disconnect(gate, fanout)
        cl.add_subcircuit(m, f"mux_{i}")
        cl.connect(f"mux_{i}_out", fanout)
        key_in = cl.add(f"{key_prefix}{i}", "input", fanout=f"mux_{i}_sel_0", uid=True)
        key[key_in] = key_val
        if key_val:
            cl.connect(gate, f"mux_{i}_in_1")
            cl.connect(decoy_gate, f"mux_{i}_in_0")
        else:
            cl.connect(gate, f"mux_{i}_in_0")
            cl.connect(decoy_gate, f"mux_{i}_in_1")

    cg.lint(cl)
    if avoid_loops and cl.is_cyclic():
        raise ValueError("Locked circuit is cyclic")
    return cl, key


def random_lut_lock(c, num_gates, lut_width, gates=None):
    """Locks a circuitgraph by replacing random gates with LUTs.

    This is kind of like applying LUT-lock with no replacement strategy.
    (H. Mardani Kamali, K. Zamiri Azar, K. Gaj, H. Homayoun and A. Sasan,
    "LUT-Lock: A Novel LUT-Based Logic Obfuscation for FPGA-Bitstream and
    ASIC-Hardware Protection," 2018 IEEE Computer Society Annual Symposium on
    VLSI (ISVLSI), Hong Kong, 2018, pp. 405-410.)

    Parameters
    ----------
    circuit: circuitgraph.CircuitGraph
            Circuit to lock.
    num_gates: int
            the number of gates to lock.
    lut_width: int
            LUT width, defines maximum fanin of locked gates.
    gates: list of str
            The gates to lock. If not provided, will be randomly sampled

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # create copy to lock
    cl = c.copy()

    # parse mux
    m = cg.logic.mux(2**lut_width)

    # randomly select gates
    potential_gates = {g for g in cl.nodes() - cl.io() if len(cl.fanin(g)) <= lut_width}
    if gates:
        if len(gates) != num_gates:
            raise ValueError(
                f"Got 'num_gates' of {num_gates} but length of "
                f"'gates' is {len(gates)}"
            )
        if any(len(cl.fanin(g)) > lut_width for g in gates):
            raise ValueError("cannot lock a gate with fanin greater than " "lut_width")
        if any(g in cl.io() for g in gates):
            raise ValueError("cannot lock an input/output gate")
    else:
        gates = sample(tuple(potential_gates), num_gates)
    potential_gates -= set(gates)
    potential_gates -= cl.transitive_fanout(gates)

    # insert key gates
    key = {}
    for i, gate in enumerate(gates):
        fanout = list(cl.fanout(gate))
        fanin = list(cl.fanin(gate))
        try:
            padding = sample(
                tuple(potential_gates - cl.fanin(gate)), lut_width - len(fanin)
            )
        except ValueError as e:
            raise ValueError("Could not find enough viable gates for padding") from e

        # create LUT
        cl.add_subcircuit(m, f"lut_{i}")

        # connect keys
        for j, vs in enumerate(product([False, True], repeat=len(fanin + padding))):
            assumptions = {
                s: v for s, v in zip(fanin + padding, vs[::-1]) if s in fanin
            }
            key_in = cl.add(
                f"key_{i*2**lut_width+j}", "input", fanout=f"lut_{i}_in_{j}", uid=True
            )
            result = cg.sat.solve(c, assumptions)
            if not result:
                key[key_in] = False
            else:
                key[key_in] = result[gate]

        # connect out
        cl.disconnect(gate, fanout)
        cl.connect(f"lut_{i}_out", fanout)

        # connect sel
        for j, f in enumerate(fanin + padding):
            cl.connect(f, f"lut_{i}_sel_{j}")

        # delete gate
        cl.remove(gate)
        cl = cg.tx.relabel(cl, {f"lut_{i}_out": gate})

    cg.lint(cl)
    return cl, key


def lut_lock(
    c,
    num_gates,
    count_keys=False,
    skip_fi1=True,
    rank_by_shared_fanin=False,
    key_prefix="key_",
):
    """Locks a circuitgraph with NB2-MO-HSC LUT-lock.

    H. Mardani Kamali, K. Zamiri Azar, K. Gaj, H. Homayoun and A. Sasan,
    "LUT-Lock: A Novel LUT-Based Logic Obfuscation for FPGA-Bitstream and
    ASIC-Hardware Protection," 2018 IEEE Computer Society Annual Symposium on
    VLSI (ISVLSI), Hong Kong, 2018, pp. 405-410.

    Parameters
    ----------
    circuit: circuitgraph.CircuitGraph
            Circuit to lock.
    num_gates: int
            The number of gates to lock.
    count_keys: bool
            If true, continue locking until at least `num_gates` keys are
            added instead of `num_gates` gates.
    skip_fi1: int
            If True, nodes with a fanin of 1 (i.e. buf or inv) will not
            be considered for locking.
    rank_by_shared_fanin: bool
            If True, the output with the least shared fanin with other outputs
            will be selected for locking first. By default, the output with
            the least amount of total fanin is selected for locking first.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input

    Raises
    ------
    ValueError
            if there are not enough viable gates to lock.
    """
    # create copy to lock
    cl = c.copy()

    def calc_skew(gate, cl):
        d = {False: 0, True: 0}
        fanin = list(cl.fanin(gate))

        # create subcircuit containing just gate for simulation
        simc = cg.Circuit()
        for i in fanin:
            simc.add(i, "input")
        simc.add(gate, cl.type(gate), fanin=fanin)

        # simulate
        for i, vs in enumerate(product([False, True], repeat=len(fanin))):
            assumptions = dict(zip(fanin, vs[::-1]))
            result = cg.sat.solve(simc, assumptions)
            if not result:
                d[False] += 1
            else:
                d[result[gate]] += 1
        num_combos = 2 ** len(fanin)
        return abs(d[False] / num_combos - d[True] / num_combos)

    def replace_lut(gate, cl):
        key = {}
        m = cg.logic.mux(2 ** len(cl.fanin(gate)))
        fanout = list(cl.fanout(gate))
        fanin = list(cl.fanin(gate))

        # create LUT
        cl.add_subcircuit(m, f"lut_{gate}")

        # create subcircuit containing just gate for simulation
        simc = cg.Circuit()
        for i in fanin:
            simc.add(i, "input")
        simc.add(gate, cl.type(gate), fanin=fanin)

        # connect keys
        for i, vs in enumerate(product([False, True], repeat=len(fanin))):
            assumptions = dict(zip(fanin, vs[::-1]))
            cl.add(
                f"{key_prefix}{locked_gates:04}{i:02}",
                "input",
                fanout = f"lut_{gate}_in_{i}",
            )
            result = cg.sat.solve(simc, assumptions)
            if not result:
                key[f"{key_prefix}{locked_gates:04}{i:02}"] = False
            else:
                key[f"{key_prefix}{locked_gates:04}{i:02}"] = result[gate]

        # connect out
        cl.disconnect(gate, fanout)
        cl.connect(f"lut_{gate}_out", fanout)

        # connect sel
        for i, f in enumerate(fanin):
            cl.connect(f, f"lut_{gate}_sel_{i}")

        # delete gate
        cl.remove(gate)
        return key, [f"lut_{gate}_{n}" for n in m.nodes()], f"lut_{gate}_out"

    def continue_locking(locked_gates, num_gates, keys, count_keys):
        if count_keys:
            return len(keys) < num_gates
        return locked_gates < num_gates

    locked_gates = 0
    outputs = list(cl.outputs())
    if rank_by_shared_fanin:

        def rank_output(x):
            other_outputs = [o for o in outputs if o != x]
            other_fanin = cl.transitive_fanin(other_outputs)
            curr_fanin = cl.transitive_fanin(x)
            return len(curr_fanin & other_fanin)

    else:

        def rank_output(x):
            return len(cl.transitive_fanin(x))

    outputs.sort(key=rank_output)
    candidates = []
    forbidden_nodes = set()
    keys = {}
    locked_list = []

    while continue_locking(locked_gates, num_gates, keys, count_keys):
        if not candidates:
            outputs = [o for o in outputs if o not in forbidden_nodes]
            try:
                candidates.append(outputs.pop(0))
            except IndexError as e:
                raise ValueError(
                    "Ran out of candidate gates at " f"{locked_gates} gates."
                ) from e
        else:
            candidate = candidates.pop(0)
            candidate_is_output = cl.is_output(candidate)
            children = cl.fanin(candidate)
            if candidate in forbidden_nodes:
                candidates += [g for g in children if g not in forbidden_nodes]
                continue
            forbidden_nodes.add(candidate)
            if len(children) == 0:
                continue
            if skip_fi1 and len(children) == 1:
                child = children.pop()
                if child not in forbidden_nodes | set(candidates):
                    candidates.insert(0, child)
                continue
            key, nodes, output_to_relabel = replace_lut(candidate, cl)
            locked_list.append(candidate)
            keys.update(key)
            forbidden_nodes.update(nodes)
            cl = cg.tx.relabel(cl, {output_to_relabel: candidate})
            if candidate_is_output:
                cl.set_output(candidate)
            for g1 in children:
                forbidden_nodes.add(g1)
                for g2 in cl.fanin(g1):
                    if g2 not in forbidden_nodes | set(candidates):
                        candidates.append(g2)
            # Sort by least number of outputs in fanout cone, then most skew
            candidates.sort(
                key=lambda x: (
                    len(cl.transitive_fanout(x) & cl.outputs()),
                    -calc_skew(x, cl),
                )
            )
            locked_gates += 1

    affected_outputs = get_affected_outputs(c, locked_list)
    return cl, keys, locked_list, affected_outputs


def tt_lock(c, width, target_output=None):
    """Locks a circuitgraph with TTLock.

    Note that in this implementation the original circuit is not
    functionally stripped, meaning that it does not produce an inverted
    response for the protected input pattern. This makes this implementation
    vulnerable to removal attacks. However, it can still be used to measure
    SAT attack resilience.

    M. Yasin, A. Sengupta, B. Schafer, Y. Makris, O. Sinanoglu, and
    J. Rajendran, “What to Lock?: Functional and Parametric Locking,”
    in Great Lakes Symposium on VLSI, pp. 351–356, 2017.

    Parameters
    ----------
    c: circuitgraph.CircuitGraph
            Circuit to lock.
    width: int
            the minimum fanin of the gates to lock.
    target_output: str
            If defined, this output will be the one which is locked.
            Otherwise, a random output will be locked.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # create copy to lock
    cl = c.copy()

    if len(c.inputs()) < width:
        raise ValueError(f"Not enough inputs to lock with width '{width}'")

    if not target_output:
        target_output = random.choice(list(cl.outputs()))

    # get inputs to lock
    target_inputs = cl.startpoints(target_output)
    if len(target_inputs) < width:
        target_inputs |= set(
            random.sample(list(cl.inputs() - target_inputs), width - len(target_inputs))
        )
    target_inputs = list(target_inputs)

    # create key
    key = {f"key_{i}": random.choice([True, False]) for i in range(width)}

    # connect comparators
    cl.add("flip_out", "and")
    cl.add("restore_out", "and")
    for i, inp in enumerate(random.sample(target_inputs, width)):
        cl.add(f"key_{i}", "input")
        cl.add(f"hardcoded_key_{i}", "1" if key[f"key_{i}"] else "0")
        cl.add(f"restore_xor_{i}", "xor", fanin=[f"key_{i}", inp], fanout="restore_out")
        cl.add(
            f"flip_xor_{i}", "xor", fanin=[f"hardcoded_key_{i}", inp], fanout="flip_out"
        )

    # flip output
    old_out = cl.uid(f"{target_output}_pre_lock")
    cl = cg.tx.relabel(cl, {target_output: old_out})
    cl.set_output(old_out, False)
    cl.add(
        target_output, "xor", fanin=[old_out, "restore_out", "flip_out"], output=True
    )

    cg.lint(cl)
    return cl, key


def tt_lock_sen(c, width, nsamples=10):
    """Locks a circuitgraph with TTLock-Sen.

    Joseph Sweeney, Marijn J.H. Heule, and Lawrence Pileggi,
    “Sensitivity Analysis of Locked Circuits,” in
    Logic for Programming, Artificial Intelligence and Reasoning
    (LPAR-23), pp. 483-497. EPiC Series in Computing 73, EasyChair.

    Parameters
    ----------
    c: circuitgraph.CircuitGraph
            Circuit to lock.
    width: int
            the minimum fanin of the gates to lock.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # create copy to lock
    cl = c.copy()

    # find output with large enough fanin
    potential_outs = [o for o in cl.outputs() if len(cl.startpoints(o)) >= width]
    if not potential_outs:
        raise ValueError(f"Not enough inputs to lock with width '{width}'")

    # find average sensitivities
    A = {}
    N = {}
    S = {}
    for o in potential_outs:
        # build sensitivity circuit
        s = cg.tx.sensitivity_transform(c, o)
        startpoints = c.startpoints(o)
        s_out = {o for o in s.outputs() if "difference" in o}

        # est avg sensitivity
        total = 0
        for i in range(nsamples):
            input_val = {i: randint(0, 1) for i in startpoints}
            model = cg.sat.solve(s, input_val)
            sen = sum(model[o] for o in s_out)
            total += sen
        A[o] = int(total / nsamples)
        N[o] = len(startpoints)
        S[o] = s

    # find output + input value with closest to avg sen
    def find_input():
        b = 0
        while b < max(N.values()):
            for o in potential_outs:
                upper = min(N[o], int(N[o] - A[o] + b))
                lower = max(0, int(N[o] - A[o] - b))
                us = cg.utils.int_to_bin(upper, cg.utils.clog2(N[o]))
                ls = cg.utils.int_to_bin(lower, cg.utils.clog2(N[o]))
                for sv in [us, ls]:
                    model = cg.sat.solve(
                        S[o], {f"sen_out_{i}": v for i, v in enumerate(sv)}
                    )
                    if model:
                        out = o
                        startpoints = c.startpoints(o)

                        key = {f"key_{i}": model[n] for i, n in enumerate(startpoints)}
                        return key, startpoints, out
            b += 1

    key, startpoints, out = find_input()

    # connect comparators
    cl.add("flip_out", "and")
    cl.add("restore_out", "and")
    for i, inp in enumerate(startpoints):
        cl.add(f"key_{i}", "input")
        cl.add(f"hardcoded_key_{i}", "1" if key[f"key_{i}"] else "0")
        cl.add(f"restore_xor_{i}", "xor", fanin=[f"key_{i}", inp], fanout="restore_out")
        cl.add(
            f"flip_xor_{i}", "xor", fanin=[f"hardcoded_key_{i}", inp], fanout="flip_out"
        )

    # flip output
    old_out = cl.uid(f"{out}_pre_lock")
    cl = cg.tx.relabel(cl, {out: old_out})
    cl.set_output(old_out, False)
    cl.add(out, "xor", fanin=[old_out, "restore_out", "flip_out"], output=True)

    cg.lint(cl)
    return cl, key


def sfll_hd(c, width, hd, target_output=None):
    """Locks a circuitgraph with SFLL-HD.

    Note that in this implementation the original circuit is not
    functionally stripped, meaning that it does not produce an inverted
    response for the protected input pattern. This makes this implementation
    vulnerable to removal attacks. However, it can still be used to measure
    SAT attack resilience.

    Muhammad Yasin, Abhrajit Sengupta, Mohammed Thari Nabeel, Mohammed Ashraf,
    Jeyavijayan (JV) Rajendran, and Ozgur Sinanoglu. 2017. Provably-Secure
    Logic Locking: From Theory To Practice. In Proceedings of the 2017 ACM
    SIGSAC Conference on Computer and Communications Security (CCS ’17).
    Association for Computing Machinery, New York, NY, USA, 1601–1618.

    Parameters
    ----------
    c: circuitgraph.CircuitGraph
            Circuit to lock.
    width: int
            key width, also the minimum fanin of the gates to lock.
    hd: int
            the hamming distance to lock with, as explained in the paper.
    target_output: str
            If defined, this output will be the one which is locked.
            Otherwise, a random output will be locked.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # create copy to lock
    cl = c.copy()

    # parse popcount
    p = cg.logic.popcount(width)

    if len(c.inputs()) < width:
        raise ValueError(f"Not enough inputs to lock with width '{width}'")

    if not target_output:
        target_output = random.choice(list(cl.outputs()))

    # get inputs to lock
    target_inputs = cl.startpoints(target_output)
    if len(target_inputs) < width:
        target_inputs |= set(
            random.sample(list(cl.inputs() - target_inputs), width - len(target_inputs))
        )
    target_inputs = list(target_inputs)

    # create key
    key = {f"key_{i}": random.choice([True, False]) for i in range(width)}

    # instantiate and connect hd circuits
    cl.add_subcircuit(p, "flip_pop")
    cl.add_subcircuit(p, "restore_pop")

    # connect inputs
    for i, inp in enumerate(random.sample(target_inputs, width)):
        cl.add(f"key_{i}", "input")
        cl.add(f"hardcoded_key_{i}", "1" if key[f"key_{i}"] else "0")
        cl.add(f"restore_xor_{i}", "xor", fanin=[f"key_{i}", inp])
        cl.add(f"flip_xor_{i}", "xor", fanin=[f"hardcoded_key_{i}", inp])
        cl.connect(f"flip_xor_{i}", f"flip_pop_in_{i}")
        cl.connect(f"restore_xor_{i}", f"restore_pop_in_{i}")

    # connect outputs
    cl.add("flip_out", "and")
    cl.add("restore_out", "and")
    for i, v in enumerate(format(hd, f"0{cg.utils.clog2(width)+1}b")[::-1]):
        cl.add(f"hd_{i}", v)
        cl.add(
            f"restore_out_xnor_{i}",
            "xnor",
            fanin=[f"hd_{i}", f"restore_pop_out_{i}"],
            fanout="restore_out",
        )
        cl.add(
            f"flip_out_xnor_{i}",
            "xnor",
            fanin=[f"hd_{i}", f"flip_pop_out_{i}"],
            fanout="flip_out",
        )

    # flip output
    old_out = cl.uid(f"{target_output}_pre_lock")
    cl = cg.tx.relabel(cl, {target_output: old_out})
    cl.set_output(old_out, False)
    cl.add(
        target_output, "xor", fanin=[old_out, "restore_out", "flip_out"], output=True
    )

    cg.lint(cl)
    return cl, key


def sfll_flex(c, width, n, target_output=None):
    """Locks a circuitgraph with SFLL-flex.

    Note that in this implementation the original circuit is not
    functionally stripped, meaning that it does not produce an inverted
    response for the protected input pattern. This makes this implementation
    vulnerable to removal attacks. However, it can still be used to measure
    SAT attack resilience.

    Muhammad Yasin, Abhrajit Sengupta, Mohammed Thari Nabeel,
    Mohammed Ashraf, Jeyavijayan (JV) Rajendran, and Ozgur Sinanoglu. 2017.
    Provably-Secure Logic Locking: From Theory To Practice. In Proceedings of
    the 2017 ACM SIGSAC Conference on Computer and Communications Security.
    Association for Computing Machinery, New York, NY, USA, 1601–1618.

    Parameters
    ----------
    c: circuitgraph.CircuitGraph
            Circuit to lock.
    width: int
            the minimum fanin of the gates to lock.
    n: int
            number of input patterns to lock.
    target_output: str
            If defined, this output will be the one which is locked.
            Otherwise, a random output will be locked.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # create copy to lock
    cl = c.copy()

    if not target_output:
        target_output = random.choice(list(cl.outputs()))

    # get inputs to lock
    target_inputs = cl.startpoints(target_output)
    if len(target_inputs) < width:
        target_inputs |= set(
            random.sample(list(cl.inputs() - target_inputs), width - len(target_inputs))
        )
    target_inputs = list(target_inputs)

    # create key
    key = {f"key_{i}": choice([True, False]) for i in range(width * n)}

    # connect comparators
    cl.add("flip_out", "or")
    cl.add("restore_out", "or")

    for j in range(n):
        cl.add(f"flip_and_{j}", "and", fanout="flip_out")
        cl.add(f"restore_and_{j}", "and", fanout="restore_out")

    for i, inp in enumerate(random.sample(target_inputs, width)):
        for j in range(n):
            cl.add(f"key_{i+j*width}", "input")
            cl.add(f"hardcoded_key_{i}_{j}", "1" if key[f"key_{i+j*width}"] else "0")
            cl.add(
                f"restore_xor_{i}_{j}",
                "xor",
                fanin=[f"key_{i+j*width}", inp],
                fanout=f"restore_and_{j}",
            )
            cl.add(
                f"flip_xor_{i}_{j}",
                "xor",
                fanin=[f"hardcoded_key_{i}_{j}", inp],
                fanout=f"flip_and_{j}",
            )

    # flip output
    old_out = cl.uid(f"{target_output}_pre_lock")
    cl = cg.tx.relabel(cl, {target_output: old_out})
    cl.set_output(old_out, False)
    cl.add(
        target_output, "xor", fanin=[old_out, "restore_out", "flip_out"], output=True
    )

    cg.lint(cl)
    return cl, key


def _connect_banyan(cl, swb_ins, swb_outs, bw):
    I = int(2 * cg.utils.clog2(bw) - 2)
    J = int(bw / 2)
    for i in range(cg.utils.clog2(J)):
        r = J / (2**i)
        for j in range(J):
            t = (j % r) >= (r / 2)
            # straight
            out_i = int((i * bw) + (2 * j) + t)
            in_i = int((i * bw + bw) + (2 * j) + t)
            cl.connect(swb_outs[out_i], swb_ins[in_i])

            # cross
            out_i = int((i * bw) + (2 * j) + (1 - t) + ((r - 1) * ((1 - t) * 2 - 1)))
            in_i = int((i * bw + bw) + (2 * j) + (1 - t))
            cl.connect(swb_outs[out_i], swb_ins[in_i])

            if r > 2:
                # straight
                out_i = int(((I * J * 2) - ((2 + i) * bw)) + (2 * j) + t)
                in_i = int(((I * J * 2) - ((1 + i) * bw)) + (2 * j) + t)
                cl.connect(swb_outs[out_i], swb_ins[in_i])

                # cross
                out_i = int(
                    ((I * J * 2) - ((2 + i) * bw))
                    + (2 * j)
                    + (1 - t)
                    + ((r - 1) * ((1 - t) * 2 - 1))
                )
                in_i = int(((I * J * 2) - ((1 + i) * bw)) + (2 * j) + (1 - t))
                cl.connect(swb_outs[out_i], swb_ins[in_i])


def _connect_banyan_bb(cl, swb_ins, swb_outs, bw):
    I = int(2 * cg.utils.clog2(bw) - 2)
    J = int(bw / 2)
    for i in range(cg.utils.clog2(J)):
        r = J / (2**i)
        for j in range(J):
            t = (j % r) >= (r / 2)
            # straight
            out_i = int((i * bw) + (2 * j) + t)
            in_i = int((i * bw + bw) + (2 * j) + t)
            cl.add(
                f"swb_{i}_{j}_straight",
                "buf",
                fanin=swb_outs[out_i],
                fanout=swb_ins[in_i],
            )

            # cross
            out_i = int((i * bw) + (2 * j) + (1 - t) + ((r - 1) * ((1 - t) * 2 - 1)))
            in_i = int((i * bw + bw) + (2 * j) + (1 - t))
            cl.add(
                f"swb_{i}_{j}_cross", "buf", fanin=swb_outs[out_i], fanout=swb_ins[in_i]
            )

            if r > 2:
                # straight
                out_i = int(((I * J * 2) - ((2 + i) * bw)) + (2 * j) + t)
                in_i = int(((I * J * 2) - ((1 + i) * bw)) + (2 * j) + t)
                cl.add(
                    f"swb_{i}_{j}_r_straight",
                    "buf",
                    fanin=swb_outs[out_i],
                    fanout=swb_ins[in_i],
                )

                # cross
                out_i = int(
                    ((I * J * 2) - ((2 + i) * bw))
                    + (2 * j)
                    + (1 - t)
                    + ((r - 1) * ((1 - t) * 2 - 1))
                )
                in_i = int(((I * J * 2) - ((1 + i) * bw)) + (2 * j) + (1 - t))
                cl.add(
                    f"swb_{i}_{j}_r_cross",
                    "buf",
                    fanin=swb_outs[out_i],
                    fanout=swb_ins[in_i],
                )


def full_lock(c, bw, lw, avoid_loops=False):
    """Locks a circuitgraph with Full-Lock.

    Hadi Mardani Kamali, Kimia Zamiri Azar, Houman Homayoun,
    and Avesta Sasan. 2019. Full-Lock: Hard Distributions of SAT instances
    for Obfuscating Circuits using Fully Configurable Logic and Routing
    Blocks. In Proceedings of the 56th Annual Design Automation Conference
    2019. Association for Computing Machinery, New York, NY, USA.

    Parameters
    ----------
    circuit: circuitgraph.CircuitGraph
            Circuit to lock.
    banyan_width: int
            Width of Banyan network to use, must follow bw = 2**n, n>1.
    lut_width: int
            Width to use for inserted LUTs, must evenly divide bw.
    avoid_loops: bool
            If True, gates fed by the Banyan network will be selected
            such that they do not cause combinational loops.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # lock with luts
    if avoid_loops:
        gates = []
        potential_gates = {g for g in c.nodes() - c.io() if len(c.fanin(g)) <= lw}
        for _ in range(int(bw / lw)):
            gates.append(random.choice(list(potential_gates)))
            potential_gates -= c.transitive_fanin(gates[-1])
            potential_gates -= c.transitive_fanout(gates[-1])
            if not potential_gates:
                raise ValueError("Could not find enough gates to make " "acyclic lock")
        cl, key = random_lut_lock(c, int(bw / lw), lw, gates=gates)
    else:
        cl, key = random_lut_lock(c, int(bw / lw), lw)

    # generate switch
    m = cg.tx.strip_io(cg.logic.mux(2))
    s = cg.Circuit(name="switch")
    s.add_subcircuit(m, "m0")
    s.add_subcircuit(m, "m1")
    s.add("in_0", "buf", fanout=["m0_in_0", "m1_in_1"])
    s.add("in_1", "buf", fanout=["m0_in_1", "m1_in_0"])
    s.add("out_0", "xor", fanin="m0_out")
    s.add("out_1", "xor", fanin="m1_out")
    s.add("key_0", "input", fanout=["m0_sel_0", "m1_sel_0"])
    s.add("key_1", "input", fanout="out_0")
    s.add("key_2", "input", fanout="out_1")

    # generate banyan
    I = int(2 * cg.utils.clog2(bw) - 2)
    J = int(bw / 2)

    # add switches
    for i in range(I * J):
        cl.add_subcircuit(s, f"swb_{i}")

    # make connections
    swb_ins = [f"swb_{i//2}_in_{i%2}" for i in range(I * J * 2)]
    swb_outs = [f"swb_{i//2}_out_{i%2}" for i in range(I * J * 2)]
    _connect_banyan(cl, swb_ins, swb_outs, bw)

    # get banyan io
    net_ins = swb_ins[:bw]
    net_outs = swb_outs[-bw:]

    # generate key
    for i in range(I * J):
        for j in range(3):
            key[f"swb_{i}_key_{j}"] = choice([True, False])

    # get banyan mapping
    mapping = {}
    polarity = {}
    orig_result = cg.sat.solve(cl, {**{n: False for n in net_ins}, **key})
    for net_in in net_ins:
        result = cg.sat.solve(cl, {**{n: n == net_in for n in net_ins}, **key})
        for net_out in net_outs:
            if result[net_out] != orig_result[net_out]:
                mapping[net_in] = net_out
                polarity[net_in] = result[net_out]
                break

    # connect banyan io to luts
    for i in range(int(bw / lw)):
        for j in range(lw):
            driver = cl.fanin(f"lut_{i}_sel_{j}").pop()
            cl.disconnect(driver, f"lut_{i}_sel_{j}")
            net_in = net_ins[i * lw + j]
            cl.connect(mapping[net_in], f"lut_{i}_sel_{j}")
            if not polarity[net_in]:
                driver = cl.add(f"not_{net_in}", "not", fanin=driver)
            cl.connect(driver, net_in)

    for k in key:
        cl.set_type(k, "input")

    cg.lint(cl)
    if avoid_loops and cl.is_cyclic():
        raise ValueError("Locked circuit is cyclic")
    return cl, key


def full_lock_mux(c, bw, lw):
    """Locks a circuitgraph with a muxed-based model of Full-Lock.

    Uses muxes instead of the Banyan network, a relaxation that breaks symmetry
    and simplifies the model substantially.

    Joseph Sweeney, Marijn J.H. Heule, and Lawrence Pileggi
    Modeling Techniques for Logic Locking. In Proceedings
    of the International Conference on Computer Aided Design 2020 (ICCAD-39).

    Parameters
    ----------
    c: circuitgraph.CircuitGraph
            Circuit to lock.
    banyan_width: int
            Width of Banyan network to use, must follow bw = 2**n, n>1.
    lut_width: int
            Width to use for inserted LUTs, must evenly divide bw.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    # first generate banyan, to get a valid mapping for the key
    b = cg.Circuit()

    # generate switch
    m = cg.tx.strip_io(cg.logic.mux(2))
    s = cg.Circuit(name="switch")
    s.add_subcircuit(m, "m0")
    s.add_subcircuit(m, "m1")
    s.add("in_0", "buf", fanout=["m0_in_0", "m1_in_1"])
    s.add("in_1", "buf", fanout=["m0_in_1", "m1_in_0"])
    s.add("out_0", "xor", fanin="m0_out")
    s.add("out_1", "xor", fanin="m1_out")
    s.add("key_0", "input", fanout=["m0_sel_0", "m1_sel_0"])
    s.add("key_1", "input", fanout="out_0")
    s.add("key_2", "input", fanout="out_1")

    # generate banyan
    I = int(2 * cg.utils.clog2(bw) - 2)
    J = int(bw / 2)

    # add switches
    for i in range(I * J):
        b.add_subcircuit(s, f"swb_{i}")

    # make connections
    swb_ins = [f"swb_{i//2}_in_{i%2}" for i in range(I * J * 2)]
    swb_outs = [f"swb_{i//2}_out_{i%2}" for i in range(I * J * 2)]
    _connect_banyan(b, swb_ins, swb_outs, bw)

    # get banyan io
    net_ins = swb_ins[:bw]
    net_outs = swb_outs[-bw:]

    # generate key
    key = {}
    for i in range(I * J):
        for j in range(3):
            key[f"swb_{i}_key_{j}"] = choice([True, False])

    # get banyan mapping
    mapping = {}
    polarity = {}
    orig_result = cg.sat.solve(b, {**{n: False for n in net_ins}, **key})
    for net_in in net_ins:
        result = cg.sat.solve(
            b, {**{n: False if n != net_in else True for n in net_ins}, **key}
        )
        for net_out in net_outs:
            if result[net_out] != orig_result[net_out]:
                mapping[net_in] = net_out
                polarity[net_in] = result[net_out]
                break

    # lock with luts
    cl, key = random_lut_lock(c, int(bw / lw), lw)

    # generate mux
    m = cg.tx.strip_io(cg.logic.mux(bw))

    # add muxes and xors
    banyan_to_mux = {}
    for i in range(bw):
        cl.add_subcircuit(m, f"mux_{i}")
        for b in range(cg.utils.clog2(bw)):
            cl.add(f"key_{i}_{b}", "input", fanout=f"mux_{i}_sel_{b}")
        cl.add(f"mux_{i}_xor", "xor", fanin=f"mux_{i}_out")
        cl.add(f"key_{i}_{cg.utils.clog2(bw)}", "input", fanout=f"mux_{i}_xor")
        banyan_to_mux[net_outs[i]] = f"mux_{i}_xor"

    # connect muxes to luts
    for i in range(bw):
        net_in = net_ins[i]
        xor = banyan_to_mux[mapping[net_in]]
        o = int(xor.split("_")[1])

        driver = cl.fanin(f"lut_{i//lw}_sel_{i%lw}").pop()
        cl.disconnect(driver, f"lut_{i//lw}_sel_{i%lw}")

        if not polarity[net_in]:
            driver = cl.add(f"not_{net_in}", "not", fanin=driver)
            key[f"key_{o}_{cg.utils.clog2(bw)}"] = True
        else:
            key[f"key_{o}_{cg.utils.clog2(bw)}"] = False

        for b in range(bw):
            cl.connect(driver, f"mux_{b}_in_{i}")

        cl.connect(xor, f"lut_{i//lw}_sel_{i%lw}")
        for b, v in enumerate(cg.utils.int_to_bin(i, cg.utils.clog2(bw), True)):
            key[f"key_{o}_{b}"] = v

    cg.lint(cl)
    return cl, key


def inter_lock(c, bw, reduced_swb=False):
    """Locks a circuitgraph with InterLock.

    Kamali, Hadi Mardani, Kimia Zamiri Azar, Houman Homayoun, and Avesta Sasan.
    "Interlock: An intercorrelated logic and routing locking."
    In 2020 IEEE/ACM International Conference On Computer Aided Design (ICCAD),
    pp. 1-9. IEEE, 2020.

    Parameters
    ----------
    circuit: circuitgraph.CircuitGraph
            Circuit to lock.
    bw: int
            The size of the keyed rounting block. A bw of m results
            in an m x m sized KeyRB.
    reduced_swb: bool
            If True, each switchbox is reduced from 3 keys to 1 key due to the fact
            that for 100% utilization, the other 2 keys will never be used. Essentially,
            the muxes at the output of the switchbox are removed.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    cl = c.copy()
    cg.lint(cl)

    # generate switch
    m = cg.tx.strip_io(cg.logic.mux(2))
    s = cg.Circuit(name="switch")
    s.add_subcircuit(m, "m0")
    s.add_subcircuit(m, "m1")
    s.add("in_0", "input", fanout=["m0_in_0", "m1_in_1"])
    s.add("in_1", "input", fanout=["m0_in_1", "m1_in_0"])
    s.add("ex_in_0", "input")
    s.add("ex_in_1", "input")
    # f1 and f2 starts as 'and' gates, must be updated later
    s.add("f1_out", "and", fanin=["m0_out", "ex_in_0"])
    s.add("f2_out", "and", fanin=["m1_out", "ex_in_1"])
    s.add("key_0", "input", fanout=["m0_sel_0", "m1_sel_0"])
    s.add("out_0", "buf", output=True)
    s.add("out_1", "buf", output=True)
    if not reduced_swb:
        s.add_subcircuit(m, "m2")
        s.add_subcircuit(m, "m3")
        s.add("key_1", "input", fanout="m2_sel_0")
        s.add("key_2", "input", fanout="m3_sel_0")
        s.connect("f1_out", "m2_in_0")
        s.connect("f2_out", "m3_in_1")
        s.connect("m0_out", "m3_in_0")
        s.connect("m1_out", "m2_in_1")
        s.connect("m2_out", "out_0")
        s.connect("m3_out", "out_1")
    else:
        s.connect("f1_out", "out_0")
        s.connect("f2_out", "out_1")

    sbb_inputs = ["in_0", "in_1", "ex_in_0", "ex_in_1", "key_0"]
    if not reduced_swb:
        sbb_inputs += ["key_1", "key_2"]
    sbb = cg.BlackBox(
        "switch",
        sbb_inputs,
        ["out_0", "out_1"],
    )

    # Select paths to embed in the routing network
    path_length = 2 * cg.utils.clog2(bw) - 2
    paths = []

    filtered_gates = set()

    def filter_gate(n):
        gate = n
        gates = [n]
        for _ in range(path_length):
            if (
                len(cl.fanin(gate)) != 2
                or len(cl.fanout(gate)) != 1
                or cl.is_output(gate)
                or gate in filtered_gates
                or len(cl.fanin(gate) & filtered_gates) > 0
                or len(cl.fanout(gate) & filtered_gates) > 0
            ):
                return False
            gate = cl.fanout(gate).pop()
            gates.append(gate)
        filtered_gates.update(gates)
        for gate in gates:
            filtered_gates.update(cl.fanin(gate))
        return True

    candidate_gates = filter(filter_gate, cl.nodes())
    for _ in range(bw):
        try:
            gate = next(candidate_gates)
        except StopIteration as e:
            raise ValueError("Not enough candidate gates found for locking") from e
        path = [gate]
        for _ in range(path_length - 1):
            gate = cl.fanout(gate).pop()
            path.append(gate)
        paths.append(path)

    # generate banyan with J rows and I columns of SwBs
    I = path_length
    J = int(bw / 2)

    for i in range(I * J):
        cl.add_blackbox(sbb, f"swb_{i}")

    # make connections
    swb_ins = [f"swb_{i//2}.in_{i%2}" for i in range(I * J * 2)]
    swb_outs = [f"swb_{i//2}.out_{i%2}" for i in range(I * J * 2)]
    _connect_banyan_bb(cl, swb_ins, swb_outs, bw)

    # generate key
    # In the example from the paper, the paths in a SWB directly from an
    # input to an output are never used. Starting with that implemetation.
    # Could sometimes choose paths less than `path_length` and use these
    # connections with a decoy external input, but such a strategy is not
    # discussed in the paper.
    swaps = []
    key = {}
    for i in range(I * J):
        swaps.append(choice([True, False]))
        if swaps[-1]:
            key[f"swb_{i}_key_0"] = True
        else:
            key[f"swb_{i}_key_0"] = False
        if not reduced_swb:
            key[f"swb_{i}_key_1"] = False
            key[f"swb_{i}_key_2"] = True

    f_gates = {}

    # Add paths to banyan
    # Get a random intial ordering of paths
    input_order = list(range(bw))
    shuffle(input_order)
    for i, p_idx in enumerate(input_order):
        path = paths[p_idx]
        swb_idx = i // 2
        i_idx = i % 2
        prev_node = cl.fanin(path[0]).pop()
        cl.connect(prev_node, f"swb_{swb_idx}.in_{i_idx}")
        for j, n in enumerate(path):
            o_idx = i_idx ^ int(swaps[swb_idx])
            ex_i = (cl.fanin(n) - {prev_node}).pop()
            cl.connect(ex_i, f"swb_{swb_idx}.ex_in_{o_idx}")
            f_gates[f"swb_{swb_idx}_f{o_idx+1}_out"] = cl.type(n)
            if j != len(path) - 1:
                next_n = cl.fanout(f"swb_{swb_idx}.out_{o_idx}").pop()
                next_n = cl.fanout(next_n).pop()
                swb_idx = int(next_n.split(".")[0].split("_")[-1])
                i_idx = int(next_n.split(".")[-1].split("_")[-1])
                prev_node = n
            else:
                for fo in cl.fanout(n):
                    cl.disconnect(n, fo)
                    try:
                        conn = cl.fanout(f"swb_{swb_idx}.out_{o_idx}").pop()
                    except KeyError:
                        conn = cl.add(
                            f"swb_{swb_idx}_out_{o_idx}_load",
                            "buf",
                            fanin=f"swb_{swb_idx}.out_{o_idx}",
                        )
                    cl.connect(conn, fo)

    for path in paths:
        for node in path:
            cl.remove(node)

    for i in range(I * J):
        cl.fill_blackbox(f"swb_{i}", s)

    for k, v in f_gates.items():
        cl.set_type(k, v)

    for k in key:
        cl.set_type(k, "input")

    cg.lint(cl)
    return cl, key


def lebl(c, bw, ng):
    """Locks a circuitgraph with Logic-Enhanced Banyan Locking.

    Joseph Sweeney, Marijn J.H. Heule, and Lawrence Pileggi Modeling Techniques
    for Logic Locking. In Proceedings of the International Conference on
    Computer Aided Design 2020 (ICCAD-39).

    Parameters
    ----------
    c: circuitgraph.CircuitGraph
            Circuit to lock.
    bw: int
            Width of Banyan network.
    lw: int
            Minimum number of gates mapped to network.

    Returns
    -------
    circuitgraph.CircuitGraph, dict of str:bool
            the locked circuit and the correct key value for each key input
    """
    from pysat.card import CardEnc
    from pysat.formula import IDPool
    from pysat.solvers import Cadical

    # create copy to lock
    cl = c.copy()

    # generate switch and mux
    s = cg.Circuit(name="switch")
    m2 = cg.tx.strip_io(cg.logic.mux(2))
    s.add_subcircuit(m2, "m2_0")
    s.add_subcircuit(m2, "m2_1")
    m4 = cg.tx.strip_io(cg.logic.mux(4))
    s.add_subcircuit(m4, "m4_0")
    s.add_subcircuit(m4, "m4_1")
    s.add("in_0", "buf", fanout=["m2_0_in_0", "m2_1_in_1"])
    s.add("in_1", "buf", fanout=["m2_0_in_1", "m2_1_in_0"])
    s.add("out_0", "buf", fanin="m4_0_out")
    s.add("out_1", "buf", fanin="m4_1_out")
    s.add("key_0", "input", fanout=["m2_0_sel_0", "m2_1_sel_0"])
    s.add("key_1", "input", fanout=["m4_0_sel_0", "m4_1_sel_0"])
    s.add("key_2", "input", fanout=["m4_0_sel_1", "m4_1_sel_1"])

    # generate banyan
    I = int(2 * cg.utils.clog2(bw) - 2)
    J = int(bw / 2)

    # add switches and muxes
    for i in range(I * J):
        cl.add_subcircuit(s, f"swb_{i}")

    # make connections
    swb_ins = [f"swb_{i//2}_in_{i%2}" for i in range(I * J * 2)]
    swb_outs = [f"swb_{i//2}_out_{i%2}" for i in range(I * J * 2)]
    _connect_banyan(cl, swb_ins, swb_outs, bw)

    # get banyan io
    net_ins = swb_ins[:bw]
    net_outs = swb_outs[-bw:]

    # generate key
    key = {f"swb_{i//3}_key_{i%3}": choice([True, False]) for i in range(3 * I * J)}

    # generate connections between banyan nodes
    bfi = {n: set() for n in swb_outs + net_ins}
    bfo = {n: set() for n in swb_outs + net_ins}
    for n in swb_outs + net_ins:
        if cl.fanout(n):
            fo_node = cl.fanout(n).pop()
            swb_i = fo_node.split("_")[1]
            bfi[f"swb_{swb_i}_out_0"].add(n)
            bfi[f"swb_{swb_i}_out_1"].add(n)
            bfo[n].add(f"swb_{swb_i}_out_0")
            bfo[n].add(f"swb_{swb_i}_out_1")

    # find a mapping of circuit onto banyan
    net_map = IDPool()
    for bn in swb_outs + net_ins:
        for cn in c:
            net_map.id(f"m_{bn}_{cn}")

    # mapping implications
    clauses = []
    for bn in swb_outs + net_ins:
        # fanin
        if bfi[bn]:
            for cn in c:
                if c.fanin(cn):
                    for fcn in c.fanin(cn):
                        clause = [-net_map.id(f"m_{bn}_{cn}")]
                        clause += [net_map.id(f"m_{fbn}_{fcn}") for fbn in bfi[bn]]
                        clause += [net_map.id(f"m_{fbn}_{cn}") for fbn in bfi[bn]]
                        clauses.append(clause)
                else:
                    clause = [-net_map.id(f"m_{bn}_{cn}")]
                    clause += [net_map.id(f"m_{fbn}_{cn}") for fbn in bfi[bn]]
                    clauses.append(clause)

        # fanout
        if bfo[bn]:
            for cn in c:
                clause = [-net_map.id(f"m_{bn}_{cn}")]
                clause += [net_map.id(f"m_{fbn}_{cn}") for fbn in bfo[bn]]
                for fcn in c.fanout(cn):
                    clause += [net_map.id(f"m_{fbn}_{fcn}") for fbn in bfo[bn]]
                clauses.append(clause)

    # no feed through
    for cn in c:
        net_map.id(f"INPUT_OR_{cn}")
        net_map.id(f"OUTPUT_OR_{cn}")
        clauses.append(
            [-net_map.id(f"INPUT_OR_{cn}")]
            + [net_map.id(f"m_{bn}_{cn}") for bn in net_ins]
        )
        clauses.append(
            [-net_map.id(f"OUTPUT_OR_{cn}")]
            + [net_map.id(f"m_{bn}_{cn}") for bn in net_outs]
        )
        for bn in net_ins:
            clauses.append([net_map.id(f"INPUT_OR_{cn}"), -net_map.id(f"m_{bn}_{cn}")])
        for bn in net_outs:
            clauses.append([net_map.id(f"OUTPUT_OR_{cn}"), -net_map.id(f"m_{bn}_{cn}")])
        clauses.append([-net_map.id(f"OUTPUT_OR_{cn}"), -net_map.id(f"INPUT_OR_{cn}")])

    # at least ngates
    for bn in swb_outs + net_ins:
        net_map.id(f"NGATES_OR_{bn}")
        clauses.append(
            [-net_map.id(f"NGATES_OR_{bn}")] + [net_map.id(f"m_{bn}_{cn}") for cn in c]
        )
        for cn in c:
            clauses.append([net_map.id(f"NGATES_OR_{bn}"), -net_map.id(f"m_{bn}_{cn}")])
    clauses += CardEnc.atleast(
        bound=ng,
        lits=[net_map.id(f"NGATES_OR_{bn}") for bn in swb_outs + net_ins],
        vpool=net_map,
    ).clauses

    # at most one mapping per out
    for bn in swb_outs + net_ins:
        clauses += CardEnc.atmost(
            lits=[net_map.id(f"m_{bn}_{cn}") for cn in c], vpool=net_map
        ).clauses

    # limit number of times a gate is mapped to net outputs to fanout of gate
    for cn in c:
        lits = [net_map.id(f"m_{bn}_{cn}") for bn in net_outs]
        bound = len(c.fanout(cn))
        if len(lits) < bound:
            continue
        clauses += CardEnc.atmost(bound=bound, lits=lits, vpool=net_map).clauses

    # prohibit outputs from net
    for bn in swb_outs + net_ins:
        for cn in c.outputs():
            clauses += [[-net_map.id(f"m_{bn}_{cn}")]]

    # solve
    solver = Cadical(bootstrap_with=clauses)
    if not solver.solve():
        raise ValueError(f"No config for width '{bw}'")
    model = solver.get_model()

    # get mapping
    mapping = {}
    for bn in swb_outs + net_ins:
        selected_gates = [cn for cn in c if model[net_map.id(f"m_{bn}_{cn}") - 1] > 0]
        if len(selected_gates) > 1:
            raise ValueError(f"Multiple gates mapped to '{bn}'")
        mapping[bn] = selected_gates[0] if selected_gates else None

    potential_net_fanins = list(
        c.nodes()
        - (c.endpoints() | set(mapping.values()) | mapping.keys() | c.startpoints())
    )

    # connect net inputs
    for bn in net_ins:
        if mapping[bn]:
            cl.connect(mapping[bn], bn)
        else:
            cl.connect(choice(potential_net_fanins), bn)
    mapping.update({cl.fanin(bn).pop(): cl.fanin(bn).pop() for bn in net_ins})
    potential_net_fanouts = list(
        c.nodes()
        - (c.startpoints() | set(mapping.values()) | mapping.keys() | c.endpoints())
    )

    # connect switch boxes
    for i, bn in enumerate(swb_outs):
        # get keys
        if key[f"swb_{i//2}_key_1"] and key[f"swb_{i//2}_key_2"]:
            k = 3
        elif not key[f"swb_{i//2}_key_1"] and key[f"swb_{i//2}_key_2"]:
            k = 2
        elif key[f"swb_{i//2}_key_1"] and not key[f"swb_{i//2}_key_2"]:
            k = 1
        elif not key[f"swb_{i//2}_key_1"] and not key[f"swb_{i//2}_key_2"]:
            k = 0
        switch_key = 1 if key[f"swb_{i//2}_key_0"] == 1 else 0

        mux_input = f"swb_{i//2}_m4_{i%2}_in_{k}"

        # connect inner nodes
        mux_gate_types = set()

        # constant output, hookup to a node that is already in the affected outputs
        # fanin, not in others
        if not mapping[bn] and bn in net_outs:
            decoy_fanout_gate = choice(potential_net_fanouts)
            # selected_fo[bn] = decoy_fanout_gate
            if cl.type(decoy_fanout_gate) in ["and", "nand"]:
                cl.set_type(mux_input, "1")
            elif cl.type(decoy_fanout_gate) in ["or", "nor", "xor", "xnor"]:
                cl.set_type(mux_input, "0")
            elif cl.type(decoy_fanout_gate) in ["buf"]:
                if randint(0, 1):
                    cl.set_type(mux_input, "1")
                    cl.set_type(decoy_fanout_gate, choice(["and", "xnor"]))
                else:
                    cl.set_type(mux_input, "0")
                    cl.set_type(decoy_fanout_gate, choice(["or", "xor"]))
            elif cl.type(decoy_fanout_gate) in ["not"]:
                if randint(0, 1):
                    cl.set_type(mux_input, "1")
                    cl.set_type(decoy_fanout_gate, choice(["nand", "xor"]))
                else:
                    cl.set_type(mux_input, "0")
                    cl.set_type(decoy_fanout_gate, choice(["nor", "xnor"]))
            elif cl.type(decoy_fanout_gate) in ["0", "1"]:
                cl.set_type(mux_input, cl.type(decoy_fanout_gate))
                cl.set_type(decoy_fanout_gate, "buf")
            else:
                raise ValueError(f"Invalid gate type '{cl.type(decoy_fanout_gate)}'")
            cl.connect(bn, decoy_fanout_gate)
            mux_gate_types.add(cl.type(mux_input))

        # feedthrough
        elif mapping[bn] in [mapping[fbn] for fbn in bfi[bn]]:
            cl.set_type(mux_input, "buf")
            mux_gate_types.add("buf")
            if mapping[cl.fanin(f"swb_{i//2}_in_0").pop()] == mapping[bn]:
                cl.connect(f"swb_{i//2}_m2_{switch_key}_out", mux_input)
            else:
                cl.connect(f"swb_{i//2}_m2_{1-switch_key}_out", mux_input)

        # gate
        elif mapping[bn]:
            cl.set_type(mux_input, cl.type(mapping[bn]))
            mux_gate_types.add(cl.type(mapping[bn]))
            gfi = cl.fanin(mapping[bn])
            if mapping[cl.fanin(f"swb_{i//2}_in_0").pop()] in gfi:
                cl.connect(f"swb_{i//2}_m2_{switch_key}_out", mux_input)
                gfi.remove(mapping[cl.fanin(f"swb_{i//2}_in_0").pop()])
            if mapping[cl.fanin(f"swb_{i//2}_in_1").pop()] in gfi:
                cl.connect(f"swb_{i//2}_m2_{1-switch_key}_out", mux_input)

        # mapped to None, any key works
        else:
            k = None

        # fill out random gates
        for j in range(4):
            if j != k:
                t = choice(
                    tuple(
                        {
                            "buf",
                            "or",
                            "nor",
                            "and",
                            "nand",
                            "not",
                            "xor",
                            "xnor",
                            "0",
                            "1",
                        }
                        - mux_gate_types
                    )
                )
                mux_gate_types.add(t)
                mux_input = f"swb_{i//2}_m4_{i%2}_in_{j}"
                cl.set_type(mux_input, t)
                if t in ("not", "buf"):
                    # pick a random fanin
                    cl.connect(f"swb_{i//2}_m2_{randint(0,1)}_out", mux_input)
                elif t in ("0", "1"):
                    pass
                else:
                    cl.connect(f"swb_{i//2}_m2_0_out", mux_input)
                    cl.connect(f"swb_{i//2}_m2_1_out", mux_input)

    # connect outputs non constant outs
    rev_mapping = {}
    for bn in net_outs:
        if mapping[bn]:
            if mapping[bn] not in rev_mapping:
                rev_mapping[mapping[bn]] = set()
            rev_mapping[mapping[bn]].add(bn)

    for cn, val in rev_mapping.items():
        for fcn, bn in zip_longest(cl.fanout(cn), val, fillvalue=list(val)[0]):
            cl.connect(bn, fcn)

    # delete mapped gates
    deleted = True
    while deleted:
        deleted = False
        for n in cl.nodes():
            # node and all fanout are in the net
            if n not in mapping and n in mapping.values():
                if all(
                    s not in mapping and s in mapping.values() for s in cl.fanout(n)
                ):
                    cl.remove(n)
                    deleted = True
            # node in net fanout
            if n in [mapping[o] for o in net_outs] and n in cl:
                cl.remove(n)
                deleted = True

    for k in key:
        cl.set_type(k, "input")

    cg.lint(cl)
    return cl, key
