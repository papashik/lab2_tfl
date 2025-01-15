import networkx as nx
import matplotlib.pyplot as plt
import random
import math

from FAdo.common import DFAequivalent
from FAdo.fa import DFA
from collections import deque
import json
import socket

def create(m, n):
    G = nx.Graph()

    for j in range(n):
        for i in range(m):
            G.add_node((2*i + 1, 4*j))
        for k in range(2):
            for i in range(m+1):
                G.add_node((2*i, 4*j + k+1))
        for i in range(m):
            G.add_node((2*i + 1, 4*j + 3))
        for i in range(m+1):
            G.add_edge((2*i, 4*j + 1), (2*i, 4*j + 2))
        for i in range(m):
            G.add_edge((2*i + 1, 4*j), (2*i, 4*j + 1))
            G.add_edge((2*i + 1, 4*j), (2*(i+1), 4*j + 1))
            G.add_edge((2*i + 1, 4*j + 3), (2*i, 4*j + 2))
            G.add_edge((2*i + 1, 4*j + 3), (2*(i+1), 4*j + 2))
        for i in range(m):
            if j == n-1: continue
            G.add_edge((2*i + 1, 4*j + 3), (2*i + 1, 4*j + 4))
    return G

def make_holes(G: nx.Graph, n):
    list_nodes = list(G)

    for i in range(n):
        node = random.choice(list_nodes)
        if not G.has_node(node): continue
        node_neighbors = list(G.neighbors(node))
        if len(node_neighbors) == 0: continue
        neighbor = random.choice(node_neighbors)
        node_neighbors.remove(neighbor)
        neighbor_neighbors = list(G.neighbors(neighbor))
        neighbor_neighbors.remove(node)
        G.remove_node(node)
        G.remove_node(neighbor)
        if len(node_neighbors) == 2:
            G.add_edge(node_neighbors[0], node_neighbors[1])
        if len(neighbor_neighbors) == 2:
            G.add_edge(neighbor_neighbors[0], neighbor_neighbors[1])

def remove_double(G : nx.Graph):
    list_nodes = list(G)
    removed = False
    for node in list_nodes:
        if not G.has_node(node): continue
        neighbors = list(G.neighbors(node))
        if len(neighbors) == 2:
            removed = True
            G.remove_node(node)
            G.add_edge(neighbors[0], neighbors[1])
    if removed:
        remove_double(G)

def find_point_near_segment(point1, point2, distance=1):
    x1, y1 = point1
    x2, y2 = point2

    x_seg = (x1 + x2) / 2
    y_seg = (y1 + y2) / 2

    if x2 - x1 == 0 or y2 - y1 == 0:
        slope = float('inf')
    else:
        slope = (y2 - y1) / (x2 - x1)

    if slope == float('inf'):
        perp_slope = 0
    else:
        perp_slope = -1 / slope

    if slope == float('inf'):
        x = x_seg + distance
        y = y_seg
    elif slope == 0:
        x = x_seg
        y = y_seg + distance
    else:
        y = y_seg + distance * math.sin(math.atan(perp_slope))
        x = x_seg + distance * math.cos(math.atan(perp_slope))

    return (x, y)

def choose_two_random_3_nodes(G : nx.Graph):
    node = random.choice(list(G))
    node_neighbors = list(G.neighbors(node))
    if len(node_neighbors) != 3: return choose_two_random_3_nodes(G)
    neighbor = random.choice(node_neighbors)
    if len(list(G.neighbors(neighbor))) != 3: return choose_two_random_3_nodes(G)
    return (node, neighbor)

def draw(G : nx.Graph):
    pos = {node: (node[0]*1.2, node[1]) for node in G.nodes()}

    plt.figure(figsize=(10, 8))
    nx.draw(G, pos, with_labels=False, node_size=200, node_color=[colors.get(node, 'lightblue') for node in G.nodes()], edge_color='gray')
    plt.axis('equal')
    plt.show()

def make_exits(G : nx.Graph, n):
    list_nodes = list(G)
    exits = []
    for node in list_nodes:
        if len(list(G.neighbors(node))) == 1:
            exits.append(node)
    for i in range(n - len(exits)):
        n1, n2 = choose_two_random_3_nodes(G)
        G.remove_edge(n1, n2)
        node = ((n1[0] + n2[0])/2, (n1[1] + n2[1])/2)
        G.add_node(node)
        G.add_edge(n1, node)
        G.add_edge(n2, node)
        new_exit = find_point_near_segment(n1, n2)
        G.add_edge(node, new_exit)
        exits.append(new_exit)

    return exits

def from_string(str):
    arr = str.strip().split()
    if not arr: return ['ε']
    res = []
    for elem in arr:
        if elem == '' or elem == 'ε': elem = 'ε'
        elif elem[0] == 'ε': elem = elem[1:]
        res.append(elem)
    return res

def make_dfa_learner(file_name):
    with open(file_name, 'r', encoding='utf-8') as f:
        data = json.load(f)

    table_str = data.get('table', '')
    pref = from_string(data.get('pref', ''))
    dop_pref = from_string(data.get('dop_pref', ''))
    suff = from_string(data.get('suff', ''))
    all_pref = pref + dop_pref

    v = list(table_str.replace(' ', ''))
    n = len(all_pref) * len(suff)
    if len(v) < n:
        v += ['0'] * (n - len(v))

    table = {}
    i = 0
    for p in all_pref:
        for s in suff:
            value = v[i]
            i += 1
            table[(p, s)] = value

    dfa = DFA()

    all = {}
    for p in all_pref:
        str_table = ''.join([table.get((p, s), '0') for s in suff])
        all[p] = str_table

    tables_to_states = {}
    i = 0
    for str_table in set(all.values()):
        state_name = i
        dfa.addState(i)
        tables_to_states[str_table] = state_name
        i += 1

    prefs_to_states = {}
    for p in all_pref:
        str_table = all[p]
        state = tables_to_states[str_table]
        prefs_to_states[p] = state

    for p in all_pref:
        state = prefs_to_states[p]
        for sym in ['L', 'R']:
            if p == 'ε':
                new_p = sym
            else:
                new_p = p + sym
            if new_p in all_pref:
                next_state = prefs_to_states[new_p]
                found = False
                for st, s, next_st in dfa.transitions():
                    if st == state and s == sym: found = True
                if not found:
                    dfa.addTransition(state, sym, next_state)

    dfa.setInitial(prefs_to_states['ε'])
    for p in all_pref:
        if table.get((p, 'ε'), '0') == '1':
            dfa.addFinal(prefs_to_states[p])

    return dfa

def listen(dfa : DFA):

    def handle_client(conn, addr):
        print(f"Connected by {addr}")

        try:
            while True:
                data = conn.recv(1024)
                if not data: break

                decoded_data = data.decode('utf-8')
                arr = decoded_data.strip().split()
                if arr[0] == 'word':
                    print(arr[1], dfa.evalWordP(arr[1]))
                    if dfa.evalWordP(arr[1]):
                        response = 'true\n'.encode('utf-8')
                    else:
                        response = 'false\n'.encode('utf-8')
                elif arr[0] == 'check':
                    if len(arr) == 1: file_name = 'learner.json'
                    else: file_name = arr[1]
                    learner = make_dfa_learner(file_name)
                    learner.display()
                    dfa_min = dfa.minimalHopcroft()
                    learner_min = learner.minimalHopcroft()
                    try:
                        result, v = dfa_min.witnessDiff(learner_min)
                        response = result + ' ' + str(v) + '\n' # v == 0 if belongs to learner, 1 if belongs to dfa
                    except DFAequivalent:
                        response = 'equivalent\n'
                    except Exception as ex:
                        print("ERROR:", ex)
                        response = 'error ' + str(ex) + '\n'
                    print(response)
                else: response = 'unknown request\n'

                conn.sendall(response)

        except ConnectionResetError:
            print(f"Connection reset by {addr}")
        except Exception as e:
            print(f"Error with client {addr}: {e}")
        finally:
            conn.close()
            print(f"Connection with {addr} closed.")

    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        PORT = random.randint(5000, 10000)
        s.bind(('127.0.0.1', PORT))
        s.listen()
        print(f"Server listening on :{PORT}")
        while True:
            conn, addr = s.accept()
            handle_client(conn, addr)

X_SIZE = random.randint(3, 12)
Y_SIZE = random.randint(3, 6)
HOLES = random.randint(3, X_SIZE * Y_SIZE)
EXITS = random.randint(3, 3 + X_SIZE * Y_SIZE // 4)

G = create(X_SIZE, Y_SIZE)
make_holes(G, HOLES)
remove_double(G)
exits = make_exits(G, EXITS)
colors = {i:'red' for i in exits}

n1, n2 = choose_two_random_3_nodes(G)
G.remove_edge(n1, n2)
start = ((n1[0] + n2[0])/2, (n1[1] + n2[1])/2)
G.add_node(start)
G.add_edge(n1, start)
G.add_edge(n2, start)

colors[start] = 'green'

draw(G)

dfa = DFA()
dfa.addState(0)
dfa.setInitial(0)

states = {}
states[start] = 0
i = 1
queue = deque([(start, 0)])
while queue:
    node, number = queue.popleft()
    if not G.has_node(node): continue
    neighbors = list(G.neighbors(node))

    if len(neighbors) == 2:
        n1, n2 = neighbors
        if n1 not in states:
            dfa.addState(i)
            states[n1] = i
            i += 1
        i_n1 = states[n1]
        if n2 not in states:
            dfa.addState(i)
            states[n2] = i
            i += 1
        i_n2 = states[n2]
        dfa.addTransition(number, 'L', i_n1)
        dfa.addTransition(number, 'R', i_n2)
        queue.append((n1, i_n1))
        queue.append((n2, i_n2))

    elif len(neighbors) == 1:
        n1 = neighbors[0]
        if n1 not in states:
            dfa.addState(i)
            states[n1] = i
            i += 1
        i_n1 = states[n1]
        dfa.addTransition(number, random.choice(['L', 'R']), i_n1)
        queue.append((n1, i_n1))
    else:
        dfa.addFinal(number)

    G.remove_node(node)

#dfa = dfa.minimalHopcroft()
dfa.display()

num1 = len(dfa.States)
num2 = EXITS
try:
    with open('parameters.txt', 'w') as f:
        f.write(str(num1) + '\n')
        f.write(str(num2) + '\n')
    print(f"Successfully wrote {num1} and {num2}")
except Exception as e:
    print(f"Error writing to file: {e}")

listen(dfa)