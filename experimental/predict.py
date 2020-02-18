#!/usr/bin/env python3

"""
 Script for predicting automata sizes in formula construction.
 @title predict.py
 @author Ondřej Valeš, 2019
"""

import sys
import getopt
import subprocess
import os
import graphviz
import math
import socket
from collections import defaultdict

FORMULAS = 400
MAX_LABEL = 2000
CREATE_FILES = True

SOCKET_NR = 50888

PRED_CALL = "PredCall"
SKIP_OP = ["Negate", "Restrict", PRED_CALL]
NULLARY_OP = [
    "True", "False", "Empty", "FirstOrder", "Const",
    "Singleton", "BoolVar", "In", "Eq1", "Eq2", "Sub2",
    "Less1", "LessEq1", "EqPlus2", "EqMinus2", "EqMin",
    "EqMax", "EqPlus1", "EqMinus1", "Union", "Inter",
    "SetMinus", "EqPlusModulo", "EqMinusModulo", "PresbConst"
]
UNARY_OP = ["Project"]

CONST_SIZES = {
    "True" : 2,
    "False" : 2,
    "Empty" : 3,
    "FirstOrder" : 3,
    "Singleton" : 4,
    "BoolVar" : 3,
    "In" : 4,
    "Eq1" : 4,
    "Eq2" : 3,
    "Sub2" : 3,
    "Less1" : 5,
    "LessEq1" : 5,
    "EqPlus2" : 4,
    "EqMinus2" : 6,
    "EqMin" : 6,
    "EqMax" : 5,
    "EqMinus1" : 6,
    "Union" : 3,
    "Inter" : 3,
    "SetMinus" : 3,
    "EqPlusModulo" : 13,
    "EqMinusModulo" : 12,
}

CALC_SIZES = {
    "Const" : lambda x : x + 4,
    "EqPlus1" : lambda x : x + 4,
    "PresbConst" : lambda x : 3 if x < 1 else 4 + int(math.log2(x))
}

def raiseEx(msg):
    raise Exception(msg)

# prediction of the size of the output automaton
# we only take the slope
PREDICT_MINSIZE = {
        "And" : defaultdict(lambda: (lambda x: x * 0.0631), # taken from "And"[4]
        {
            0: lambda x: x * 0.666,
            1: lambda x: x * 0.0555,
            2: lambda x: x * 0.0863,
            3: lambda x: x * 0.0583,
            4: lambda x: x * 0.0631
        }
    ),
    "Or" : defaultdict(lambda: (lambda x: x * 0.632), # taken from "Or"[2]
        {
            2: lambda x: x * 0.632,
            3: lambda x: x * 0.0659
        }
    ),
    "Project" : defaultdict(
        lambda: (lambda x: raiseEx("Invalid # of free variables for Proj: " + str(x))),
        {
            1: lambda x: x * 0.899
        }
    ),
    "Impl" : defaultdict(lambda: (lambda x: x * 0.141), # taken from "Impl"[1]
        {
            1: lambda x: x * 0.141
        }
    ),
    "Biimpl" : defaultdict(lambda: (lambda x: x * 0.666), # taken from "Equiv"[0]
        {
            0: lambda x: x * 0.666,
            1: lambda x: x * 0.5
        }
    )
}

# prediction of the cost of constructing the output automaton
# we only take the slope
PREDICT_COST = {
    "And" : defaultdict(lambda: (lambda x: x * 0.174), # taken from "And"[4]
        {
            0: lambda x: x * 1.337,
            1: lambda x: x * 0.331,
            2: lambda x: x * 0.173,
            3: lambda x: x * 0.116,
            4: lambda x: x * 0.174
        }
    ),
    "Or" : defaultdict(lambda: (lambda x: x * 1.225), # taken from "Or"[2]
        {
            2: lambda x: x * 1.225,
            3: lambda x: x * 0.139
        }
    ),
    "Project" : defaultdict(
        lambda: (lambda x: raiseEx("Invalid # of free variables for Proj: " + str(x))),
        {
            1: lambda x: x * 1.799
        }
    ),
    "Impl" : defaultdict(lambda: (lambda x: x * 0.425), # taken from "Impl"[1]
        {
            1: lambda x: x * 0.425
        }
    ),
    "Biimpl" : defaultdict(lambda: (lambda x: x * 1.333), # taken from "Equiv"[0]
        {
            0: lambda x: x * 1.333,
            1: lambda x: x * 1.000
        }
    )
}

# MAX_SHARED = {k : len(PREDICT[k]) for k in PREDICT}

class Formula:
    _counter = 1
    @staticmethod
    def _skip_unused(formula):
        while True:
            if formula[-1] == ']':
                formula, repls = formula[:-1].rsplit('[', 1)
                repls
                for repl in reversed(repls.split(',')):
                    old, new = repl.split('->')
                    formula = formula.replace(old, new)
            oper, formula = formula[:-1].split('(', 1)
            if oper == PRED_CALL:
                formula = formula.split(',', 1)[1]
                formula
            if oper not in SKIP_OP:
                return oper, formula


    @staticmethod
    def _split_index(formula):
        ind = 0
        cnt = 0
        while True:
            if formula[ind] == ',' and cnt == 0:
                break
            if formula[ind] in ['(', '[']:
                cnt += 1
            if formula[ind] in [')', ']']:
                cnt -= 1
            ind += 1
        return ind


    def __init__(self, formula):
        self.id = str(Formula._counter)
        Formula._counter += 1
        oper, formula = Formula._skip_unused(formula)

        self.name = oper + "(" + formula + ")"
        self.oper = oper

        if self.oper in NULLARY_OP:
            self.__init_nullary__(formula)
        elif self.oper in UNARY_OP:
            self.__init_unary__(formula)
        else:
            ind = Formula._split_index(formula)
            self.__init_binary__(formula[:ind], formula[ind + 1:])


    def __init_nullary__(self, formula):
        self.right = None
        self.left = None
        if self.oper in CONST_SIZES:
            self.size = CONST_SIZES[self.oper]
            self.fv = set(formula.split(','))
        else:
            n = int(formula.split(',')[-1])
            self.fv = set(formula.split(',')[:-1])
            self.size = CALC_SIZES[self.oper](n)
        self.total_size = self.size


    def __init_unary__(self, formula):
        self.var, formula = formula.split(',', 1)
        self.left = Formula(formula)
        self.right = None
        self.fv = self.left._get_fv()
        self.fv.discard(self.var)
        shared_vars = 1
        self.size = int(PREDICT_MINSIZE[self.oper][shared_vars](self.left.size))
        self.size = max(1, self.size)
        self.total_size = int(PREDICT_COST[self.oper][shared_vars](
                          self.left.size)) + self.left.total_size


    def __init_binary__(self, lformula, rformula):
        self.left = Formula(lformula)
        self.right = Formula(rformula)
        self.fv = self.left._get_fv().union(self.right._get_fv())
        shared_vars = len(self.left.fv) + len(self.right.fv) - len(self.fv)
        # shared_vars = min(shared_vars, MAX_SHARED[self.oper]-1)
        prod_size = self.left.size * self.right.size
        self.size = int(PREDICT_MINSIZE[self.oper][shared_vars](prod_size))
        self.size = max(1, self.size)
        self.total_size = int(PREDICT_COST[self.oper][shared_vars](
                          prod_size)) + self.left.total_size + self.right.total_size


    def _get_fv(self):
        return self.fv.copy()


    def to_graph(self, name):
        graph = graphviz.Digraph(name)
        self._to_graph(graph)
        return graph


    def _to_graph(self, graph):
        if self.left is None:
            create_leaf_node(graph, self.id, self.name, str(self.size), self.fv)
        elif self.right is None:
            self.left._to_graph(graph)
            create_unary_node(graph, self.id, self.name, str(self.size), self.fv,
                              self.left.id, self.oper)
        else:
            self.left._to_graph(graph)
            self.right._to_graph(graph)
            create_binary_node(graph, self.id, self.name, str(self.size), self.fv,
                               self.left.id, self.right.id, self.oper)


def main():
    global SOCKET_NR

    monabin = parse_args(sys.argv)
    i = 0


    socket_in = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    socket_in.bind(('localhost', SOCKET_NR))
    socket_in.listen()
    while True:
        conn, _ = socket_in.accept()
        monafile = conn.recv(2048).decode()
        monafile = monafile.strip()
        #print(i)
        i += 1

        if monafile == "stop":
            break

        try:
            mona_output = process_file(monafile, monabin)
            formula = Formula(mona_output.split('\n')[-1])
            data = (str(formula.total_size)+"\n").encode()
            conn.sendall(data)
            print("{0}".format(formula.total_size))
        except subprocess.CalledProcessError as _:
            print("ERROR")
            conn.sendall("ERROR\n".encode())
        except OverflowError:
            conn.sendall("-1\n".encode())
        except ValueError:
            conn.sendall("-2\n".encode())
        #except KeyError:
        #    conn.sendall("-2\n".encode())


def parse_args(args):
    if len(sys.argv) != 2:
        help_err()
        sys.exit()
    return args[1]


def get_files(formulafolder):
    global FORMULAS
    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".mona")]
    files.sort()
    return files[:FORMULAS]


def process_file(filename, monabin):
    return subprocess.check_output([monabin, "-a", filename]).decode("utf-8")


def print_graph(filename, folder, suf, formula):
    base = os.path.basename(filename)
    name = os.path.splitext(base)[0]
    name = os.path.join(folder, name)
    graph = formula.to_graph(name)
    graph.render(filename=name, format="svg", cleanup=True)
    graph.save(filename=name + ".dot")


def create_leaf_node(graph, name, label, size, free_vars):
    graph.node(name, label=label + "\\n" + format_node(name, size, free_vars), tooltip=label)


def create_unary_node(graph, name, label, size, free_vars, child, operation):
    global MAX_LABEL
    label = label[:MAX_LABEL]
    graph.node(name, label=format_node(name, size, free_vars), tooltip=label)
    graph.edge(name, child, label=operation, arrowhead="none")


def create_binary_node(graph, name, label, size, free_vars, lchild, rchild, operation):
    global MAX_LABEL
    label = label[:MAX_LABEL]
    graph.node(name, label=format_node(name, size, free_vars), tooltip=label)
    graph.edge(name, lchild, label=graphviz.nohtml(operation), arrowhead="none")
    graph.edge(name, rchild, label=graphviz.nohtml(operation), arrowhead="none")


def format_node(name, size, free_vars):
    return size + " states\\n" + ','.join(free_vars) + "\\n" + name


def print_config():
    print("Number of formulas: {0}".format(FORMULAS))


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./predict.py " +
                     "[mona-bin]\n")


if __name__ == "__main__":
    main()
