#!/usr/bin/env python3

"""
 Script for automated collecting statistics about the formula construction.
 @title mona-stat.py
 @author Vojtech Havlena, July 2019
"""

import sys
import getopt
import subprocess
import string
import re
import os
import os.path
import resource

TIMEOUT = 300 #in seconds
FORMULAS = 20


def main():
    if len(sys.argv) < 3:
        help_err()
        sys.exit()

    monabin = sys.argv[1]
    formulafolder = sys.argv[2]

    try:
        opts, args = getopt.getopt(sys.argv[3:], "f:", ["formulas="])
    except getopt.GetoptError as err:
        help_err()
        sys.exit()
    FORMULAS = 20

    for o, a in opts:
        if o in ("-f", "--formulas"):
            FORMULAS = int(a)

    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".mona")]
    files.sort()
    files = files[:FORMULAS]

    print_config()

    for monafile in files:
        filename = os.path.join(formulafolder, monafile)
        try:
            mona_output = subprocess.check_output([monabin, "-i", filename], timeout=TIMEOUT).decode("utf-8")
            mona_parse = parse_mona(mona_output)
        except subprocess.TimeoutExpired:
            mona_parse = "TO"
        except subprocess.CalledProcessError as e:
            mona_parse = "None"
        print_output(filename, "", mona_parse)


def format_op(op, params):
    res = op
    for par in params:
        res = res + ";{0}".format(par)
    return res


def parse_mona(output):
    res = ""
    lines = output.split('\n')
    for i in range(len(lines)):
        line = lines[i]
        if line.startswith("Product &"):
            parse = proc_product(lines, i)
            res = res + "{0}\n".format(format_op("&", parse))
        if line.startswith("Product |"):
            parse = proc_product(lines, i)
            res = res + "{0}\n".format(format_op("|", parse))
        if line.startswith("Projecting"):
            parse = parse_mona_projection(lines[i+3:i+5])
            fv = dfa_fv(lines[i+6:])
            parse.append(','.join(fv))
            res = res + "{0}\n".format(format_op("proj", parse))
    return res


def proc_product(lines, i):
    parse = parse_mona_product(lines[i+3:i+5])
    j = i+6
    if parse is None:
        parse = parse_mona_product(lines[i+1:i+3])
        j = i+4
    fv = dfa_fv(lines[j:])
    parse.append(','.join(fv))
    return parse


def parse_mona_product(lines):
    res = [None]*4
    match = re.search("\\(([0-9]+),[0-9]+\\)x\\(([0-9]+),[0-9]+\\) -> \\(([0-9]+),[0-9]+\\)", lines[0])
    if match is None:
        return None
    res[0], res[1], res[2] = int(match.group(1)), int(match.group(2)), int(match.group(3))
    match = re.search("Minimizing \\([0-9]+,[0-9]+\\) -> \\(([0-9]+),[0-9]+\\)", lines[1])
    if match is None:
        return None
    res[3] = int(match.group(1))
    return res


def parse_mona_projection(lines):
    res = [None]*4
    match = re.search("\\(([0-9]+),[0-9]+\\) -> \\(([0-9]+),[0-9]+\\)", lines[0])
    res[0], res[1], res[2] = int(match.group(1)), -1, int(match.group(2))
    match = re.search("Minimizing \\([0-9]+,[0-9]+\\) -> \\(([0-9]+),[0-9]+\\)", lines[1])
    res[3] = int(match.group(1))
    return res


def dfa_fv(lines):
    fv = set()
    for line in lines[5:]:
        ret = parse_dfa_trans(line)
        if ret is None:
            break
        _, sym, _ = ret
        fv = fv.union(symbols_free_vars(sym))
    return fv


def parse_dfa_trans(line):
    match = re.search("^State ([0-9]+): ([^->]*) -> state ([0-9]+)$", line)
    if match is None:
        return None
    fr, label, to = int(match.group(1)), match.group(2), match.group(3)
    if label.strip() == "":
        syms = []
    else:
        syms = label.split(", ")
    return fr, syms, to


def symbols_free_vars(syms):
    fv = set()
    for sym in syms:
        fv.add(sym.split("=")[0])
    return fv


def print_config():
    print("Timeout: {0}".format(TIMEOUT))
    print("Number of formulas: {0}".format(FORMULAS))


def print_output(filename, suf, output):
    base = os.path.basename(filename)
    name = os.path.splitext(base)[0]
    output = "operation;operand1;operand2;result;minresult;fv\n" + output
    f = open(name + suf + ".csv", "w")
    f.write(output)
    f.close()


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./mona-stat.py [mona-bin] [formula folder]\n")


if __name__ == "__main__":
    main()
