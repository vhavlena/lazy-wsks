#!/usr/bin/env python3

"""
 Script for automated experimental evaluation.
 @title experimental.py
 @author Vojtech Havlena, June 2018
"""

import sys
import getopt
import subprocess
import string
import re
import os
import os.path
import resource

VALIDLINE = -2
TIMELINE = -1
TIMEOUT = 100 #in seconds
FORMULAS = 5

def main():
    #Input parsing
    if len(sys.argv) < 4:
        help_err()
        sys.exit()
    try:
        opts, args = getopt.getopt(sys.argv[4:], "t", ["tex"])
    except getopt.GetoptError as err:
        help_err()
        sys.exit()

    lazybin = sys.argv[1]
    monabin = sys.argv[2]
    formulafolder = sys.argv[3]
    texout = False

    for o, a in opts:
        if o in ("-t", "--tex"):
            texout = True

    #Experiments

    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".mona")]
    files.sort()
    files = files[:FORMULAS]
    tex = "Timeout: {0}\n".format(TIMEOUT)
    tex += "\\begin{table}[h]\n\\begin{tabular}{lll}\n"
    tex += "\\textbf{Formula File} & \\textbf{Lazy Approach} & \\textbf{Mona} \\\\\n\\toprule \n"

    print_config()
    print("Formula: lazy approach, MONA")

    for monafile in files:
        filename = os.path.join(formulafolder, monafile)

        try:
            lazy_output = subprocess.check_output([lazybin, filename], \
                timeout=TIMEOUT).decode("utf-8")
            lazy_parse = parse_lazy(lazy_output)
        except subprocess.TimeoutExpired:
            lazy_parse = None, None
        try:
            mona_output = subprocess.check_output([monabin, filename], \
                timeout=TIMEOUT).decode("utf-8")
            mona_parse = parse_mona(mona_output)
        except subprocess.TimeoutExpired:
            mona_parse = None, None
        except subprocess.CalledProcessError as e:
            mona_parse = None, None

        print_output(filename, lazy_parse, mona_parse)
        tex = tex + "\\emph{{{0}}} & {1} & {2} \\\\\n\\midrule\n".format(filename, \
            format_output(lazy_parse), format_output(mona_parse))

    tex += "\\end{tabular}\n\\end{table}"
    if texout:
        print(tex)


def parse_lazy(output):
    lines = output.split('\n')
    lines = list(filter(None, lines)) #Remove empty lines
    valid = lines[VALIDLINE] == "True"
    match = re.search("Time: ([0-9]+.[0-9]+)s", lines[TIMELINE])
    time = round(float(match.group(1)), 2)
    return valid, time


def parse_mona(output):
    valid = None
    time = None
    for line in output.split('\n'):
        out = parse_mona_sat(line)
        if out is not None:
            valid = out
        out = parse_mona_time(line)
        if out is not None:
            time = out
    return valid, time


def parse_mona_sat(line):
    match = re.search("Formula is unsatisfiable", line)
    if match is not None:
        return False
    match = re.search("A satisfying example", line)
    if match is not None:
        return True
    return None


def parse_mona_time(line):
    match = re.search("Time: ([0-9][0-9]):([0-9][0-9]):([0-9][0-9].[0-9][0-9])", line)
    if match is not None:
        time = 3600*float(match.group(1)) + 60*float(match.group(2)) + float(match.group(3))
        return time
    return None


def print_config():
    print("Timeout: {0}".format(TIMEOUT))
    print("Number of formulas: {0}".format(FORMULAS))


def format_output(parse):
    return "{0} {1}".format("N/A" if parse[0] is None else parse[0], "TO" if parse[1] is None else parse[1])


def print_output(filename, lazy_parse, mona_parse):
    print("{0}: {1}\t {2}".format(filename, format_output(lazy_parse), format_output(mona_parse)))


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./experimental [lazy-bin] [mona-bin] [formula folder] [--tex]\n")


if __name__ == "__main__":
    main()
