#!/usr/bin/env python3

"""
 Script for automated experimental evaluation.
 @title experimental-prenex.py
 @author Vojtech Havlena, October 2018
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
FORMULAS = 20

PREPROFILE = "test-wgjcm3.mona"
ANTIPREFILE = "test-wgjcm4.mona"

def main():
    if len(sys.argv) < 4:
        help_err()
        sys.exit()

    lazybin = sys.argv[1]
    monabin = sys.argv[2]
    formulafolder = sys.argv[3]

    try:
        opts, args = getopt.getopt(sys.argv[4:], "tf:", ["tex", "formulas="])
    except getopt.GetoptError as err:
        help_err()
        sys.exit()

    texout = False
    FORMULAS = 20

    for o, a in opts:
        if o in ("-t", "--tex"):
            texout = True
        if o in ("-f", "--formulas"):
            FORMULAS = int(a)

    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".mona")]
    files.sort()
    files = files[:FORMULAS]

    print_config()
    print("Formula: MONA, MONA+antiprenex")
    tex = "Timeout: {0}\n".format(TIMEOUT)
    tex += "\\begin{table}[h]\n\\begin{tabular}{llll}\n"
    tex += "\\textbf{Formula File} & \\textbf{Mona} & \\textbf{Mona+antiprenex} \\\\\n\\toprule \n"


    for monafile in files:
        filename = os.path.join(formulafolder, monafile)

        try:
            anti_time = prenex_file(PREPROFILE, [lazybin, filename, "-w"])
            mona_output = subprocess.check_output([monabin, PREPROFILE], timeout=TIMEOUT).decode("utf-8")
            mona_parse = parse_mona(mona_output)
            os.remove(PREPROFILE)
        except subprocess.TimeoutExpired:
            mona_parse = None, None
        except subprocess.CalledProcessError as e:
            mona_parse = None, None

        try:
            anti_time = prenex_file(ANTIPREFILE, [lazybin, filename])
            mona_output_anti = subprocess.check_output([monabin, ANTIPREFILE], timeout=TIMEOUT).decode("utf-8")
            mona_parse_anti = parse_mona(mona_output_anti)
            os.remove(ANTIPREFILE)
        except subprocess.TimeoutExpired:
            mona_parse_anti = None, None, None
        except subprocess.CalledProcessError as e:
            mona_parse_anti = None, None, None

        if mona_parse_anti[1] is None:
            mona_parse_anti = mona_parse_anti[0], None, None
        else:
            mona_parse_anti = mona_parse_anti[0], round(mona_parse_anti[1], 2), round(anti_time, 2)
        print_output(filename, mona_parse, mona_parse_anti)
        tex = tex + "\\emph{{{0}}} & {1} & {2} \\\\\n".format(filename, \
            format_output(mona_parse), format_output_anti(mona_parse_anti))

    tex += "\\end{tabular}\n\\end{table}"
    if texout:
        print(tex)


def prenex_file(store, input):
    f = open(store, "w")
    output_anti = subprocess.check_output(input, timeout=TIMEOUT).decode("utf-8")
    anti_fle, anti_time = parse_prenex(output_anti)
    f.write(anti_fle)
    f.close()
    return anti_time


def parse_prenex(output):
    lines = output.split('\n')
    lines = list(filter(None, lines)) #Remove empty lines
    match = re.search("Time: ([0-9]+.[0-9]+)s", lines[TIMELINE])
    formula = "\n".join(lines[:-1])
    time = float(match.group(1))
    return formula, time


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
    return "{0}".format("TO" if parse[1] is None else parse[1])


def format_output_anti(parse):
    return "{0}({1})".format("TO" if parse[1] is None else parse[1], "TO" if parse[2] is None else parse[2])


def print_output(filename, lazy_parse, mona_parse):
    print("{0}: {1}\t {2}".format(filename, format_output(lazy_parse), format_output_anti(mona_parse)))


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./experimental-prenex [lazy-bin]  [mona-bin] [formula folder]\n")


if __name__ == "__main__":
    main()
