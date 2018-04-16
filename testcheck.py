#!/usr/bin/env python3

import sys
import subprocess
import string
import re
import os
import os.path

def main():
    if len(sys.argv) != 3:
        sys.stderr.write("Bad input arguments.\n")
        sys.exit()

    program = sys.argv[1]
    formulafolder = sys.argv[2]

    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".mona")]

    for monafile in files:
        filename = os.path.join(formulafolder, monafile)
        program_output = subprocess.check_output([program, filename]).decode()
        lines = program_output.split('\n')
        lines = list(filter(None, lines)) #Remove empty lines
        valid = file_formula_valid(filename)
        if (lines[-1] == "True" and valid) or (lines[-1] == "False" and not valid):
            print("Correct: {0}".format(monafile))
        else:
            print("Fail: {0}".format(monafile))


def parse_validity(content):
    p = re.compile(r'^#\s*Validity:\s*(?P<valid>\w*)')
    lines = content.split('\n')
    for line in lines:
        mobject = p.match(line)
        if mobject is not None:
            if mobject.group("valid").startswith("valid"):
                return True
            return False


def file_formula_valid(filename):
    try:
        handler = open(filename, "r")
    except IOError:
        sys.stderr("Could not open MONA formula file.")
        return False

    content = handler.read()
    handler.close()
    return parse_validity(content)



if __name__ == "__main__":
    main()
