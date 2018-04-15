#!/usr/bin/env python3

import sys
import subprocess
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
        subprocess.call([program, os.path.join(formulafolder, monafile)])


if __name__ == "__main__":
    main()
