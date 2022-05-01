#!usr/bin/python3

# Script that essentially copies and pastes
# the Grouper standard library into a specified
# Grouper source code file before compiling
import os, sys

def main():
    tmp_path = "tmp/tmpsrc.grp" 
    stdlib_path = "stdlib.grp"
    tmp_file = open(tmp_path, "w+")
    stdlib_file = open(stdlib_path, "r")
    src_file = open(sys.argv[1], "r")
    type_decls, prog = [], []
    std_lines = stdlib_file.readlines()
    src_lines = src_file.readlines()
    for line in std_lines:
        if line[:3] == "typ":
            type_decls.append(line)
        elif line[:2] != "(*":
            prog.append(line) 
    for line in src_lines:
        if line[:3] == "typ":
            type_decls.append(line)
        elif line[:2] != "(*":
            prog.append(line) 
    tmp_file.writelines(type_decls)
    tmp_file.writelines(prog)

if __name__ == "__main__":
    main()