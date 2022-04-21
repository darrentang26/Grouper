#! python3

import os
import subprocess

scriptpath = os.path.realpath(__file__)
testpath = scriptpath[:scriptpath.rindex("/")] + "/test/e2e/"

for file in os.listdir(testpath):
    if file.endswith(".grp"):
        try:
            output_file = file[:file.rindex(".")] + ".out"
            compilation_return_code = subprocess.call("src/toplevel.native -c " + testpath + file " > llvm.out", shell=True)
            if compilation_return_code != 0:
                print("\u001b[31compilation failure in " + file + "\u001b[0m")
            else:
                subprocess.call("llc -relocation-model=pic llvm.out | cc -o out -xassembler -")
        except:
            print("\u001b[31mtest failure in " + file + ": parsing error\u001b[0m")
    if file.startswith("fail") and file.endswith(".grp"):
        try:
            output = subprocess.check_output("src/toplevel.native -a " + testpath + file, shell=True, stderr=subprocess.STDOUT)
            # print(output)
            print("\u001b[31munexpected success ocurred in " + file + "\u001b[0m")
        except:
            print("\u001b[32mexpected failure ocurred in " + file + "\u001b[0m")
