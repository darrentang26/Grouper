#! python3

import os
import subprocess

scriptpath = os.path.realpath(__file__)
testpath = scriptpath[:scriptpath.rindex("/")] + "/test/e2e/"

for file in os.listdir(testpath):
    if file.endswith(".fail.grp"):
        output_file = file[:file.rindex(".")] + ".out"
        compilation = subprocess.run(args="src/toplevel.native -l " + testpath + file + " 2> error.out", shell=True)
        diff = subprocess.run(args="diff " + testpath + output_file + " error.out", shell=True, capture_output=True)
        if diff.returncode != 0:
            print("\u001b[31m" + file + " failed to validate (output mismatch)\u001b[0m")
        else:
            print("\u001b[32m" + file + " validated (negative test failed with correct output)\u001b[0m")

    
    elif file.endswith(".grp"):
        output_file = file[:file.rindex(".")] + ".out"
        compilation = subprocess.run(args="src/toplevel.native -c " + testpath + file + " | llc -relocation-model=pic | cc -o out -xassembler -", shell=True, capture_output=True)
        if compilation.returncode != 0:
            print("\u001b[31m" + file + " failed to validate (compilation error in positive test)\u001b[0m")
        else:
            execution = subprocess.run(args="./out | diff " + testpath + output_file + " -", shell=True, capture_output=True)
            if execution.returncode != 0:
                print("\u001b[31m" + file + " failed to validate (output mismatch)\u001b[0m")
            else:
                print("\u001b[32m" + file + " validated (positive test passed)\u001b[0m")
                        
            


    # if file.startswith("fail") and file.endswith(".grp"):
    #     try:
    #         output = subprocess.check_output("src/toplevel.native -a " + testpath + file, shell=True, stderr=subprocess.STDOUT)
    #         # print(output)
    #         print("\u001b[31munexpected success ocurred in " + file + "\u001b[0m")
    #     except:
    #         print("\u001b[32mexpected failure ocurred in " + file + "\u001b[0m")
