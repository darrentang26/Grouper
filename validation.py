#! python3

import os
import subprocess

scriptpath = os.path.realpath(__file__)
testpath = scriptpath[:scriptpath.rindex("/")] + "/test/scanner_parser/"

for file in os.listdir(testpath):
    if file.startswith("pass") and file.endswith(".grp"):
        try:
            output_file = file[:file.rindex(".")] + ".out"
            output_diff = subprocess.check_output("src/toplevel.native " + testpath + file + " | diff " + testpath + output_file + " -", shell=True, stderr=subprocess.STDOUT)
            if output_diff != b"":
                print("\u001b[31mtest failure in " + file + ": diff failure\u001b[0m")
                print("diff output:" + output_diff.decode("utf-8"))
            else:
                print("\u001b[32mtest success in " + file + "\u001b[0m")
        except:
            print("\u001b[31mtest failure in " + file + ": parsing error\u001b[0m")
    if file.startswith("fail") and file.endswith(".grp"):
        try:
            output = subprocess.check_output("src/toplevel.native " + testpath + file, shell=True, stderr=subprocess.STDOUT)
            # print(output)
            print("\u001b[31munexpected success ocurred in " + file + "\u001b[0m")
        except:
            print("\u001b[32mexpected failure ocurred in " + file + "\u001b[0m")
