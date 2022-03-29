#! python3

import os
import subprocess

scriptpath = os.path.realpath(__file__)
testpath = scriptpath[:scriptpath.rindex("/")] + "/test/hello_world/"
testfile = testpath + "hello_world.grp"

compile_command = "src/toplevel.native -c " + testfile + " | llc -relocation-model=pic | cc -o hello -xassembler -"
diff_command = "./hello | diff " + testpath + "hello_world.out -" 

try:
    diff_output = subprocess.check_output(compile_command + ";" + diff_command, shell=True, stderr=subprocess.STDOUT)
    if diff_output == b"":
        print("\u001b[32mhello world test success!\u001b[0m")
except subprocess.CalledProcessError as ex:
    print("\u001b[31mhello world test failure code [" + str(ex.returncode) + "]:\u001b[0m " + ex.output.decode("utf-8"))