#! /bin/python3

import os
import sys
import time
import subprocess
import re
import csv

try:
    if sys.argv[1] == "--debug":
        debug = ["--debug",  "1"]  
    else:
        print("Could not parse arguments")
        exit(1)
except IndexError:
    debug = []

suffixlen = len("s_part.smt2")

projDir = os.getcwd() + "/.."
path_to_tests = projDir + "/bench/tasks"
tests_set = set()
for file in os.listdir(path_to_tests):
    testName = path_to_tests + '/' + file[:-suffixlen]
    tests_set.add(testName)

resTable = [["test", "stdout", "time"]]

numTests = len(tests_set)
i = 1
for t in tests_set:
    print(f"Test {i}/{numTests}")
    result = [t]
    args = [projDir + "/build/tools/aeval/aeval"] + debug + [t + "s_part.smt2", t + "t_part.smt2"]
    t1 = time.time()
    try:
        output = subprocess.run(args, timeout=300, stdout=subprocess.PIPE)
        output = output.stdout
        t2 = time.time()
        if output:
            output = output.decode("utf-8").strip()
            result.append(output)
        else:
            result.append("emptyStdout")
        result.append(t2-t1)
    except Exception as e:
        result.append(e)
    i += 1
    resTable.append(result)

with open("example.csv", 'w') as file:
    writer = csv.writer(file)
    writer.writerows(resTable)
