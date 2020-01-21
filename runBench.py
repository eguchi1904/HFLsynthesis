import subprocess
import re

TEST_DIR = "testcase/"
BINARY_PATH = "bin/fptSynthesizer.bc"

BENCHMARKS =[('fib.spec', ['-p', '1', '-e', '7']),
             ('tfib.spec', ['-p', '1', '-e', '5']),
             ]


def is_success(proc_stdout):
    return proc_stdout.find("SUCSESS")

def extract_time(proc_stdout):
    matchObj = re.search(r'time:(.*)',proc_stdout)
    if matchObj:
        time =matchObj.group(1) 
        return time
    else:
        raise Exception("extract_time")

def runSynthesizer(name, args):
    proc = subprocess.run(['dune', 'exec', '--',
                    BINARY_PATH,
                    TEST_DIR + name]
                    + args,
                    stdout = subprocess.PIPE,
                    stderr = subprocess.PIPE
                             )

    proc_stdout = proc.stdout.decode("utf8")
    if is_success(proc_stdout):
        time = extract_time(proc_stdout)
        return time
    else:
        return None
        
    
def print_result(results_list):
    for result in results_list:
        if result["time"]:
            print("%s:  %s" %(result["name"], result["time"]) )
        else:
            print("%s:  TIMEOUT" %result[name] )
            
def runBenchmarks(benchmarks):
    result_list = []
    for (bench, args) in benchmarks:
        time_of_bench = runSynthesizer(bench, args)
        if time_of_bench:
            result_list.append( {"name":bench,"time":time_of_bench})
        else:
            result_list.append( {"name":bench,"time":None})                

    print_result(result_list)

        
if __name__ == '__main__':
    runBenchmarks(BENCHMARKS)





