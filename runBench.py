import subprocess
import re

TEST_DIR = "testcase/"
BINARY_PATH = "bin/fptSynthesizer.bc"

# 一先ず
BENCHMARKS =[
             ('listDelete.spec',['-p', '2', '-e', '7']),
             ('listAppend.spec',['-p', '2', '-e', '7']),
             ('rep.spec',['-p', '2', '-e', '7']),
             ('sum.spec',['-p', '2', '-e', '7']),
             ('accSum.spec',['-p', '2', '-e', '5']),
             ('sumList.spec',['-p', '2', '-e', '5']),
             ('fib.spec', ['-p', '1', '-e', '7']),
             ('tfib.spec', ['-p', '1', '-e', '5']),
             ('memofib.spec', ['-p', '2', '-e', '5'])
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

def extract_solver_time(proc_stdout):
    matchObj = re.search(r'z3 time:(.*)',proc_stdout)
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
    print(proc_stdout)
    if is_success(proc_stdout):
        time = extract_time(proc_stdout)
        solver_time = extract_solver_time(proc_stdout)
        return {"total":time, "solver":solver_time}
    else:
        return None
        
    
def print_result(result):
    if result["time"]:
        print("%s:  %s    %s" %(result["name"],
                                result["time"]["total"],
                                result["time"]["solver"]) )
    else:
        print("%s:  TIMEOUT" %result[name] )

def print_result_list(results_list):
    for result in results_list:
        print_result(result)
        
            
def runBenchmarks(benchmarks):
    result_list = []
    for (bench, args) in benchmarks:
        time_of_bench = runSynthesizer(bench, args)
        if time_of_bench:
            result =  {"name":bench,"time":time_of_bench}
        else:
            result =  {"name":bench,"time":None}

        print_result(result)
        result_list.append( result)
        
    print("--------------------------------------------------")
    print("benchmark end")
    print_result_list(result_list)

        
if __name__ == '__main__':
    runBenchmarks(BENCHMARKS)





