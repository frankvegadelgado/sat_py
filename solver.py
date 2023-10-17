#                          SAT Solver
#                          Frank Vega
#                        October 17, 2023
#        We use Z3 that is a theorem prover from Microsoft Research.

import argparse
import sys
import z3
import time
z3.set_option(model=True)
z3.set_param("parallel.enable", False)
k = 0
dummy = 0
mapped = {}

log = False
timed = False
started = 0.0


def logging(message):
    if log:
        print(message)
    
def Fsat_to_3sat(clauses):
    global mapped, k, dummy
    s = dummy + 1
    reduced = []
    for l in clauses:
        C = list(set(l))
        if len(C) == 1:
            reduced.append([C[0], dummy, dummy])
        elif len(C) == 2:
            reduced.append([C[0], C[1], dummy])
        elif len(C) == 3:
            reduced.append(C)
        elif len(C) > 3:
            if len(C) > 0:
                B = C
                while True:
                    A = B[:2]
                    B = B[2:]
                    A.append(s)
                    B.append(-s)
                    mapped[s] = k
                    k += 1
                    s += 1
                    reduced.append(A)
                    if len(B) == 3:
                        break
                reduced.append(B)
    return reduced 
        
def polynomial_time_reduction(clauses):
    global mapped, dummy
    logging("Start building the conditional formula")
    if timed:
        started = time.time()

    # Build the conditional formula  
    s = z3.Solver()
    smt2 = [ ('(declare-fun |%s| () Bool)' % i) for i in range(len(mapped)) ]
    smt2.append('(assert')
    smt2.append(' (not |%s|))' % (mapped[dummy]))
    for list in clauses:
        smt2.append('(assert')
        v = '(not |%s|)' % (mapped[-list[0]]) if (list[0] < 0) else '|%s|' % mapped[list[0]]
        w = '(not |%s|)' % (mapped[-list[1]]) if (list[1] < 0) else '|%s|' % mapped[list[1]]
        z = '(not |%s|)' % (mapped[-list[2]]) if (list[2] < 0) else '|%s|' % mapped[list[2]]
        smt2.append(' (ite (or %s %s) true %s))' % (v, w, z))
    if timed:
        logging(f"Done building the conditional formula in: {(time.time() - started) * 1000.0} milliseconds")
    else:
        logging("Done building the conditional formula")
    smt2.append('(check-sat)')
    s.from_string("%s" % '\n'.join(smt2))    
    return s
    
def solve_conditional_formula(s):
    global mapped, dummy
    logging("Start solving the conditional formula")  
    if timed:
        started = time.time()
    
    #Solve the conditional formula
    result = s.check()

    if timed:
        logging(f"Done solving the conditional formula in: {(time.time() - started) * 1000.0} milliseconds")
    else:
        logging("Done solving the conditional formula")

    if result == z3.unsat:
        print("s UNSATISFIABLE")
    elif result == z3.unknown:
        print("s UNKNOWN")
    else:
        m = s.model()
        print("s SATISFIABLE")
        sys.stdout.write("v ")
        inv_mapped = {}
        for key in mapped:
            inv_mapped[mapped[key]] = key
        for d in m.decls():
            v = int(d.name())
            if inv_mapped[v] < dummy:
                value = ('%s' % m[d])
                if value == 'False': 
                    sys.stdout.write("-%s " % (inv_mapped[v]))
                else:
                    sys.stdout.write("%s " % (inv_mapped[v]))
        print("0")
        
def parse_dimacs(asserts):
    global mapped, k, dummy
    result = []
    for strvar in asserts:
        line = strvar.strip()
        if not line.startswith('p') and not line.startswith('c'):
            expr = line.split(" ")
            expr = expr[:-1]
            l = []
            for t in expr:
                v = int(t)
                l.append(v)
                value = abs(v)
                if value not in mapped:
                    mapped[value] = k
                    k += 1
                    dummy = value if (dummy < value) else dummy
            result.append(l)        
    return result   
                       
if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Solve an NP-complete problem from a DIMACS file.')
    parser.add_argument('-i', '--inputFile', type=str, help='Input file path', required=True)
    parser.add_argument('-v', '--verbose', action='store_true', help='Enable verbose output')
    parser.add_argument('-t', '--timer', action='store_true', help='Enable timer output')
    
    args = parser.parse_args()

    log = args.verbose
    timed = args.timer

    #Read and parse a dimacs file
    logging("Pre-processing started")
    if timed:
        started = time.time()

    file = open(args.inputFile, 'r')
    #Format from dimacs
    asserts = file.readlines()    
    original = parse_dimacs(asserts[1:])
    dummy += 1
    mapped[dummy] = k
    k += 1
    clauses = Fsat_to_3sat(original)
    if timed:
        logging(f"Pre-processing done in: {(time.time() - started) * 1000.0} milliseconds")
    else:
        logging("Pre-processing done")
    # Polynomial Time Reduction from 3SAT to 2SAT Conditional
    reduction = polynomial_time_reduction(clauses)
    # Solve 2SAT Conditional in Polynomial Time
    solution = solve_conditional_formula(reduction)