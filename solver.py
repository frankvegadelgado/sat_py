#                          SAT Solver
#                          Frank Vega
#                        October 16, 2023
#        We use Z3 that is a theorem prover from Microsoft Research.

import argparse
import sys
import z3
import time
z3.set_option(model=True)
z3.set_param("parallel.enable", False)
log = False
timed = False
started = 0.0


def logging(message):
    if log:
        print(message)
    
def Fsat_to_3sat(clauses, total):
    new_clauses = []
    added = total
    dummy = added + 1
    added += 1
                    
    for l in clauses:
        C = list(set(l))
        if len(C) == 1:
            new_clauses.append([C[0], dummy, dummy])
        elif len(C) == 2:
            new_clauses.append([C[0], C[1], dummy])
        elif len(C) == 3:
            new_clauses.append(C)
        elif len(C) > 3:
            if len(C) > 0:
                B = C
                while True:
                    A = B[:2]
                    B = B[2:]
                    v = added+1
                    A.append(v)
                    B.append(-v)
                    added += 1
                    new_clauses.append(A)
                    if len(B) == 3:
                        break
                new_clauses.append(B)
    return (new_clauses, added) 
    
        

        
def polynomial_time_reduction(clauses, init, total):
    
    logging("Start building the linear system")
    if timed:
        started = time.time()

    # Build the linear system  
    s = z3.Solver()
    x = [ z3.Bool('%s' % (i + 1)) for i in range(total) ]
    s.add(z3.Not(x[init]))    
    for list in clauses:
        a = z3.Not(x[-list[0]-1]) if (list[0] < 0) else x[list[0]-1]
        b = z3.Not(x[-list[1]-1]) if (list[1] < 0) else x[list[1]-1]
        c = z3.Not(x[-list[2]-1]) if (list[2] < 0) else x[list[2]-1]
        s.add(z3.If(z3.Or(a, b), z3.BoolVal(True), c))
    if timed:
        logging(f"Done building the linear system in: {(time.time() - started) * 1000.0} milliseconds")
    else:
        logging("Done building the linear system")
    return s
    
def solve_linear_system(s, init):

    logging("Start solving the linear system")  
    if timed:
        started = time.time()
    
    #Solve the linear system
    result = s.check()

    if timed:
        logging(f"Done solving the linear system in: {(time.time() - started) * 1000.0} milliseconds")
    else:
        logging("Done solving the linear system")

    if result == z3.unsat:
        print("s UNSATISFIABLE")
        return []
    elif result == z3.unknown:
        print("s UNKNOWN")
        return []
    else:
        m = s.model()
        sol = []
        for d in m.decls():
            v = int(d.name())
            if v <= init:
                value = ('%s' % m[d])
                if value == 'False': 
                    sol.append(-v)
                else:
                    sol.append(v)
        return sol
        
def parse_dimacs(asserts):
    result = []
    for strvar in asserts:
        expr = strvar.split(" ")
        expr = expr[:-1]
        l = []
        for t in expr:
            v = int(t)
            l.append(v)
        result.append(l)        
    return result   
                       
if __name__ == "__main__":

    parser = argparse.ArgumentParser(description='Solve an NP-complete problem from a DIMACS file.')
    parser.add_argument('-i', '--inputFile', type=str, help='Input file path', required=True)
    parser.add_argument('-v', '--verbose', action='store_true', help='Enable verbose output')
    parser.add_argument('-t', '--timer', action='store_true', help='Enable timer output')
    parser.add_argument('-c', '--satSolution', action='store_true', help='check the SAT solution')
    
    args = parser.parse_args()

    log = args.verbose
    timed = args.timer

    #Read and parse a dimacs file
    logging("Pre-processing started")
    if timed:
        started = time.time()

    reader = z3.Solver()
    reader.from_file(args.inputFile)
    #Format from dimacs
    asserts = reader.dimacs().splitlines()
    reader.reset()
    total = int(asserts[0].split(' ')[2])
    original = parse_dimacs(asserts[1:])

    init = total
    (clauses, total) = Fsat_to_3sat(original, total)
    if timed:
        logging(f"Pre-processing done in: {(time.time() - started) * 1000.0} milliseconds")
    else:
        logging("Pre-processing done")
    # Polynomial Time Reduction from 3SAT to 2SAT Conditional
    reduction = polynomial_time_reduction(clauses, init, total)
    # Solve 2SAT Conditional
    solution = solve_linear_system(reduction, init)
    if len(solution) > 0:
        truth = True
        if args.satSolution:
            logging("Checking the solution")
            for list in original:
                truth = False
                for z in list:
                    truth = z in solution
                    if truth == True:
                        break
                if truth == False:
                    print("s UNSATISFIABLE")
                    break
        if truth == True:
            print("s SATISFIABLE")
            sys.stdout.write("v ")
            for w in solution:
                sys.stdout.write("%s " % w)
            print("0")