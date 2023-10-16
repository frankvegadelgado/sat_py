# SAT PY
SAT
----- 
Instance: A Boolean formula $\phi$ in CNF.

Question: Is $\phi$ satisfiable?
 
**Note: This problem is NP-complete (If any NP-complete can be solved in polynomial time, then $P = NP$)**.

# Theory

- A literal in a Boolean formula is an occurrence of a variable or its negation. A Boolean formula is in conjunctive normal form, or CNF, if it is expressed as an AND of clauses, each of which is the OR of one or more literals. 

- A truth assignment for a Boolean formula $\phi$ is a set of values for the variables in $\phi$. A satisfying truth assignment is a truth assignment that causes $\phi$ to be evaluated as true. A Boolean formula with a satisfying truth assignment is satisfiable. The problem SAT asks whether a given Boolean formula $\phi$ in CNF is satisfiable.

Example
----- 

Instance: The Boolean formula $(x_{1} \vee \rightharpoondown x_{3} \vee \rightharpoondown x_{2}) \wedge (x_{3} \vee x_{2} \vee x_{4})$ where $\vee$ (OR), $\wedge$ (AND) and $\rightharpoondown$ (NEGATION) are the logic operations.

Answer: Satisfiable (the formula is satisfiable when we assign simultaneously the variables $x_{1}$ and $x_{3}$ as true to obtain a satisfying truth assignment).

Input of this project
-----

The input is on [DIMACS](http://www.satcompetition.org/2009/format-benchmarks2009.html) formula with the extension .cnf.
  
The **file.cnf** on DIMACS format for $(x_{1} \vee \rightharpoondown x_{3} \vee \rightharpoondown x_{2}) \wedge (x_{3} \vee x_{2} \vee x_{4})$ is
```  
p cnf 4 2
1 -3 -2 0
3 2 4 0
```  

- The first line **p cnf 4 2** means there are 4 variables and 2 clauses.

- The second line **1 -3 -2 0** means the clause $(x_{1} \vee \rightharpoondown x_{3} \vee \rightharpoondown x_{2})$ (Note that, the number *0* means the end of the clause).

- The third line **3 2 4 0** means the clause $(x_{3} \vee x_{2} \vee x_{4})$ (Note that, the number *0* means the end of the clause).

# Compile and Environment

Downloading and Installing
-----

Install at least Python 2.7 or a greater version until 3.10

Download and Install the following Number Theory Library 

- Z3 is a theorem prover from Microsoft Research with support for bitvectors, booleans, arrays, floating point numbers, strings, and other data types.

If you use pip, you can install Z3 with:
-----
```
pip install z3-solver
```

-----

# Build and Execute

To build and run from the command prompt:

```
git clone https://github.com/frankvegadelgado/sat_py.git
cd sat-py
```

On sat-py directory run

```
python solver.py -i file.cnf
```

Finally, it would obtain in the console output:

```
s SATISFIABLE
v 4 2 3 1 0
```

# Command Options

On the same input we can run the options

```
python solver.py -i file.cnf -v
```

It would obtain a more verbose in the console output:

```
Pre-processing started
Pre-processing done
Start building the linear system
Done building the linear system
Start solving the linear system
Done solving the linear system
s SATISFIABLE
v 4 2 3 1 0
```

and the next option 

```
python solver.py -i file.cnf -v -c
```

It would check the given solution when the formula is satisfiable:

```
Pre-processing started
Pre-processing done
Start building the linear system
Done building the linear system
Start solving the linear system
Done solving the linear system
Checking the solution
s SATISFIABLE
v 4 2 3 1 0
```

and the final option

```
python solver.py -i file.cnf -v -t
```

It would obtain a more verbose in the console output measuring the elapsed time:

```
Pre-processing started
Pre-processing done in: 6.622076034545898 milliseconds
Start building the linear system
Done building the linear system in: 15.730142593383789 milliseconds
Start solving the linear system
Done solving the linear system in: 15.53964614868164 milliseconds
s SATISFIABLE
v 4 2 3 1 0
```


# **SAT Benchmarks** 

We can run the DIMACS files with the extension .cnf in the simplest benchmarks folder:

```
>  python solver.py -i .\bin\simplest\aim-50-1_6-yes1-1.cnf
s SATISFIABLE
v -1 2 3 -4 -5 -6 7 8 9 -10 -11 -12 -13 14 -15 -16 17 18 19 20 21 22 23 24 -25 26 27 28 -29 30 31 -32 -33 -34 35 36 -37 38 39 40 41 42 43 -44 -45 46 -47 48 -49 -50 0
```

and

```
> python solver.py -i .\bin\simplest\aim-50-1_6-no-1.cnf
s UNSATISFIABLE
```

- We run each script and output the solutions for the satisfiable formulas.

We obtain this result since those files were copied into the directory sat-py\bin\simplest:

```
aim-50-1_6-yes1-1.cnf
aim-50-1_6-no-1.cnf
```

from this well-known dataset [SAT Benchmarks](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/AIM/descr.html). 

# Code

- Python code by **Frank Vega**.

# Complexity

````diff
+ We reduce SAT to a Linear System of Constraints in homogeneous quadratic time.
+ The quadratic optimization with real variables can be solved in polynomial time.
````
 
# License
- MIT.