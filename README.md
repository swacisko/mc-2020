# mc-2020

Repository with source code of **mcTw** solver - submission to Model Counting problem of MC 2020 competition.<br>

mcTw calculates number of models of given CNF formula. The algorthm is mainly based on dynamic programming on treewidth decomposition of primal graph of given formula, just as described in [[Samer, Szeider]](https://doi.org/10.1016/j.jda.2009.06.002)<br>

**Short description:**

Algorithm tries to find solution based on decomposition of primal graph. Each connected component of primal graph is treated separately. For given connected graph some preprocessing is done - removing clauses containing both x and 'not x' and setting values of variables that occur is singular clauses - procedure is repeated until no further reduction can be made. If the treewidth of the graph is larger than 23, then branching is applied. First, a set of candidate variables is selected. That set contains all variables that occur in binary clauses and all variables that occur in any of the largest bags of current treewidth decomposition. Each candidate variable is checked using described preprocessing method. As branching node is chosen the one corresponding to such variable which, when set to true or false, reduces maximally treewidth of the current graph. Then for each 2 possible values of the chosen variable algorithm runs recursively.<br>

Dynamic programming on decomposition of dual graph is also implemented, but it is not used (it occurs to be much slower than for primal graphs).<br>

Treewidth is found using FlowCutter algorithm ([link here](https://github.com/ben-strasser/flow-cutter-pace16)).

<br>


**Requirements**:

CMake VERSION 3.10.2 or higher<br>
c++ 17 or higher

<br>

**Installation**:

Use cmake to obtain a binary file, e.g. in linux in the main directory (mc-2020) you can use the following commands:

mkdir build<br>
cd build<br>
cmake ..<br>
make

After this, the executable file named "mcTw" should be in the "build" directory

<br>

**Usage:**

Given a cnf formula in a file example_input.cnf, you can run mcTw in the following way
 
./mcTw < example_input.cnf > example_output.out