# mc-2020

Repository with source code of **mcTw** solver - submission to Model Counting problem of MC 2020 competition.<br>

mcTw calculates number of models of given cnf formula. The algorthm is mainly based on dynamic programming on treewidth decomposition of primal and dual graph of given formula, just as described in [[Samer, Szeider]](https://doi.org/10.1016/j.jda.2009.06.002)<br>
Algorithm tries to find solution based on decomposition of primal graph. If the treewidth of any component of that graph is larger than 24, then it branches: two variables are selected - one variable that occurs in largest number of binary clauses (or ternary if there are no binary. If there are no binary and ternary clauses then node is not selected that way) and one variable for which corresponding node in primal graph maximizes sum of squares of bags' sizes of the treewidth decomposition, to which that node belongs. Then for each 4 possible assignments, algorithm runs recursively.<br>

Dynamic programming on decomposition of dual graph is implemented but not used (it occurs to be much slower than for primal graphs).<br>

Treewidth is found using flow cutter algorithm ([link here](https://github.com/ben-strasser/flow-cutter-pace16)).

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