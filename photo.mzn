/*
In this mandatory assignment you are to write two MiniZinc programs. You may use any solver, but make sure solver supports all global constraints you are using. I recommend JaCoP.

A group of n people wants to take a group photo. Each person can give preferences next to whom he or she wants to be placed in the photo. A person can give any number of preferences and a preference is unidirectional, i.e. if both Per and Vicky wants to stand next to the other placing them next to each other satisfies two preferences.  All people are place on one line, so everyone have two neighbours, with the exception of the people at the ends of the line, which have one neighbour.

Task 1: Write a program that finds a placement that maximizes the number satisfied preferences, i.e. the cost function counts the number of satisfied preferences. The preferences are provided in a data input file. Two examples are provided below.

With this approach some people might be placed far from everyone they want to stand next to. Another way to rank placements is to minimise the longest distance between the people that want to stand next to another.

Task 2: Write a MiniZinc program that finds a placement that minimise the longest distance between people with a preference, i.e. for each preference there is a distance between the two people. The cost function is the largest of these distances.

Task 3: Present your solution for the lab assistant during your time slot at the lab session. 

Task 4: When the lab assistant is happy with your solution, submit it here (click on the "Submit Assignment" button in the upper right corner and submit the files in the box that appears bellow).
*/
include "globals.mzn";

int: n;
int: n_prefs;
var 0..n_prefs: pSatisfied;

array [1..n_prefs, 1..2] of int: prefs;

array [1..n] of var 1..n: placement; % placement[person] = position

constraint alldifferent(placement);

%Task 1 Works best with chuffed solver!
/*
pSatisfied = sum([abs(placement[prefs[index,1]] - placement[prefs[index,2]])  == 1 | index in 1..n_prefs]);

solve maximize pSatisfied;

output ["Seating list: " ++ show(placement) ++ "\nSatisfied preferences: " ++ show(pSatisfied)];
*/

%Task 2 Works best with chuffed solver!
var int: dist = max([abs(placement[prefs[index,1]] - placement[prefs[index,2]]) | index in 1..n_prefs]);

solve minimize dist;

output ["Seating list: " ++ show(placement) ++ "\nMinimum distance " ++ show(dist)];
