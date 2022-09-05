include "globals.mzn";
include "jacop.mzn";

int : del_add;
int : del_mul;
int : number_add;
int : number_mul;

int : n; % number of operations
set of int : last;
set of int : add;
set of int : mul;
array[1..n] of set of int : dependencies;

array [1..n] of var 0..n*max(del_add, del_mul): starts;
array [1..n] of var 1..number_add+number_mul: alloc;
array [1..n] of int : len = 
[
    if (exists(j in 1..length(add)) (add[j] == i)) then del_add
    else del_mul endif 
    | i in 1..n
];
array [1..n] of int : h = [ 1 | i in 1..n];

% add operations should use units 1..number_add
% lower bound set by var domain
constraint forall (i in 1..length(add)) (
    alloc[add[i]] <= number_add
);

% mul operations should use units number_add+1..number_add+number_mul
% upper bound set by var domain
constraint forall (i in 1..length(mul)) (
    alloc[mul[i]] > number_add
);

% dependencies must be met
constraint forall (i in 1..n) (
    forall (j in 1..length(dependencies[i])) (
        starts[i] + len[i] <= starts[dependencies[i][j]]
    )
);

var int: c2 = max([starts[last[i]] + len[last[i]] | i in 1..length(last)]);

constraint cumulative(starts, len, h, number_add+number_mul);

% operations cannot overlap
constraint diffn(starts, alloc, len, h);



solve :: int_search(starts, smallest_max, indomain_min, complete)
    minimize c2;

output [
    "starts at:\n",
    show(starts),
    "\ncycles: ",
    show(c2),
    "\nunit 1: ",
    show(
    [            
        if alloc[u] == 1 then u
        else 0
        endif
        | u in 1..n]
    ),
    "\nunit 2: ",
    show(
    [            
        if alloc[u] == 2 then u
        else 0
        endif
        | u in 1..n]
    ),
    "\nunit 3: ",
    show(
    [            
        if alloc[u] == 3 then u
        else 0
        endif
        | u in 1..n]
    ),
    "\nunit 4: ",
    show(
    [            
        if alloc[u] == 4 then u
        else 0
        endif
        | u in 1..n]
    ),
    "\nunit 5: ",
    show(
    [            
        if alloc[u] == 5 then u
        else 0
        endif
        | u in 1..n]
    ),
    "\nunit 6: ",
    show(
    [            
        if alloc[u] == 6 then u
        else 0
        endif
        | u in 1..n]
    )
];