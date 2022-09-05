include "globals.mzn";

int: graph_size;
int: start;
int: n_dests;
array [1..n_dests] of int: dest;
int: n_edges;
array [1..n_edges] of int: from;
array [1..n_edges] of int: to;
array [1..n_edges] of int: cost;

array [1..n_edges,1..2] of int: edges = array2d(1..n_edges, 1..2, [ 
    if j == 1 then from[i]
    else to[i] endif
  | i in 1..n_edges, j in 1..2]);
  
array [1..graph_size] of int: balances = [ 
    if i == start then n_dests
    elseif exists(j in 1..n_dests)(dest[j] == i) then -1
    else 0 endif
  | i in 1..graph_size];
 
array [1..n_edges] of var -n_dests..n_dests: flows;

constraint network_flow(edges, balances, flows);

var int: costFun = sum([cost[i] | i in 1..n_edges where flows[i] != 0]);

solve minimize costFun;

output [
  show([show(edges[i,1])++"->"++show(edges[i,2])++":"++show(flows[i]) | i in 1..n_edges where flows[i] != 0]),
  "\ncost: " ++ show(costFun)
];