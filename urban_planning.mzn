/*
  Assignment 5, Ludvig Lifting, EDAN01 Constraint programming

    data set 1: max points: 14 | Chuffed 0.10.4: 386ms  | Geocode 6.3.0: 332ms
    data set 2: max points: 36 | Chuffed 0.10.4: 353ms  | Geocode 6.3.0: 338ms
    data set 3: max points: 58 | Chuffed 0.10.4: 1m 14s | Geocode 6.3.0: 4m 33s
*/

include "globals.mzn";


int : n; % Size of the square matrix
int : n_commercial; % Commercial building = 1 in the grid
int : n_residential; % Residential building = 0 in the grid

array [1..n+1] of int : point_distribution; % Point array

array [1..n, 1..n] of var 0..1 : grid; % n*n-matrix representing all the lots


% Ensures the number of commercial and residential buildings is not exceeded
constraint (
  sum(grid) == n_commercial
);

% Soft constraint for symmetrical breaking (Lexical ordering)
constraint(
  lex2(grid)
);


% Calculates points for all rows
var int : rowPoints = sum([point_distribution[n - sum(row(grid, i)) + 1] | i in 1..n]);

% Calculates points for all columns
var int : colPoints = sum([point_distribution[n - sum(col(grid, i)) + 1] | i in 1..n]);

% Calculates total number of points
var int : totalPoints = rowPoints + colPoints;


% Solving for maximizing the total number of points
solve maximize totalPoints;

% Output the matrix as well as the total number of points
output [ 
  if [i,j] == [1,1] then "URBAN PLANNING:\n" ++ "1 = Commercial building, 0 = Residential building\n\n" else "" endif ++
  
  show_int(2, grid[i,j]) ++ 
  if j == n then "\n" else " " endif ++
  
  if [i,j] == [n,n] then "\nTotal Points = " ++ show(totalPoints) else "" endif | i in 1..n, j in 1..n
];
