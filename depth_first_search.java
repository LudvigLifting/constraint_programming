/**
 *  SimpleDFS.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2015 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

import java.util.Random;

import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XgtC;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Implements Simple Depth First Search .
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

public class SplitSearch  {

    boolean trace = false;
	Random r = new Random();

    /**
     * Store used in search
     */
    Store store;

    /**
     * Defines varibales to be printed when solution is found
     */
    IntVar[] variablesToReport;

    /**
     * It represents current depth of store used in search.
     */
    int depth = 0;

    /**
     * It represents the cost value of currently best solution for FloatVar cost.
     */
    public int costValue = IntDomain.MaxInt;

    /**
     * It represents the cost variable.
     */
    public IntVar costVariable = null;

    /*
     * Number of visited nodes
     */
    public long N=0;

    /*
     * Number of failed nodes excluding leave nodes
     */
    public long failedNodes = 0;

    public SplitSearch(Store s) {
	store = s;
	}
	
	private boolean allDone(IntVar[] vars) {
		for (int i = 0; i < vars.length; i++) {
			if (!vars[i].singleton()) return false;
		}
		return true;
	}


    /**
     * This function is called recursively to assign variables one by one.
     */
    public boolean label(IntVar[] vars) {
		N++;
		
		if (trace) {
			for (int i = 0; i < vars.length; i++) 
				System.out.print (vars[i] + " ");
			System.out.println ();
		}

		ChoicePoint choice = null;
		boolean consistent;

		// Instead of imposing constraint just restrict bounds
		// -1 since costValue is the cost of last solution
		if (costVariable != null) {
			try {
				if (costVariable.min() <= costValue - 1)
					costVariable.domain.in(store.level, costVariable, costVariable.min(), costValue - 1);
				else
					return false;
			} catch (FailException f) {
				return false;
			}
		}

		consistent = store.consistency();
			
		if (!consistent) {
			// Failed leaf of the search tree
			return false;
		} else { // consistent

			if (allDone(vars)) { // this thing
				// solution found; no more variables to label

				// update cost if minimization
				if (costVariable != null)
					costValue = costVariable.min();

				reportSolution();

				return costVariable == null; // true is satisfiability search and false if minimization
			}

			choice = new ChoicePoint(vars);

			levelUp();

			store.impose(choice.getConstraint());

			// choice point imposed.
				
			consistent = label(choice.getSearchVariables());

			if (consistent) {
				levelDown();
				return true;
			} else {
				failedNodes++;

				restoreLevel();

				store.impose(new Not(choice.getConstraint()));

				// negated choice point imposed.
				
				consistent = label(vars);

				levelDown();

				if (consistent) {
					return true;
				} else {
					return false;
				}
			}
		}
    }

    void levelDown() {
		store.removeLevel(depth);
		store.setLevel(--depth);
    }

    void levelUp() {
		store.setLevel(++depth);
    }

    void restoreLevel() {
		store.removeLevel(depth);
		store.setLevel(store.level);
    }

    public void reportSolution() {
		System.out.println("Nodes visited: " + N);

		if (costVariable != null)
			System.out.println ("Cost is " + costVariable);

		for (int i = 0; i < variablesToReport.length; i++) 
			System.out.print (variablesToReport[i] + " ");

		System.out.println ("\n---------------");
    }

	public void setVariablesToReport(IntVar[] v) {
		variablesToReport = v;
    }

    public void setCostVariable(IntVar v) {
		costVariable = v;
    }

    public class ChoicePoint {
		IntVar var;
		IntVar[] searchVariables;
		int value;

		public ChoicePoint (IntVar[] v) {
			var = selectVariable(v);
			value = selectValue(var);
		}

		public IntVar[] getSearchVariables() {
			return searchVariables;
		}

		/**
		 * example variable selection; input order
		 */ 
		IntVar selectVariable(IntVar[] v) {
			enum Strat {Longest, Longest2, Shortest, First, Last, Random };
			Strat strat = Strat.Longest2;

			if (v.length != 0) {
				searchVariables = v;
				switch (strat) {
				case Longest:
					int longest = 0;
					int l = 0;
					for (int i = 0; i < v.length; i++) {
						int ll = v[i].max() - v[i].min(); 
						if (ll > l) {
							l = ll;
							longest = i;
						}
					}
					return v[longest];
				case Longest2:
					longest = 0;
					l = 0;
					for (int i = 0; i < v.length; i++) {
						int ll = v[i].max() - v[i].min(); 
						if (ll >= l) {
							l = ll;
							longest = i;
						}
					}
					return v[longest];
				case Shortest:
					int shortest = 0;
					int s = Integer.MAX_VALUE;
					for (int i = 0; i < v.length; i++) {
						int ll = v[i].max() - v[i].min(); 
						if (ll < s && ll > 0) {
							s = ll;
							shortest = i;
						}
					}
					return v[shortest];
				case Random:
					return searchVariables[r.nextInt(searchVariables.length )];
				case Last:
					for (int i = searchVariables.length - 1; i >= 0; i--) {
						if (!searchVariables[i].singleton()) return searchVariables[i];
					}
					System.err.println("found no variables");
					return searchVariables[searchVariables.length - 1];
				case First:
				default:
					for (int i = 0; i < searchVariables.length; i++) {
						if (!searchVariables[i].singleton()) return searchVariables[i];
					}
					System.err.println("found no variables");
					return searchVariables[0];
				}
			}
			else {
				System.err.println("Zero length list of variables for labeling");
				return new IntVar(store);
			}
		}

		/**
		 * value selection - pick a point at a fraction of the distance from min to max
		 */ 
		int selectValue(IntVar v) {
			return (int)((v.max() - v.min()) / 2) + v.min();
		}

		/**
		 * example constraint assigning a selected value
		 */
		public PrimitiveConstraint getConstraint() {
			return new XlteqC(var, value);
			//return new XgtC(var, value);
		}
    }
}
