//==============================================================================
//	
//	Copyright (c) 2002-
//	Authors:
//	* Dave Parker <david.parker@comlab.ox.ac.uk> (University of Oxford)
//	* Vojtech Forejt <vojtech.forejt@cs.ox.ac.uk> (University of Oxford)
//	
//------------------------------------------------------------------------------
//	
//	This file is part of PRISM.
//	
//	PRISM is free software; you can redistribute it and/or modify
//	it under the terms of the GNU General Public License as published by
//	the Free Software Foundation; either version 2 of the License, or
//	(at your option) any later version.
//	
//	PRISM is distributed in the hope that it will be useful,
//	but WITHOUT ANY WARRANTY; without even the implied warranty of
//	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//	GNU General Public License for more details.
//	
//	You should have received a copy of the GNU General Public License
//	along with PRISM; if not, write to the Free Software Foundation,
//	Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
//	
//==============================================================================

package explicit;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import common.IterableStateSet;
import explicit.rewards.STPGRewards;
import explicit.rewards.STPGRewardsNestedSimple;
import parser.VarList;
import prism.*;
import strat.MDStrategy;

/**
 * Simple explicit-state representation of a stochastic two-player game (STPG),
 * as used for abstraction of MDPs, i.e. with strict cycling between player 1,
 * player 2 and probabilistic states. Thus, we store this a set of sets of
 * distributions for each state. This means that the player 2 states are not true
 * states, i.e. they don't count for statistics and player 1 states are treated
 * as successors of each other.
 * <br><br>
 * For this reason, methods to provide direct access transitions in an {@link STPG}
 * ({@link #getNumChoices(int)}, {@link #getAction(int, int)} and {@link #getTransitionsIterator(int, int)})
 * are not supported and "nested" variants are provided instead.
 * If the {@code i}th choice of state {@code s} is nested (always true for this class),
 * then {@link #isChoiceNested(int, int)} is true and transition info is available via methods
 * Use {@link #getNumNestedChoices(int, int)}, {@link #getNestedAction(int, int, int)}
 * and {@link #getNestedTransitionsIterator(int, int, int)}.
 */
public class STPGAbstrSimple<Value> extends ModelExplicit<Value> implements STPG<Value>, NondetModelSimple<Value>
{
	// Transition function (Steps)
	protected List<ArrayList<DistributionSet<Value>>> trans;

	// Flag: allow dupes in distribution sets?
	public boolean allowDupes = false;

	// Other statistics
	protected int numDistrSets;
	protected int numDistrs;
	protected int numTransitions;
	protected int maxNumDistrSets;
	protected int maxNumDistrs;

	protected StateOwnersSimple stateOwners;

	/**
	 * Constructor: empty STPG.
	 */
	public STPGAbstrSimple()
	{
		initialise(0);
	}

	/**
	 * Constructor: new STPG with fixed number of states.
	 */
	public STPGAbstrSimple(int numStates)
	{
		initialise(numStates);
	}

	/**
	 * Constructor: build an STPG from an MDP.
	 * Data is copied directly from the MDP so take a copy first if you plan to keep/modify the MDP.
	 */
	public STPGAbstrSimple(MDPSimple<Value> m)
	{
		DistributionSet<Value> set;
		int i;
		// TODO: actions?
		initialise(m.getNumStates());
		copyFrom(m);
		for (i = 0; i < numStates; i++) {
			set = newDistributionSet(null);
			set.addAll(m.getChoices(i));
			addDistributionSet(i, set);
		}
	}

	// Mutators (for ModelSimple)

	// public List<String> getPlayerNames() {
	// 	List<String> my_list = new ArrayList<String>();
	// 	my_list.add("1");
	// 	my_list.add("2");
	// 	return my_list;
	// }

	@Override
	public void initialise(int numStates)
	{
		super.initialise(numStates);
		numDistrSets = numDistrs = numTransitions = 0;
		maxNumDistrSets = maxNumDistrs = 0;
		trans = new ArrayList<ArrayList<DistributionSet<Value>>>(numStates);
		for (int i = 0; i < numStates; i++) {
			trans.add(new ArrayList<>());
		}
	}

	public void instantiateStateOwners() {
	    int n = getNumStates();
        stateOwners = new StateOwnersSimple(n);
        // for(int i = 0; i < n; i++) {
        // 	stateOwners.add(1);
		// }
    }

	@Override
	public void clearState(int i)
	{
		// Do nothing if state does not exist
		if (i >= numStates || i < 0)
			return;
		// Clear data structures and update stats
		List<DistributionSet<Value>> list = trans.get(i);
		numDistrSets -= list.size();
		for (DistributionSet<Value> set : list) {
			numDistrs -= set.size();
			for (Distribution<Value> distr : set)
				numTransitions -= distr.size();
		}
		//TODO: recompute maxNumDistrSets
		//TODO: recompute maxNumDistrs
		// Remove all distribution sets
		trans.set(i, new ArrayList<>(0));
	}

	@Override
	public int addState()
	{
		addStates(1);
		return numStates - 1;
	}

	@Override
	public void addStates(int numToAdd)
	{
		for (int i = 0; i < numToAdd; i++) {
			trans.add(new ArrayList<>());
		}
		numStates += numToAdd;
	}

	public void setPlayer(int s, int p) throws PrismException {
		if(p < 1 || p > 2) {
			throw new PrismException("Player must be 1 or 2 for STPG.");
		}
		if(s < 0 || s >= getNumStates()) {
			throw new PrismException("s must be a valid state in the STPG.");
		}
		stateOwners.setPlayer(s, p);
	}

	@Override
	public void exportPlayers(int exportType, VarList varList, PrismLog log) throws PrismException
	{
		//Unless it's a stochastic game, we only have player 0.
		log.println(numStates);
		for (int i = 0; i < numStates; i++) {
			if (exportType != Prism.EXPORT_MATLAB)
				log.println(i + ":" + stateOwners.getPlayer(i));
			else
				log.println(stateOwners.getPlayer(i));
		}
	}

	@Override
	public void buildFromPrismExplicit(String filename) throws PrismException
	{
		BufferedReader in;
		Distribution<Value> distr;
		DistributionSet<Value> distrs;
		String s, ss[];
		int i, j, k1, k2, iLast, k1Last, k2Last, n, lineNum = 0;

		try {
			// Open file
			in = new BufferedReader(new FileReader(new File(filename)));
			// Parse first line to get num states
			s = in.readLine();
			lineNum = 1;
			if (s == null) {
				in.close();
				throw new PrismException("Missing first line of .tra file");
			}
			ss = s.split(" ");
			n = Integer.parseInt(ss[0]);
			// Initialise
			initialise(n);
			// Go though list of transitions in file
			iLast = -1;
			k1Last = -1;
			k2Last = -1;
			distrs = null;
			distr = null;
			s = in.readLine();
			lineNum++;
			while (s != null) {
				s = s.trim();
				if (s.length() > 0) {
					ss = s.split(" ");
					i = Integer.parseInt(ss[0]);
					k1 = Integer.parseInt(ss[1]);
					k2 = Integer.parseInt(ss[2]);
					j = Integer.parseInt(ss[3]);
					Value prob = getEvaluator().fromString(ss[4]);
					// For a new state or distribution set or distribution
					if (i != iLast || k1 != k1Last || k2 != k2Last) {
						// Add any previous distribution to the last set, create new one
						if (distrs != null) {
							distrs.add(distr);
						}
						distr = new Distribution<>(getEvaluator());
						// Only for a new state or distribution set...
						if (i != iLast || k1 != k1Last) {
							// Add any previous distribution set to the last state, create new one
							if (distrs != null) {
								addDistributionSet(iLast, distrs);
							}
							distrs = newDistributionSet(null);
						}
					}
					// Add transition to the current distribution
					distr.add(j, prob);
					// Prepare for next iter
					iLast = i;
					k1Last = k1;
					k2Last = k2;
				}
				s = in.readLine();
				lineNum++;
			}
			// Add previous distribution to the last set
			distrs.add(distr);
			// Add previous distribution set to the last state
			addDistributionSet(iLast, distrs);
			// Close file
			in.close();
		} catch (IOException e) {
			System.out.println(e);
			System.exit(1);
		} catch (NumberFormatException e) {
			throw new PrismException("Problem in .tra file (line " + lineNum + ") for " + getModelType());
		}
	}
	// public void buildFromPrismExplicit(String filename) throws PrismException
	// {
	// 	// we want to accurately store the model as it appears
	// 	// in the file, so we allow dupes
	// 	allowDupes = true;

	// 	int lineNum = 0;
	// 	// Open file for reading, automatic close
	// 	try (BufferedReader in = new BufferedReader(new FileReader(new File(filename)))) {
	// 		// Parse first line to get num states
	// 		String info = in.readLine();
	// 		lineNum = 1;
	// 		if (info == null) {
	// 			throw new PrismException("Missing first line of .tra file");
	// 		}
	// 		String[] infos = info.split(" ");
	// 		if (infos.length < 3) {
	// 			throw new PrismException("First line of .tra file must read #states, #choices, #transitions");
	// 		}
	// 		int n = Integer.parseInt(infos[0]);
	// 		int expectedNumChoices = Integer.parseInt(infos[1]);
	// 		int expectedNumTransitions = Integer.parseInt(infos[2]);

	// 		int emptyDistributions = 0;

	// 		// Initialise
	// 		initialise(n);
	// 		// Go though list of transitions in file
	// 		String s = in.readLine();
	// 		lineNum++;
	// 		while (s != null) {
	// 			s = s.trim();
	// 			if (s.length() > 0) {
	// 				String[] transition = s.split(" ");
	// 				int source = Integer.parseInt(transition[0]);
	// 				int choice = Integer.parseInt(transition[1]);
	// 				int target = Integer.parseInt(transition[2]);
	// 				double prob = Double.parseDouble(transition[3]);

	// 				if (source < 0 || source >= numStates) {
	// 					throw new PrismException("Problem in .tra file (line " + lineNum + "): illegal source state index " + source);
	// 				}
	// 				if (target < 0 || target >= numStates) {
	// 					throw new PrismException("Problem in .tra file (line " + lineNum + "): illegal target state index " + target);
	// 				}

	// 				// ensure distributions for all choices up to choice (inclusive) exist
	// 				// this potentially creates empty distributions that are never defined
	// 				// so we keep track of the number of distributions that are still empty
	// 				// and provide an error message if there are still empty distributions
	// 				// after having read the full .tra file
	// 				while (choice >= getNumChoices(source)) {
	// 					addChoice(source, new Distribution());
	// 					emptyDistributions++;
	// 				}

	// 				if (trans.get(source).get(choice).isEmpty()) {
	// 					// was empty distribution, becomes non-empty below
	// 					emptyDistributions--;
	// 				}
	// 				// add transition
	// 				if (! trans.get(source).get(choice).add(target, prob)) {
	// 					numTransitions++;
	// 				} else {
	// 					throw new PrismException("Problem in .tra file (line " + lineNum + "): redefinition of probability for " + source + " " + choice + " " + target);
	// 				}

	// 				// add action
	// 				if (transition.length > 4) {
	// 					String action = transition[4];
	// 					Object oldAction = getAction(source, choice);
	// 					if (oldAction != null && !action.equals(oldAction)) {
	// 						throw new PrismException("Problem in .tra file (line " + lineNum + "):"
	// 								+ "inconsistent action label for " + source + ", " + choice + ": "
	// 								+ oldAction + " and " + action);
	// 					}
	// 					setAction(source, choice, action);
	// 				}
	// 			}
	// 			s = in.readLine();
	// 			lineNum++;
	// 		}
	// 		// check integrity
	// 		if (getNumChoices() != expectedNumChoices) {
	// 			throw new PrismException("Problem in .tra file: unexpected number of choices: " + getNumChoices());
	// 		}
	// 		if (getNumTransitions() != expectedNumTransitions) {
	// 			throw new PrismException("Problem in .tra file: unexpected number of transitions: " + getNumTransitions());
	// 		}
	// 		assert(emptyDistributions >= 0);
	// 		if (emptyDistributions > 0) {
	// 			throw new PrismException("Problem in .tra file: there are " + emptyDistributions + " empty distribution, are there gaps in the choice indices?");
	// 		}
	// 	} catch (IOException e) {
	// 		throw new PrismException("File I/O error reading from \"" + filename + "\": " + e.getMessage());
	// 	} catch (NumberFormatException e) {
	// 		throw new PrismException("Problem in .tra file (line " + lineNum + ") for " + getModelType());
	// 	}
	// }

	// Mutators (other)

	/**
	 * Creates a new distribution set suitable for passing to addDistributionSet(...)
	 * i.e. a data structure consistent with the internals of the this class.
	 * An optional action label (any Object type) can be specified; null if not needed.
	 */
	public DistributionSet<Value> newDistributionSet(Object action)
	{
		return new DistributionSet<>(action);
	}

	/**
	 * Add distribution set 'newSet' to state s (which must exist).
	 * Distribution set is only actually added if it does not already exists for state s.
	 * (Assuming 'allowDupes' flag is not enabled.)
	 * Returns the index of the (existing or newly added) set.
	 * Returns -1 in case of error.
	 */
	public int addDistributionSet(int s, DistributionSet<Value> newSet)
	{
		ArrayList<DistributionSet<Value>> set;
		// Check state exists
		if (s >= numStates || s < 0)
			return -1;
		// Add distribution set (if new)
		set = trans.get(s);
		if (!allowDupes) {
			int i = set.indexOf(newSet);
			if (i != -1)
				return i;
		}
		set.add(newSet);
		// Update stats
		numDistrSets++;
		maxNumDistrSets = Math.max(maxNumDistrSets, set.size());
		numDistrs += newSet.size();
		maxNumDistrs = Math.max(maxNumDistrs, newSet.size());
		for (Distribution<Value> distr : newSet)
			numTransitions += distr.size();
		return set.size() - 1;
	}

	// Accessors (for ModelSimple)

	@Override
	public int getNumTransitions()
	{
		return numTransitions;
	}

	@Override
	public Iterator<Integer> getSuccessorsIterator(final int s)
	{
		// Need to build set to avoid duplicates
		// So not necessarily the fastest method to access successors
		HashSet<Integer> succs = new HashSet<Integer>();
		for (DistributionSet<Value> distrs : trans.get(s)) {
			for (Distribution<Value> distr : distrs) {
				succs.addAll(distr.getSupport());
			}
		}
		return succs.iterator();
	}

	@Override
	public boolean isSuccessor(int s1, int s2)
	{
		for (DistributionSet<Value> distrs : trans.get(s1)) {
			for (Distribution<Value> distr : distrs) {
				if (distr.contains(s2))
					return true;
			}
		}
		return false;
	}

	@Override
	public boolean allSuccessorsInSet(int s, BitSet set)
	{
		for (DistributionSet<Value> distrs : trans.get(s)) {
			for (Distribution<Value> distr : distrs) {
				if (!distr.isSubsetOf(set))
					return false;
			}
		}
		return true;
	}

	@Override
	public boolean someSuccessorsInSet(int s, BitSet set)
	{
		for (DistributionSet<Value> distrs : trans.get(s)) {
			for (Distribution<Value> distr : distrs) {
				if (distr.isSubsetOf(set))
					return true;
			}
		}
		return false;
	}

	@Override
	public void findDeadlocks(boolean fix) throws PrismException
	{
		for (int i = 0; i < numStates; i++) {
			// Note that no distributions is a deadlock, not an empty distribution
			if (trans.get(i).isEmpty()) {
				addDeadlockState(i);
				if (fix) {
					DistributionSet<Value> distrs = newDistributionSet(null);
					Distribution<Value> distr = new Distribution<>(getEvaluator());
					distr.add(i, getEvaluator().one());
					distrs.add(distr);
					addDistributionSet(i, distrs);
				}
			}
		}
	}

	@Override
	public void checkForDeadlocks(BitSet except) throws PrismException
	{
		for (int i = 0; i < numStates; i++) {
			if (trans.get(i).isEmpty() && (except == null || !except.get(i)))
				throw new PrismException("STPG has a deadlock in state " + i);
		}
		// TODO: Check for empty distributions sets too?
	}

	@Override
	public void exportTransitionsToDotFile(int i, PrismLog out, Iterable<explicit.graphviz.Decorator> decorators, int precision)
	{
		// Custom dot format for game abstractions
		// We ignore decorators for the moment
		int j = -1;
		for (DistributionSet<Value> distrs : trans.get(i)) {
			j++;
			String nij = "n" + i + "_" + j;
			out.print(i + " -> " + nij + " [ arrowhead=none,label=\"" + j + "\" ];\n");
			out.print(nij + " [ shape=circle,width=0.1,height=0.1,label=\"\" ];\n");
			int k = -1;
			for (Distribution<Value> distr : distrs) {
				k++;
				String nijk = "n" + i + "_" + j + "_" + k;
				out.print(nij + " -> " + nijk + " [ arrowhead=none,label=\"" + k + "\" ];\n");
				out.print(nijk + " [ shape=point,label=\"\" ];\n");
				for (Map.Entry<Integer, Value> e : distr) {
					out.print(nijk + " -> " + e.getKey() + " [ label=\"" + getEvaluator().toStringExport(e.getValue(), precision) + "\" ];\n");
				}
			}
		}
	}

	@Override
	public void exportToDotFileWithStrat(PrismLog out, BitSet mark, int strat[], int precision)
	{
		throw new RuntimeException("Not yet supported");
	}
	
	@Override
	public String infoString()
	{
		String s = "";
		s += numStates + " states (" + getNumInitialStates() + " initial)";
		s += ", " + numTransitions + " transitions";
		s += ", " + numDistrs + " choices";
		s += ", " + numDistrSets + " choice sets";
		s += ", p1max/avg = " + maxNumDistrSets + "/" + PrismUtils.formatDouble2dp(((double) numDistrSets) / numStates);
		s += ", p2max/avg = " + maxNumDistrs + "/" + PrismUtils.formatDouble2dp(((double) numDistrs) / numDistrSets);
		return s;
	}

	@Override
	public String infoStringTable()
	{
		String s = "";
		s += "States:      " + numStates + " (" + getNumInitialStates() + " initial)\n";
		s += "Transitions: " + numTransitions + "\n";
		s += "Choices:     " + numDistrs + "\n";
		s += "P1 max/avg:  " + maxNumDistrSets + "/" + PrismUtils.formatDouble2dp(((double) numDistrSets) / numStates) + "\n";
		s += "P2 max/avg:  " + maxNumDistrs + "/" + PrismUtils.formatDouble2dp(((double) numDistrs) / numDistrSets) + "\n";
		return s;
	}

	// Accessors (for NondetModel)

	@Override
	public int getNumChoices(int s)
	{
		return trans.get(s).size();
	}

	@Override
	public int getMaxNumChoices()
	{
		return maxNumDistrSets;
	}

	@Override
	public int getNumChoices()
	{
		return numDistrSets;
	}

	@Override
	public Object getAction(int s, int i)
	{
		// No actions stored currently
		return null;
	}

	@Override
	public boolean allSuccessorsInSet(int s, int i, BitSet set)
	{
		return trans.get(s).get(i).isSubsetOf(set);
	}

	@Override
	public boolean someSuccessorsInSet(int s, int i, BitSet set)
	{
		return trans.get(s).get(i).containsOneOf(set);
	}

	@Override
	public SuccessorsIterator getSuccessors(final int s, final int i)
	{
		return SuccessorsIterator.chain(new Iterator<SuccessorsIterator>() {
			private Iterator<Distribution<Value>> iterator = trans.get(s).get(i).iterator();

			@Override
			public boolean hasNext()
			{
				return iterator.hasNext();
			}

			@Override
			public SuccessorsIterator next()
			{
				Distribution<Value> dist = iterator.next();
				return SuccessorsIterator.from(dist.getSupport().iterator(), true);
			}
		});
	}

	// Accessors (for STPG)

	@Override
	public int getPlayer(int s)
	{
		// All states are player 1
		return 1;
	}

	@Override
	public int getNumTransitions(int s, int i)
	{
		// All choices are nested
		return 0;
	}

	@Override
	public Iterator<Entry<Integer, Value>> getTransitionsIterator(int s, int i)
	{
		// All choices are nested
		return null;
	}

	@Override
	public Model<Value> constructInducedModel(MDStrategy<Value> strat)
	{
		throw new RuntimeException("Not implemented");
	}
	
	@Override
	public void prob0step(BitSet subset, BitSet u, boolean forall1, boolean forall2, BitSet result)
	{
		boolean b1, b2, b3;
		for (int i : new IterableStateSet(subset, numStates)) {
			b1 = forall1; // there exists or for all player 1 choices
			for (DistributionSet<Value> distrs : trans.get(i)) {
				b2 = forall2; // there exists or for all player 2 choices
				for (Distribution<Value> distr : distrs) {
					b3 = distr.containsOneOf(u);
					if (forall2) {
						if (!b3)
							b2 = false;
					} else {
						if (b3)
							b2 = true;
					}
				}
				if (forall1) {
					if (!b2)
						b1 = false;
				} else {
					if (b2)
						b1 = true;
				}
			}
			result.set(i, b1);
		}
	}

	@Override
	public void prob1step(BitSet subset, BitSet u, BitSet v, boolean forall1, boolean forall2, BitSet result)
	{
		boolean b1, b2, b3;
		for (int i : new IterableStateSet(subset, numStates)) {
			b1 = forall1; // there exists or for all player 1 choices
			for (DistributionSet<Value> distrs : trans.get(i)) {
				b2 = forall2; // there exists or for all player 2 choices
				for (Distribution<Value> distr : distrs) {
					b3 = distr.containsOneOf(v) && distr.isSubsetOf(u);
					if (forall2) {
						if (!b3)
							b2 = false;
					} else {
						if (b3)
							b2 = true;
					}
				}
				if (forall1) {
					if (!b2)
						b1 = false;
				} else {
					if (b2)
						b1 = true;
				}
			}
			result.set(i, b1);
		}
	}

	@Override
	public void mvMultMinMax(double vect[], boolean min1, boolean min2, double result[], BitSet subset, boolean complement, int adv[])
	{
		for (int s : new IterableStateSet(subset, numStates, complement)) {
			result[s] = mvMultMinMaxSingle(s, vect, min1, min2);
		}
	}

	@Override
	public double mvMultMinMaxSingle(int s, double vect[], boolean min1, boolean min2)
	{
		int k;
		double d, prob, minmax1, minmax2;
		boolean first1, first2;
		ArrayList<DistributionSet<Value>> step;

		minmax1 = 0;
		first1 = true;
		step = trans.get(s);
		for (DistributionSet<Value> distrs : step) {
			minmax2 = 0;
			first2 = true;
			for (Distribution<Value> distr : distrs) {
				// Compute sum for this distribution
				d = 0.0;
				for (Map.Entry<Integer, Value> e : distr) {
					k = e.getKey();
					prob = getEvaluator().toDouble(e.getValue());
					d += prob * vect[k];
				}
				// Check whether we have exceeded min/max so far
				if (first2 || (min2 && d < minmax2) || (!min2 && d > minmax2))
					minmax2 = d;
				first2 = false;
			}
			// Check whether we have exceeded min/max so far
			if (first1 || (min1 && minmax2 < minmax1) || (!min1 && minmax2 > minmax1))
				minmax1 = minmax2;
			first1 = false;
		}

		return minmax1;
	}

	@Override
	public List<Integer> mvMultMinMaxSingleChoices(int s, double vect[], boolean min1, boolean min2, double val)
	{
		int j, k;
		double d, prob, minmax2;
		boolean first2;
		List<Integer> res;
		ArrayList<DistributionSet<Value>> step;

		// Create data structures to store strategy
		res = new ArrayList<Integer>();
		// One row of matrix-vector operation 
		j = -1;
		step = trans.get(s);
		for (DistributionSet<Value> distrs : step) {
			j++;
			minmax2 = 0;
			first2 = true;
			for (Distribution<Value> distr : distrs) {
				// Compute sum for this distribution
				d = 0.0;
				for (Map.Entry<Integer, Value> e : distr) {
					k = e.getKey();
					prob = getEvaluator().toDouble(e.getValue());
					d += prob * vect[k];
				}
				// Check whether we have exceeded min/max so far
				if (first2 || (min2 && d < minmax2) || (!min2 && d > minmax2))
					minmax2 = d;
				first2 = false;
			}
			// Store strategy info if value matches
			//if (PrismUtils.doublesAreClose(val, d, termCritParam, termCrit == TermCrit.ABSOLUTE)) {
			if (PrismUtils.doublesAreEqual(val, minmax2)) {
				res.add(j);
				//res.add(distrs.getAction());
			}
		}

		return res;
	}

	@Override
	public double mvMultGSMinMax(double vect[], boolean min1, boolean min2, BitSet subset, boolean complement, boolean absolute, int[] adv)
	{
		double d, diff, maxDiff = 0.0;
		for (int s : new IterableStateSet(subset, numStates, complement)) {
			d = mvMultJacMinMaxSingle(s, vect, min1, min2, adv);
			diff = absolute ? (Math.abs(d - vect[s])) : (Math.abs(d - vect[s]) / d);
			maxDiff = diff > maxDiff ? diff : maxDiff;
			vect[s] = d;
		}
		return maxDiff;
	}

	@Override
	public double mvMultJacMinMaxSingle(int s, double vect[], boolean min1, boolean min2, int[] adv)
	{
		int k;
		double diag, d, prob, minmax1, minmax2;
		boolean first1, first2;
		ArrayList<DistributionSet<Value>> step;

		minmax1 = 0;
		first1 = true;
		step = trans.get(s);
		for (DistributionSet<Value> distrs : step) {
			minmax2 = 0;
			first2 = true;
			for (Distribution<Value> distr : distrs) {
				diag = 1.0;
				// Compute sum for this distribution
				d = 0.0;
				for (Map.Entry<Integer, Value> e : distr) {
					k = e.getKey();
					prob = getEvaluator().toDouble(e.getValue());
					if (k != s) {
						d += prob * vect[k];
					} else {
						diag -= prob;
					}
					if (diag > 0)
						d /= diag;
				}
				// Check whether we have exceeded min/max so far
				if (first2 || (min2 && d < minmax2) || (!min2 && d > minmax2))
					minmax2 = d;
				first2 = false;
			}
			// Check whether we have exceeded min/max so far
			if (first1 || (min1 && minmax2 < minmax1) || (!min1 && minmax2 > minmax1))
				minmax1 = minmax2;
			first1 = false;
		}

		return minmax1;
	}

	@Override
	public void mvMultRewMinMax(double vect[], STPGRewards<Double> rewards, boolean min1, boolean min2, double result[], BitSet subset, boolean complement, int adv[])
	{
		for (int s : new IterableStateSet(subset, numStates, complement)) {
			result[s] = mvMultRewMinMaxSingle(s, vect, rewards, min1, min2, adv);
		}
	}

	@Override
	public double mvMultRewMinMaxSingle(int s, double vect[], STPGRewards<Double> rewards, boolean min1, boolean min2, int adv[])
	{
		int dsIter, dIter, k;
		double d, prob, minmax1, minmax2;
		boolean first1, first2;
		ArrayList<DistributionSet<Value>> step;

		minmax1 = 0;
		first1 = true;
		dsIter = -1;
		step = trans.get(s);
		for (DistributionSet<Value> distrs : step) {
			dsIter++;
			minmax2 = 0;
			first2 = true;
			dIter = -1;
			for (Distribution<Value> distr : distrs) {
				dIter++;
				// Compute sum for this distribution
				d = ((STPGRewardsNestedSimple<Double>) rewards).getNestedTransitionReward(s, dsIter, dIter);
				for (Map.Entry<Integer, Value> e : distr) {
					k = e.getKey();
					prob = getEvaluator().toDouble(e.getValue());
					d += prob * vect[k];
				}
				// Check whether we have exceeded min/max so far
				if (first2 || (min2 && d < minmax2) || (!min2 && d > minmax2))
					minmax2 = d;
				first2 = false;
			}
			minmax2 += rewards.getTransitionReward(s, dsIter);
			// Check whether we have exceeded min/max so far
			if (first1 || (min1 && minmax2 < minmax1) || (!min1 && minmax2 > minmax1))
				minmax1 = minmax2;
			first1 = false;
		}

		return minmax1;
	}

	@Override
	public List<Integer> mvMultRewMinMaxSingleChoices(int s, double vect[], STPGRewards<Double> rewards, boolean min1, boolean min2, double val)
	{
		int dsIter, dIter, k;
		double d, prob, minmax2;
		boolean first2;
		List<Integer> res;
		ArrayList<DistributionSet<Value>> step;

		// Create data structures to store strategy
		res = new ArrayList<Integer>();
		// One row of matrix-vector operation 
		dsIter = -1;
		step = trans.get(s);
		for (DistributionSet<Value> distrs : step) {
			dsIter++;
			minmax2 = 0;
			first2 = true;
			dIter = -1;
			for (Distribution<Value> distr : distrs) {
				dIter++;
				// Compute sum for this distribution
				d = ((STPGRewardsNestedSimple<Double>) rewards).getNestedTransitionReward(s, dsIter, dIter);
				for (Map.Entry<Integer, Value> e : distr) {
					k = e.getKey();
					prob = getEvaluator().toDouble(e.getValue());
					d += prob * vect[k];
				}
				// Check whether we have exceeded min/max so far
				if (first2 || (min2 && d < minmax2) || (!min2 && d > minmax2))
					minmax2 = d;
				first2 = false;
			}
			minmax2 += rewards.getTransitionReward(s, dsIter);
			// Store strategy info if value matches
			//if (PrismUtils.doublesAreClose(val, d, termCritParam, termCrit == TermCrit.ABSOLUTE)) {
			if (PrismUtils.doublesAreEqual(val, minmax2)) {
				res.add(dsIter);
				//res.add(distrs.getAction());
			}
		}

		return res;
	}

	@Override
	public void mvMultRewMinMax(double[] vect, STPGRewards<Double> rewards, boolean min1, boolean min2, double[] result, BitSet subset, boolean complement, int[] adv, double disc)
	{
		throw new UnsupportedOperationException();
	}
	
	// Additional accessor that extended STPG with a "nested view"

	/**
	 * Is choice {@code i} of state {@code s} in nested form? (See {@link explicit.STPG} for details)
	 */
	public boolean isChoiceNested(int s, int i)
	{
		// All choices are nested
		return true;
	}

	/**
	 * Get the number of (nested) choices in choice {@code i} of state {@code s}.
	 */
	public int getNumNestedChoices(int s, int i)
	{
		return trans.get(s).get(i).size();
	}

	/**
	 * Get the action label (if any) for nested choice {@code i,j} of state {@code s}.
	 */
	public Object getNestedAction(int s, int i, int j)
	{
		return trans.get(s).get(i).getAction();
	}

	/**
	 * Get the number of transitions from nested choice {@code i,j} of state {@code s}.
	 */
	public int getNumNestedTransitions(int s, int i, int j)
	{
		DistributionSet<Value> ds = trans.get(s).get(i);
		Iterator<Distribution<Value>> iter = ds.iterator();
		Distribution<Value> distr = null;
		int k = 0;
		while (iter.hasNext() && k <= j) {
			distr = iter.next();
			k++;
		}
		if (k <= j)
			return 0;
		else
			return distr.size();
	}

	/**
	 * Get an iterator over the transitions from nested choice {@code i,j} of state {@code s}.
	 */
	public Iterator<Entry<Integer, Value>> getNestedTransitionsIterator(int s, int i, int j)
	{
		DistributionSet<Value> ds = trans.get(s).get(i);
		Iterator<Distribution<Value>> iter = ds.iterator();
		Distribution<Value> distr = null;
		int k = 0;
		while (iter.hasNext() && k <= j) {
			distr = iter.next();
			k++;
		}
		if (k <= j)
			return null;
		else
			return distr.iterator();
	}

	// Accessors (other)

	/**
	 * Get the list of choices (distribution sets) for state s.
	 */
	public List<DistributionSet<Value>> getChoices(int s)
	{
		return trans.get(s);
	}

	/**
	 * Get the ith choice (distribution set) for state s.
	 */
	public DistributionSet<Value> getChoice(int s, int i)
	{
		return trans.get(s).get(i);
	}

	/**
	 * Get the total number of player 1 choices (distribution sets) over all states.
	 */
	public int getNumPlayer1Choices()
	{
		return numDistrSets;
	}

	/**
	 * Get the total number of player 2 choices (distributions) over all states.
	 */
	public int getNumPlayer2Choices()
	{
		return numDistrs;
	}

	/**
	 * Get the maximum number of player 1 choices (distribution sets) in any state.
	 */
	public int getMaxNumPlayer1Choices()
	{
		// TODO: Recompute if necessary
		return maxNumDistrSets;
	}

	/**
	 * Get the maximum number of player 2 choices (distributions) in any state.
	 */
	public int getMaxNumPlayer2Choices()
	{
		// TODO: Recompute if necessary
		return maxNumDistrs;
	}

	// Standard methods

	// @Override // Move to superclass later
	public String toStringGeneric()
	{
		// General purpose toString(), based on STPG access methods
		int s, i, j, ni, nj;
		boolean first, firsti, firstTr;
		Iterator<Entry<Integer, Value>> it;
		String str = "";
		first = true;
		str = "[ ";
		for (s = 0; s < numStates; s++) {
			if (first)
				first = false;
			else
				str += ", ";
			str += s + ": ";
			ni = getNumChoices(s);
			str += "[";
			firsti = true;
			for (i = 0; i < ni; i++) {
				// Do non-nested choices
				it = getTransitionsIterator(s, i);
				if (it == null)
					continue;
				if (firsti)
					firsti = false;
				else
					str += ", ";
				str += "{";
				firstTr = true;
				while (it.hasNext()) {
					Entry<Integer, Value> next = it.next();
					if (firstTr)
						firstTr = false;
					else
						str += ", ";
					str += next.getKey() + "=" + next.getValue();
				}
				str += "}";
				// Do nested choices
				nj = getNumNestedChoices(s, i);
				if (nj == 0)
					continue;
				if (firsti)
					firsti = false;
				else
					str += ", ";
				str += "[";
				for (j = 0; j < nj; j++) {
					it = getNestedTransitionsIterator(s, i, j);
					if (it == null)
						continue;
					if (j > 0)
						str += ", ";
					str += "{";
					firstTr = true;
					while (it.hasNext()) {
						Entry<Integer, Value> next = it.next();
						if (firstTr)
							firstTr = false;
						else
							str += ", ";
						str += next.getKey() + "=" + next.getValue();
					}
					str += "}";
				}
				str += "]";
			}
			str += "]";
		}
		str += " ]";
		return str;
	}

	@Override
	public String toString()
	{
		// Custom toString()
		int i;
		boolean first;
		String s = "";
		first = true;
		s = "[ ";
		for (i = 0; i < numStates; i++) {
			if (first)
				first = false;
			else
				s += ", ";
			s += i + ": " + trans.get(i);
		}
		s += " ]";
		return s;
	}

	/**
	 * Equality check.
	 */
	public boolean equals(Object o)
	{
		if (o == null || !(o instanceof STPGAbstrSimple))
			return false;
		STPGAbstrSimple<?> stpg = (STPGAbstrSimple<?>) o;
		if (numStates != stpg.numStates)
			return false;
		if (!initialStates.equals(stpg.initialStates))
			return false;
		if (!trans.equals(stpg.trans))
			return false;
		return true;
	}

	/**
	 * Simple test program
	 */
	public static void main(String args[])
	{
		STPGModelChecker mc;
		STPGAbstrSimple<Double> stpg;
		DistributionSet<Double> set;
		Distribution<Double> distr;
		//ModelCheckerResult res;
		BitSet target;

		// Simple example: Create and solve the stochastic game from:
		// Mark Kattenbelt, Marta Kwiatkowska, Gethin Norman, David Parker
		// A Game-based Abstraction-Refinement Framework for Markov Decision Processes
		// Formal Methods in System Design 36(3): 246-280, 2010

		try {
			// Build game
			stpg = new STPGAbstrSimple<>();
			stpg.addStates(4);
			// State 0 (s_0)
			set = stpg.newDistributionSet(null);
			distr = Distribution.ofDouble();
			distr.set(1, 1.0);
			set.add(distr);
			stpg.addDistributionSet(0, set);
			// State 1 (s_1,s_2,s_3)
			set = stpg.newDistributionSet(null);
			distr = Distribution.ofDouble();
			distr.set(2, 1.0);
			set.add(distr);
			distr = Distribution.ofDouble();
			distr.set(1, 1.0);
			set.add(distr);
			stpg.addDistributionSet(1, set);
			set = stpg.newDistributionSet(null);
			distr = Distribution.ofDouble();
			distr.set(2, 0.5);
			distr.set(3, 0.5);
			set.add(distr);
			distr = Distribution.ofDouble();
			distr.set(3, 1.0);
			set.add(distr);
			stpg.addDistributionSet(1, set);
			// State 2 (s_4,s_5)
			set = stpg.newDistributionSet(null);
			distr = Distribution.ofDouble();
			distr.set(2, 1.0);
			set.add(distr);
			stpg.addDistributionSet(2, set);
			// State 3 (s_6)
			set = stpg.newDistributionSet(null);
			distr = Distribution.ofDouble();
			distr.set(3, 1.0);
			set.add(distr);
			stpg.addDistributionSet(3, set);
			// Print game
			System.out.println(stpg);

			// Model check
			mc = new STPGModelChecker(null);
			//mc.setVerbosity(2);
			target = new BitSet();
			target.set(3);
			stpg.exportToDotFile("stpg.dot", target);
			System.out.println("min min: " + mc.computeReachProbs(stpg, target, true, true).soln[0]);
			System.out.println("max min: " + mc.computeReachProbs(stpg, target, false, true).soln[0]);
			System.out.println("min max: " + mc.computeReachProbs(stpg, target, true, false).soln[0]);
			System.out.println("max max: " + mc.computeReachProbs(stpg, target, false, false).soln[0]);
		} catch (PrismException e) {
			System.out.println(e);
		}
	}
}
