package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.Unit;
import soot.ValueBox;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.scalar.ArrayPackedSet;
import soot.toolkits.scalar.CollectionFlowUniverse;
import soot.toolkits.scalar.FlowUniverse;
import soot.toolkits.scalar.ForwardFlowAnalysis;

/**
 * Determine for two LValues v1, v2 if there
 * exists a path in an atomic section where 
 * 		v1 is accessed
 * 	    v1 is possibly modified
 * 		v2 is accessed
 * then we say v1 accessedBefore v2
 * 
 * @author Ben_Sepanski
 *
 */
class AccessedBeforeRelationOnBody extends ForwardFlowAnalysis<Unit, AccessedThenModifiedSet> {	
	private static Logger log = LoggerFactory.getLogger(AccessedBeforeRelationOnBody.class);

	private static final CollectionFlowUniverse<Integer>
		emptyUniv = new CollectionFlowUniverse<>(new HashSet<Integer>());
	
	private PointerAnalysis ptrAnalysis;
	private final List<LValueBox> lValues;
	private final CollectionFlowUniverse<Integer> univ;
	// Map LVal to set{LVals w | v accessedBefore w}
	private final Map<Integer, Set<Integer>> accessedBefore = new HashMap<>();
	// all the lvalues as ids
	private final Map<LValueBox, Integer> lValueIDs = new HashMap<>();
	// atomic segment beginnings and endings
	private final Set<Unit> startAtomicSegment = new HashSet<>(),
							afterAtomicSegment = new HashSet<>();

	/**
	 * 
	 * @param b the method body
	 * @param ptrAnalysis oracle for alias relaation
	 * @param atomicSegments a list of atomic segments (possibly including
	 *                       atomic segments in some other body).
	 *                       We will use the sublist of atomic segments
	 *                       associated to b
	 * @param lValuesAccessedIn A list whose *i*th element holds the IDs
	 * 							of all the lValues accessed in the segment
	 * 							atomicSegments.get(i)
	 * @param lValues A map from ID -> LValueBox
	 */
	public AccessedBeforeRelationOnBody(Body b,
								PointerAnalysis ptrAnalysis,
							    List<AtomicSegment> atomicSegments,
							    List<List<Integer>> lValuesAccessedIn,
							    List<LValueBox> lValues)
	{
		super(new BriefUnitGraph(b));  // Operating on body b		
		this.ptrAnalysis = ptrAnalysis;
		this.lValues = lValues;
		
		// Grab all the atomic segments corresponding to this body,
		// as well as the LValues
		for(int i = 0; i < atomicSegments.size(); ++i) {
			AtomicSegment atSeg = atomicSegments.get(i);
			if(b.equals(atSeg.getBody())) {
				startAtomicSegment.add(atSeg.getFirstUnit());
				// THIS RELIES ON THE FACT THAT ATOMIC SEGMENTS ARE
				// AT THE TOP LEVEL: only have one successor in CFG
				afterAtomicSegment.add(b.getUnits().getSuccOf(atSeg.getLastUnit()));
				// Record all the lValues that we might need to look out for,
				// as well as their index
				for(int j : lValuesAccessedIn.get(i)) {
					lValueIDs.put(lValues.get(j), j);
				}
			}
		}
		
		this.univ = new CollectionFlowUniverse<Integer>(lValueIDs.values());
		for(Integer lvbID : lValueIDs.values()) {
			this.accessedBefore.put(lvbID, new HashSet<Integer>());
		}
		log.debug("Begnning flow analysis on " + b.getMethod().getName());
		this.doAnalysis();
		log.debug("Flow analysis complete");
	}
	
	/**
	 * @return a map (id of v) -> {id of w | v accessed before w}
	 */
	public Map<Integer, Set<Integer>> getAccessedBefore() {
		return accessedBefore;
	}

	/**
	 * If we are at the start/end of an atomic section, change
	 * the universe to the lvalues/the empty universe.
	 * 
	 * Then, if inside an atomic segment record reads and possible
	 * modifies.
	 */
	@Override
	protected void flowThrough(AccessedThenModifiedSet in, Unit d, AccessedThenModifiedSet out) {
		// If at the start of an atomic segment, make sure the universe is
		// the universe of lvalues and return.
		if(this.startAtomicSegment.contains(d)) {
			if(out.getUniverse().equals(emptyUniv)) {
				out.setUniverse(this.univ);
			}
			return;
		}
		// If leaving, make sure the universe is empty and return
		else if(this.afterAtomicSegment.contains(d)) {
			if(!out.getUniverse().equals(emptyUniv)) {
				out.setUniverse(emptyUniv);
			}
		}
		// If in was not in the atomic segment, neither is out. Leave it as-is
		if(in.getUniverse().equals(emptyUniv)) {
			return;
		}
		// Now we know we are inside an atomic segment: do our analysis
		in.copy(out);
		// Look at use and def to record what gets accessed and possibly
		// modified
		Set<Integer> usedLVals = new HashSet<>(),
					 defLVals = new HashSet<>();
		LValueBox lvb = new LValueBox();
		for(ValueBox vb : d.getUseBoxes()) {
			if(lvb.canContainValue(vb.getValue())) {
				lvb.setValue(vb.getValue());
				if(lValueIDs.containsKey(lvb)) {
					usedLVals.add(lValueIDs.get(lvb));
				}
			}
		}
		for(ValueBox vb : d.getDefBoxes()) {
			if(lvb.canContainValue(vb.getValue())) {
				lvb.setValue(vb.getValue());
				if(lValueIDs.containsKey(lvb)) {
					defLVals.add(lValueIDs.get(lvb));
				}
			}
		}
		// Record what got accessed and possibly modified
		out.recordAccess(usedLVals, accessedBefore);
		out.recordAccess(defLVals, accessedBefore);
		// Look at defs to record what might get modified
		out.recordPossibleMod(defLVals, this.ptrAnalysis, this.lValues);
	}

	/**
	 * Start with an empty universe
	 */
	@Override
	protected AccessedThenModifiedSet newInitialFlow() {
		return new AccessedThenModifiedSet(emptyUniv);
	}
	
	@Override
	protected void merge(AccessedThenModifiedSet in1, AccessedThenModifiedSet in2, AccessedThenModifiedSet out) {
		out.merge(in1, in2);  // merge in1, in2 into out
	}

	@Override
	protected void copy(AccessedThenModifiedSet source, AccessedThenModifiedSet dest) {
		source.copy(dest);  // copy source into dest
	}
}


/**
 * Just a struct basically keeping track of lvalues that
 * have been accessed inside an atomic and of lvalues
 * that have been accessed then modified inside an atomic 
 * 
 * @author Ben_Sepanski
 */
class AccessedThenModifiedSet {
	private ArrayPackedSet<Integer> accessedInAtomic;
	private ArrayPackedSet<Integer> accessedThenModInAtomic;
	private FlowUniverse<Integer> universe;
	
	/**
	 * Build a ReadThenModifiedSet
	 * 
	 * @param univ The universe of LValues
	 * @param _ptrAnalysis tells us what might be aliased
	 */
	public AccessedThenModifiedSet(FlowUniverse<Integer> univ) {
		accessedInAtomic = new ArrayPackedSet<Integer>(univ);
		accessedThenModInAtomic = new ArrayPackedSet<Integer>(univ);
		universe = univ;
	}
	
	/**
	 * Overload equals to just check that have same
	 * flowsets and universe
	 * @param that
	 * @return
	 */
	@Override
	public boolean equals(Object that) {
		if(that == this) return true;
		if(!(that instanceof AccessedThenModifiedSet)) return false;
		AccessedThenModifiedSet other = (AccessedThenModifiedSet) that;
		return Objects.equals(accessedInAtomic, other.accessedInAtomic)
			   && Objects.equals(accessedThenModInAtomic, other.accessedThenModInAtomic)
			   && Objects.equals(universe, other.universe);
	}
	
	/**
	 * Get the current universe
	 * @return
	 */
	public FlowUniverse<Integer> getUniverse() {
		return this.universe;
	}
	
	/**
	 * Sets the universe, re-initializes accessedInAtomic and
	 * accessedThenModInAtomic to empty sets in the new universe
	 * 
	 * @param newUniverse
	 */
	public void setUniverse(FlowUniverse<Integer> newUniverse) {
		this.universe = newUniverse;
		accessedInAtomic = new ArrayPackedSet<Integer>(newUniverse);
		accessedThenModInAtomic = new ArrayPackedSet<Integer>(newUniverse);
	}
	
	/**
	 * Deep copy this into that
	 * 
	 * @param that
	 */
	public void copy(AccessedThenModifiedSet that) {
		that.universe = this.universe;
		this.accessedInAtomic.copy(that.accessedInAtomic);
		this.accessedThenModInAtomic.copy(that.accessedThenModInAtomic);
	}
	/**
	 * Store union of in1 and in2 in this.
	 * We assume that in1 and in2 have the same universe
	 * (which is fine if our atomic segments are placed reasonably)
	 * 
	 * @param in1
	 * @param in2
	 * @param out
	 */
	public void merge(AccessedThenModifiedSet in1, AccessedThenModifiedSet in2) {
		assert(in1.getUniverse().equals(in2.getUniverse()));
		this.universe = in1.universe;
		in1.accessedInAtomic.union(in2.accessedInAtomic, this.accessedInAtomic);
		in1.accessedThenModInAtomic.union(in2.accessedThenModInAtomic, this.accessedThenModInAtomic);
	}
	/**
	 * Record all the LValues w1,...,wn in accessedLVals as accessed
	 * in the atomic section, and for any LValues v1
	 * that have already been accessed then possibly modified
	 * put w1,...,wn in accessedBefore[v1]
	 * 
	 * @param accessedLVals The lvals accessed in a unit
	 * @param accessedBefore the mapping v -> {w | v accessedbefore w}
	 */
	public void recordAccess(Set<Integer> accessedLVals,
							 Map<Integer, Set<Integer>> accessedBefore) {
		for(int lValID : accessedLVals) {
			this.accessedInAtomic.add(lValID);
		}
		Iterator<Integer> accThenMod = accessedThenModInAtomic.iterator();
		while(accThenMod.hasNext()) {
			accessedBefore.get(accThenMod.next()).addAll(accessedLVals);
		}
	}
	/**
	 * Mark all the LValues in possibleModLVals which have
	 * already been accessed in the atomic section
	 * as possibly modified.
	 * 
	 * Use the alias analysis to be sure we don't miss
	 * anything
	 * 
	 * @param possibleModLVals
	 * @param PointerAnalysis an oracle for the alias relation
	 * @param lValues a map from ID -> LValueBox
	 */
	public void recordPossibleMod(Set<Integer> possibleModLVals,
								  PointerAnalysis ptrAnalysis,
								  List<LValueBox> lValues) {
		// For each already accessed element
		Iterator<Integer> alreadyAccessed = accessedInAtomic.iterator();
		while(alreadyAccessed.hasNext()) {
			int lvbID = alreadyAccessed.next();
			LValueBox lvb = lValues.get(lvbID);
			// For each possibly modified value
			for(int possModID : possibleModLVals) {
				LValueBox possMod = lValues.get(possModID);
				// If they may alias, record lvb as accessed then possibly modified
				AliasRelation aliasQ = ptrAnalysis.getAliasRelation(possMod, lvb);
				if(!aliasQ.equals(AliasRelation.NOT_ALIAS)) {
					accessedThenModInAtomic.add(lvbID);
					break;
				}
			}
		}
	}
}
