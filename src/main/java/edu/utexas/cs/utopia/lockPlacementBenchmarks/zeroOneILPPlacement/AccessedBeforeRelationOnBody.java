package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Objects;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.InvokeStmt;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.scalar.ArrayPackedSet;
import soot.toolkits.scalar.CollectionFlowUniverse;
import soot.toolkits.scalar.FlowSet;
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

	private static SootClass lockManagerClass = Scene.v().getSootClass(
		"edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.TwoPhaseLockManager");
	private static SootMethod 
		enterAtomicMethod = lockManagerClass.getMethod("void enterAtomicSegment()");
	private static CollectionFlowUniverse<LValueBox>
		emptyUniv = new CollectionFlowUniverse<>(new HashSet<LValueBox>());
	
	private PointerAnalysis ptrAnalysis;
	private HashSet<LValueBox> sharedLValues;
	private CollectionFlowUniverse<LValueBox> univ;
	// Map LVal to set{LVals w | v accessedBefore w}
	private HashMap<LValueBox, HashSet<LValueBox>> accessedBefore;
	
	/**
	 * Get the accessedBefore relation for this body
	 * @return
	 */
	public HashMap<LValueBox, HashSet<LValueBox>> getAccessedBefore() {
		return accessedBefore;
	}

	public AccessedBeforeRelationOnBody(PointerAnalysis ptrAnalysis, Body b, HashSet<LValueBox> sharedLValues) 
	{
		super(new BriefUnitGraph(b));		
		this.ptrAnalysis = ptrAnalysis;
		this.sharedLValues = sharedLValues;
		this.univ = new CollectionFlowUniverse<LValueBox>(sharedLValues);
		this.accessedBefore = new HashMap<LValueBox, HashSet<LValueBox>>();
		for(LValueBox lvb : sharedLValues) {
			this.accessedBefore.put(lvb, new HashSet<LValueBox>());
		}
		log.debug("Begnning flow analysis on " + b.getMethod().getName());
		this.doAnalysis();
		log.debug("Flow analysis complete");
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
		// If at the start of an atomic segment, change
		// the universe to the lvalues. If leaving an atomic segment,
		// there is nothing to do
		if(out.getUniverse().equals(emptyUniv) && d instanceof InvokeStmt) {
			InvokeStmt invk = (InvokeStmt) d;
			if(invk.getInvokeExpr().getMethod().equals(enterAtomicMethod)) {
				out = new AccessedThenModifiedSet(univ, ptrAnalysis);
			}
		}
		// Now if considering empty universe (i.e. we're not in an atomic section),
		// out will not change
		if(in.getUniverse().equals(emptyUniv)) {
			return;
		}
		// Otherwise, we are inside an atomic segment.
		// Copy in into out
		in.copy(out);
		// Look at use to record what gets accessed
		HashSet<LValueBox> useBoxes = LValueBox.getAllLValues(d.getUseBoxes());
		useBoxes.retainAll(sharedLValues);
		out.recordAccess(useBoxes, accessedBefore);
		// Look at defs to record what might get modified
		HashSet<LValueBox> defBoxes = LValueBox.getAllLValues(d.getDefBoxes());
		defBoxes.retainAll(sharedLValues);
		out.recordPossibleMod(defBoxes);
		// defs were accessed during modification, record that
		out.recordAccess(defBoxes, accessedBefore);
	}

	/**
	 * Start with an empty universe
	 */
	@Override
	protected AccessedThenModifiedSet newInitialFlow() {
		return new AccessedThenModifiedSet(emptyUniv, null);
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
	private ArrayPackedSet<LValueBox> accessedInAtomic;
	private ArrayPackedSet<LValueBox> accessedThenModInAtomic;
	private FlowUniverse<LValueBox> universe;
	private PointerAnalysis ptrAnalysis;
	
	/**
	 * Build a ReadThenModifiedSet
	 * 
	 * @param univ The universe of LValues
	 * @param _ptrAnalysis tells us what might be aliased
	 */
	public AccessedThenModifiedSet(FlowUniverse<LValueBox> univ, PointerAnalysis _ptrAnalysis) {
		accessedInAtomic = new ArrayPackedSet<LValueBox>(univ);
		accessedThenModInAtomic = new ArrayPackedSet<LValueBox>(univ);
		universe = univ;
		ptrAnalysis = _ptrAnalysis;
	}
	
	/**
	 * Overload equals to just check that have same
	 * flowsets, ptr analysis, and universe
	 * @param that
	 * @return
	 */
	@Override
	public boolean equals(Object that) {
		if(that == this) return true;
		if(!(that instanceof AccessedThenModifiedSet)) return false;
		AccessedThenModifiedSet other = (AccessedThenModifiedSet) that;
		if(!(
			 Objects.equals(accessedInAtomic, other.accessedInAtomic)
			 && Objects.equals(accessedThenModInAtomic, other.accessedThenModInAtomic)
			 && Objects.equals(universe, other.universe)
			 && Objects.equals(ptrAnalysis, other
					 .ptrAnalysis)))
		{
			return false;
		}
		return true;
	}
	
	/**
	 * Get the current universe
	 * @return
	 */
	public FlowUniverse<LValueBox> getUniverse() {
		return this.universe;
	}
	/**
	 * Deep copy this into that
	 * 
	 * @param that
	 */
	public void copy(AccessedThenModifiedSet that) {
		that.universe = this.universe;
		that.ptrAnalysis = this.ptrAnalysis;
		this.accessedInAtomic.copy(that.accessedInAtomic);
		this.accessedThenModInAtomic.copy(that.accessedThenModInAtomic);
	}
	/**
	 * Store union of in1 and in2 in this.
	 * We assume that in1 and in2 have the same universe
	 * (which is fine if our atomic segments are placed reasonably)
	 * and the same pointer analysis
	 * 
	 * @param in1
	 * @param in2
	 * @param out
	 */
	public void merge(AccessedThenModifiedSet in1, AccessedThenModifiedSet in2) {
		assert(in1.getUniverse().equals(in2.getUniverse()));
		assert(in1.ptrAnalysis.equals(in2.ptrAnalysis));
		this.universe = in1.universe;
		this.ptrAnalysis = in1.ptrAnalysis;
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
	public void recordAccess(HashSet<LValueBox> accessedLVals,
							 HashMap<LValueBox, HashSet<LValueBox>> accessedBefore) {
		for(LValueBox lvb : accessedLVals) {
			this.accessedInAtomic.add(lvb);
		}
		Iterator<LValueBox> accThenMod = accessedThenModInAtomic.iterator();
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
	 */
	public void recordPossibleMod(HashSet<LValueBox> possibleModLVals) {
		// For each already accessed element
		Iterator<LValueBox> alreadyAccessed = accessedInAtomic.iterator();
		while(alreadyAccessed.hasNext()) {
			LValueBox lvb = alreadyAccessed.next();
			// For each possibly modified value
			for(LValueBox possMod : possibleModLVals) {
				// If they may alias, record lvb as possibly modified
				// and add it to accessedBefore
				if(ptrAnalysis.getAliasRelation(possMod, lvb).equals(AliasRelation.NOT_ALIAS)) {
					accessedThenModInAtomic.add(lvb);
					break;
				}
			}
		}
	}
}
