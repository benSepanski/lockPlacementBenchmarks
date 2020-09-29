package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;

import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.ValueBox;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.SpecialInvokeExpr;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
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
public class AccessedBeforeRelation extends ForwardFlowAnalysis<Unit, AccessedThenModifiedSet> {	
	private static SootClass lockManagerClass = Scene.v().getSootClass(
		"edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.TwoPhaseLockManager");
	private static SootMethod 
		enterAtomicMethod = lockManagerClass.getMethod("void enterAtomicSegment()"),
		exitAtomicMethod = lockManagerClass.getMethod("void exitAtomicSegment()");
	private static CollectionFlowUniverse<LValueBox>
		emptyUniv = new CollectionFlowUniverse<>(new HashSet<LValueBox>());
	
	private PointerAnalysis ptrAnalysis;
	private HashSet<LValueBox> sharedLValues;
	private CollectionFlowUniverse<LValueBox> univ;

	public AccessedBeforeRelation(PointerAnalysis ptrAnalysis, Body b, HashSet<LValueBox> sharedLValues) 
	{
		super(new ExceptionalUnitGraph(b));		
		this.ptrAnalysis = ptrAnalysis;
		this.sharedLValues = sharedLValues;
		this.univ = new CollectionFlowUniverse<LValueBox>(sharedLValues);
		this.doAnalysis();
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
		// If at the start/end of an atomic segment, change
		// the universe to the lvalues/the empty universe. In latter case return
		if(d instanceof InvokeStmt) {
			InvokeStmt invk = (InvokeStmt) d;
			if(invk.getInvokeExpr().getMethod().equals(enterAtomicMethod)) {
				out = new AccessedThenModifiedSet(univ, ptrAnalysis);
			}
			else if(invk.getInvokeExpr().getMethod().equals(exitAtomicMethod)) {
				out = new AccessedThenModifiedSet(emptyUniv, null);
				return;
			}
		}
		// Now if considering empty universe (i.e. we're not in an atomic section),
		// out will be the same as in
		if(in.getUniverse().equals(emptyUniv)) {
			out = new AccessedThenModifiedSet(emptyUniv, null);
			return;
		}
		// Otherwise, we are inside an atomic segment.
		// Copy in into out
		out = new AccessedThenModifiedSet(univ, ptrAnalysis);
		in.copy(out);
		// Look at use and defs to record what gets accessed
		HashSet<LValueBox> useAndDefBoxes = LValueBox.getAllLValues(d.getUseAndDefBoxes());
		useAndDefBoxes.retainAll(sharedLValues);
		out.recordAccess(useAndDefBoxes);
		// Look at defs to record what might get modified
		HashSet<LValueBox> defBoxes = LValueBox.getAllLValues(d.getDefBoxes());
		defBoxes.retainAll(sharedLValues);
		out.recordPossibleMod(defBoxes);
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
	public ArrayPackedSet<LValueBox> accessedInAtomic;
	public FlowSet<LValueBox> accessedThenModInAtomic;
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
		in1.copy(this); // copy in1 into this
		// union in2 into this
		this.accessedInAtomic.union(in2.accessedInAtomic);
		this.accessedThenModInAtomic.union(in2.accessedThenModInAtomic);
	}
	/**
	 * Record all the LValues in accessedLVals as accessed
	 * in the atomic section
	 * 
	 * @param accessedLVals
	 */
	public void recordAccess(HashSet<LValueBox> accessedLVals) {
		for(LValueBox lvb : accessedLVals) {
			this.accessedInAtomic.add(lvb);
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
				if(ptrAnalysis.getAliasRelation(possMod, lvb) != AliasRelation.NOT_ALIAS) {
					accessedThenModInAtomic.add(lvb);
					break;
				}
			}
		}
	}
}
