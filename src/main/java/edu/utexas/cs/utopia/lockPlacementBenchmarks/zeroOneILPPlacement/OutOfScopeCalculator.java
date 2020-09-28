package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.SootClass;
import soot.SootMethod;
import soot.Value;
import soot.jimple.AbstractJimpleValueSwitch;
import soot.jimple.ArrayRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.Jimple;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;
import soot.jimple.toolkits.invoke.AccessManager;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.GuaranteedDefs;
import soot.toolkits.scalar.LiveLocals;
import soot.toolkits.scalar.SimpleLiveLocals;

/**
 * Given bodies and their respective atomic segments,
 * as well as a set of LValues, determine which LValues
 * are out of scope at the beginning of each atomic segment
 * 
 * @author Ben_Sepanski
 *
 */
public class OutOfScopeCalculator {
	
	private final HashMap<AtomicSegment, HashSet<LValueBox>> 
		outOfScope = new HashMap<>();
	
	/**
	 * Compute which shared lValues are out of scope
	 * at the beginning of the given atomic segments
	 * 
	 * @param atomicSegments the atomic segments and their bodies
	 * @param lValues the shared lValues
	 */
	public OutOfScopeCalculator(HashMap<Body, ArrayList<AtomicSegment>> atomicSegments,
							    HashSet<LValueBox> lValues) {
		// For each body
		for(Entry<Body, ArrayList<AtomicSegment>> entr : atomicSegments.entrySet()) {
			Body b = entr.getKey();
			final ExceptionalUnitGraph euGraph = new ExceptionalUnitGraph(b);
			final GuaranteedDefs bGuaranteedDefs = new GuaranteedDefs(euGraph);
			// For each atomic segment in that body
			for(AtomicSegment atomicSeg : entr.getValue()) {
				// Compute the outOfScope for that body
				computeOutOfScope(b, bGuaranteedDefs, atomicSeg, lValues);
			}
		}
	}
	
	/**
	 * Return the subset of shared lValues which are not in scope
	 * at the beginning of atomicSeg, or null if atomicSeg is
	 * not recognized
	 * 
	 * @param atomicSeg
	 * @return
	 */
	public HashSet<LValueBox> getOutOfScope(AtomicSegment atomicSeg) {
		return outOfScope.get(atomicSeg);
	}
	
	/**
	 * Determine the subset of lValues which are out of scop
	 * 
	 * @param b the method body holding the atomic segment
	 * @param bodyLiveLocals a live locals analysis of b
	 * @param atomicSeg the atomic segment
	 * @param lValues all possible shared values to consider
	 */
	private void computeOutOfScope(final Body b,
								   final GuaranteedDefs bodyDefs,
								   final AtomicSegment atomicSeg, 
								   final HashSet<LValueBox> lValues) {
		// Get locals that are defined
		@SuppressWarnings("unchecked")
		final List<Local> guaranteedDefs = bodyDefs.getGuaranteedDefs(atomicSeg.getFirstUnit());
		final HashSet<Local> guaranteedDefsSet = new HashSet<>(guaranteedDefs);
		// Get body method and class
		final SootMethod bMethod = b.getMethod();
		final SootClass bClass = b.getMethod().getDeclaringClass();

		/// Make a switch to test inScope /////////////////////////////////////
		AbstractJimpleValueSwitch inScope = new AbstractJimpleValueSwitch() {

			boolean isInScope = false;
			@Override public Object getResult() {return isInScope;}
			
			@Override public void caseLocal(Local v) {
				isInScope = guaranteedDefsSet.contains(v);
			}
			@Override public void caseInstanceFieldRef(InstanceFieldRef v) {
				isInScope = AccessManager.isAccessLegal(bMethod, v.getField());
			}
			@Override public void caseParameterRef(ParameterRef v) {
				isInScope = b.getParameterRefs().contains(v);
			}
			@Override public void caseStaticFieldRef(StaticFieldRef v) {
				isInScope = AccessManager.isAccessLegal(bMethod, v.getField());
			}
			@Override public void caseThisRef(ThisRef v) {
				v.equivTo(Jimple.v().newThisRef(bClass.getType()));
			}
			@Override public void caseArrayRef(ArrayRef v) {
				v.getBase().apply(this);
			}
			@Override public void defaultCase(Object v) {
				throw new RuntimeException("v must be an lvalue");
			}
		};
		///////////////////////////////////////////////////////////////////////
		
		// Go through all the lValues, and record the ones that are not
		// in scope
		HashSet<LValueBox> notInScope = new HashSet<>();
		for(LValueBox lvb : lValues) {
			lvb.getValue().apply(inScope);
			if(!(Boolean) inScope.getResult()) {
				notInScope.add(lvb);
			}
		}
		outOfScope.put(atomicSeg, notInScope);
	}

}
