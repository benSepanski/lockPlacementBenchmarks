package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.common.base.Objects;

import soot.Body;
import soot.Local;
import soot.SootClass;
import soot.SootMethod;
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

/**
 * Given bodies and their respective atomic segments,
 * as well as a set of LValues, determine which LValues
 * are out of scope at the beginning of each atomic segment
 * 
 * @author Ben_Sepanski
 *
 */
class OutOfScopeCalculator {
	
	private final List<List<Integer>> outOfScope = new ArrayList<>();
	
	/**
	 * Compute which shared lValues are out of scope
	 * at the beginning of the given atomic segments.
	 * 
	 * This will run faster if atomic segments from the same
	 * body are adjacent in atomicSegments
	 * 
	 * @param atomicSegments the atomic segments
	 * @param lValues the list of all lvalues
	 */
	public OutOfScopeCalculator(List<AtomicSegment> atomicSegments,
							    List<LValueBox> lValues) {
		GuaranteedDefs bodyGuaranteedDefs = null;
		Body prevBody = null;
		for(AtomicSegment atomicSeg : atomicSegments) {
			// Get guaranteed defs (re-use if already have it)
			final Body b = atomicSeg.getBody();
			if(!Objects.equal(prevBody, b)) {
				prevBody = b;
				ExceptionalUnitGraph euGraph = new ExceptionalUnitGraph(b);
				bodyGuaranteedDefs = new GuaranteedDefs(euGraph);
			}
			
			/// Make a switch to test inScope /////////////////////////////////////
			final SootMethod bMethod = b.getMethod();
			final SootClass bClass = bMethod.getDeclaringClass();
			final Set<Local> guaranteedDefs = new HashSet<>();
			@SuppressWarnings("unchecked")
			List<Local> defList = bodyGuaranteedDefs.getGuaranteedDefs(atomicSeg.getFirstUnit());
			guaranteedDefs.addAll(defList);
			
			AbstractJimpleValueSwitch inScope = new AbstractJimpleValueSwitch() {
				boolean isInScope = false;
				@Override public Object getResult() {return isInScope;}
				
				@Override public void caseLocal(Local v) {
					isInScope = guaranteedDefs.contains(v);
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
			// Determine which values are out of scope
			List<Integer> atomicSegOutOfScope = new ArrayList<>();
			for(int i = 0; i < lValues.size(); ++i) {
				lValues.get(i).getValue().apply(inScope);
				boolean defined = (Boolean) inScope.getResult();
				if(!defined) {
					atomicSegOutOfScope.add(i);
				}
			}
			this.outOfScope.add(atomicSegOutOfScope);
		}
	}
	
	/**
	 * @return the *i*th entry is the set of all lValues *j*
	 *         which are out of scope at the beginning of
	 *         atomic segment *i*
	 */
	public List<List<Integer>> getOutOfScope() {
		return outOfScope;
	}
}
