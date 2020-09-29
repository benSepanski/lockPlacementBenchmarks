package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;
import soot.Local;
import soot.PrimType;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AbstractJimpleValueSwitch;
import soot.jimple.ArrayRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.JimpleBody;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.CombinedDUAnalysis;

/**
 * Extract (possibly) shared LValues
 * from all atomic segments in the method, recording
 * which atomic segments access which shared LValues.
 * We assume shared LValues are only accessed within
 * atomic segments.
 * 
 * @author Ben_Sepanski
 */
public class SharedLValuesExtractor {
	private static final Logger 
		log = LoggerFactory.getLogger(SharedLValuesExtractor.class);

	private final HashSet<LValueBox> sharedLValues = new HashSet<>();
	private final HashMap<AtomicSegment, HashSet<LValueBox>> 
		atomicSegmentToAccessedLValues = new HashMap<>();
	
	/**
	 * Given a map holding all atomic segments and their
	 * associated bodies, extract
	 * all of the (possibly) shared LValues from the atomic
	 * segments
	 * 
	 * @param bodyToAtomicSegments
	 */
	public SharedLValuesExtractor(Map<Body, ArrayList<AtomicSegment>> bodyToAtomicSegments) {
		for(Body b : bodyToAtomicSegments.keySet()) {
			this.extractSharedLValues(b, bodyToAtomicSegments.get(b));
		}
	}

	/**
	 * Get all the LValues accessed in atomic segments which might
	 * be shared with other concurrent threads
	 * 
	 * @return A set containing all LValues accessed in atomic segments
	 *         which are shared, and possibly some non-shared LValues
	 */
	public HashSet<LValueBox> getSharedLValues() {
		return sharedLValues;
	}
	
	/**
	 * Get a mapping from atomic segments to
	 *  all the LValues accessed in the segment
	 * 
	 * @return
	 */
	public HashMap<AtomicSegment, HashSet<LValueBox>> getLValuesAccessedIn() {
		return atomicSegmentToAccessedLValues;
	}

	/**
	 * For a particular body with given atomic segments,
	 * extract all the LValues which might be shared,
	 * and record which atomic segments they are accessed in
	 * 
	 * @param b
	 * @param atomicSegments the atomic segments inside of body b
	 */
	private void extractSharedLValues(Body b, ArrayList<AtomicSegment> atomicSegments) {
		// Build a DUAnalysis for determining shared variables
		log.debug("Building CombinedDUAnalysis for " + b.getMethod().getName() + " body");
		final JimpleBody body = (JimpleBody) b;
		final ExceptionalUnitGraph cfUnitGraph = new ExceptionalUnitGraph(body);
		final CombinedDUAnalysis duAnalysis = new CombinedDUAnalysis(cfUnitGraph);
		
		/// Make a test for shared values /////////////////////////////////////
		AbstractJimpleValueSwitch sharedTest = new AbstractJimpleValueSwitch() {
			boolean maybeShared = false;
			// We need this map to avoid looping forever during recursion
			private HashSet<Value> beingEvaluated = new HashSet<>();
			private HashMap<Value, Boolean> valueToMaybeShared = new HashMap<>();
			@Override public Object getResult() {
				return maybeShared;
			}
			
			// Locals are maybe shared if they are ever assigned
			// to a shared variable.
			// We over-approximate this by just saying it is maybe shared
			// if it is assigned to a rhs-expression which involves a
			// shared LValue (not including inside of an array access,
			//                e.g. if v = A[i], then we only check if
			//                A is maybeShared)
			@Override public void caseLocal(Local v) {
				// Short-circuit recursion
				if(valueToMaybeShared.containsKey(v)) {
					maybeShared = valueToMaybeShared.get(v);
					return;
				}
				// If we are currently evaluating v, we have no evidence that
				// it is shared yet
				else if(beingEvaluated.contains(v)) {
					maybeShared = false;
					return;
				}
				// record this variable as being evaluated
				beingEvaluated.add(v);
				// Get the LValues involved in definitions of this variable
				ArrayList<ValueBox> useBoxesInDefsOfv = new ArrayList<>();
				for(Unit stmt : body.getUnits()) {
					for(Unit defStmt : duAnalysis.getDefsOfAt(v, stmt)) {
						useBoxesInDefsOfv.addAll(defStmt.getUseBoxes());
					}
				}
				HashSet<LValueBox> lValuesInRHS = LValueBox.getAllLValues(useBoxesInDefsOfv);
				// If any RHS-values are shared, mark this local as maybeShared
				for(LValueBox lValBox : lValuesInRHS) {
					lValBox.getValue().apply(this);
					if((Boolean) this.getResult()) {
						valueToMaybeShared.put(v, true);
						maybeShared = true;				
						beingEvaluated.remove(v);
						return;
					}
				}
				// Otherwise, mark this local as not shared
				valueToMaybeShared.put(v, false);
				maybeShared = false;
				beingEvaluated.remove(v);
			}
			@Override public void caseInstanceFieldRef(InstanceFieldRef v) {
				// If we already know the result, return it
				if(valueToMaybeShared.containsKey(v)) {
					maybeShared = valueToMaybeShared.get(v);
					return;
				}
				// If we are currently evaluating this, then we have no evidence
				// that it is shared yet
				else if(beingEvaluated.contains(v)) {
					maybeShared = false;
					return;
				}
				// Otherwise, recursively see if the base of the field ref
				// is maybe shared
				beingEvaluated.add(v);
				v.getBase().apply(this);
				maybeShared = (Boolean) this.getResult();
				valueToMaybeShared.put(v, maybeShared);
				beingEvaluated.remove(v);
			}
			@Override public void caseParameterRef(ParameterRef v) {
				// A parameter is passed by value, so is only possibly
				// shared if it is not primitive
				maybeShared = !(v.getType() instanceof PrimType);
			}
			@Override public void caseStaticFieldRef(StaticFieldRef v) {
				maybeShared = true;
			}
			@Override public void caseThisRef(ThisRef v) {
				maybeShared = true;
			}
			// maybeShared if the base is maybe shared
			@Override public void caseArrayRef(ArrayRef v) {
				// If we already know the result, return it
				if(valueToMaybeShared.containsKey(v)) {
					maybeShared = valueToMaybeShared.get(v);
					return;
				}
				// If we are currently evaluating this, then we have no evidence
				// that it is shared yet
				else if(beingEvaluated.contains(v)) {
					maybeShared = false;
					return;
				}
				// Otherwise, recursively see if the base of the array ref
				// is maybe shared
				beingEvaluated.add(v);
				v.getBase().apply(this);
				maybeShared = (Boolean) this.getResult();
				valueToMaybeShared.put(v, maybeShared);
				beingEvaluated.remove(v);
			}
			@Override public void defaultCase(Object v) {
				throw new RuntimeException("v must be an LValue");
			}
		};
		///////////////////////////////////////////////////////////////////////
		
		/// For each atomic segment, get all the shared LValues ///////////////
		log.debug("Extracting lvalues from atomic segments of " 
				  + b.getMethod().getName() + " body");
		for(AtomicSegment atomicSeg : atomicSegments) {
			// Get all the LValues in the use and def value boxes in the atomic segment
			Iterator<Unit> unitsInSeg = body.getUnits().iterator(atomicSeg.getFirstUnit(),
																 atomicSeg.getLastUnit());
			ArrayList<ValueBox> valueBoxesInSeg = new ArrayList<>();
			while(unitsInSeg.hasNext()) {
				valueBoxesInSeg.addAll(unitsInSeg.next().getUseAndDefBoxes());
			}
			HashSet<LValueBox> usedLVals = LValueBox.getAllLValues(valueBoxesInSeg);
			// gather used lvals which might be shared
			HashSet<LValueBox> usedSharedLVals = new HashSet<>();
			for(LValueBox lvb : usedLVals) {
				lvb.getValue().apply(sharedTest);
				if((Boolean) sharedTest.getResult()) {
					usedSharedLVals.add(lvb);
					System.out.println("atomic seg in " + b.getMethod().getName() + " has shared lValue "
									   + lvb.getValue().toString());
				}
			}
			// associate used shared LValues with this atomic segment, and
			// add them to the set of shared LValues
			atomicSegmentToAccessedLValues.put(atomicSeg, usedSharedLVals);
			sharedLValues.addAll(usedSharedLVals);
		}
		///////////////////////////////////////////////////////////////////////
	}
}
