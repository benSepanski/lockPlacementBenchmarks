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
	 * extract all the LValues
	 * and record which atomic segments they are accessed in
	 * 
	 * @param b
	 * @param atomicSegments the atomic segments inside of body b
	 */
	private void extractSharedLValues(Body b, ArrayList<AtomicSegment> atomicSegments) {
		/// For each atomic segment, get all the shared LValues ///////////////
		log.debug("Extracting lvalues from atomic segments of " 
				  + b.getMethod().getName() + " body");
		final JimpleBody body = (JimpleBody) b;
		for(AtomicSegment atomicSeg : atomicSegments) {
			// Get all the LValues in the use and def value boxes in the atomic segment
			Iterator<Unit> unitsInSeg = body.getUnits().iterator(atomicSeg.getFirstUnit(),
																 atomicSeg.getLastUnit());
			ArrayList<ValueBox> valueBoxesInSeg = new ArrayList<>();
			while(unitsInSeg.hasNext()) {
				valueBoxesInSeg.addAll(unitsInSeg.next().getUseAndDefBoxes());
			}
			System.out.println(valueBoxesInSeg);
			HashSet<LValueBox> usedLVals = LValueBox.getAllLValues(valueBoxesInSeg);
			// gather used lvals
			HashSet<LValueBox> usedSharedLVals = new HashSet<>();
			for(LValueBox lvb : usedLVals) {
				// Don't look at the lock manager which we added while marking
				// atomic segments. Also, don't mark primitive locals as shared
				if(lvb.getValue() instanceof Local) {
					Local ell = (Local) lvb.getValue();
					if(ell.getName().equals(AtomicSegmentMarker.lockManagerLocalName)) {
						continue;
					}
					else if(ell.getType() instanceof PrimType)  {
						continue;
					}
				} // Also don't mark primitive parameters as shared
				else if(lvb.getValue() instanceof ParameterRef) {
					if(((ParameterRef) lvb.getValue()).getType() instanceof PrimType) {
						continue;
					}
				}
				usedSharedLVals.add(lvb);
				System.out.println("atomic seg in " + b.getMethod().getName() + " has shared lValue "
								   + lvb.getValue().toString());
			}
			// associate used shared LValues with this atomic segment, and
			// add them to the set of shared LValues
			atomicSegmentToAccessedLValues.put(atomicSeg, usedSharedLVals);
			sharedLValues.addAll(usedSharedLVals);
		}
		///////////////////////////////////////////////////////////////////////
	}
}
