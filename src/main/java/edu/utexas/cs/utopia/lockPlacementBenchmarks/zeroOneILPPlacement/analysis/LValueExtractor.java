package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.Body;
import soot.Unit;
import soot.ValueBox;

/**
 * Extract all LValues
 * from all atomic segments in the method, recording
 * which atomic segments access which shared LValues.
 * We assume shared LValues are only accessed within
 * atomic segments.
 * 
 * @author Ben_Sepanski
 */
class LValueExtractor {
	private final Map<LValueBox, Integer> lValueID = new HashMap<>();
	private final List<LValueBox> lValues = new ArrayList<>();
	private final List<List<Integer>> 
		lValuesInAtomicSegment = new ArrayList<>();
	
	/**
	 * Extract all the lValues accessed in each of the atomic segments
	 * 
	 * @param atomicSegments the list of atomic segments
	 */
	public LValueExtractor(List<AtomicSegment> atomicSegments) {
		for(AtomicSegment atomicSeg : atomicSegments) {
			Set<Integer> accessedLValues = this.extractSharedLValues(atomicSeg);
			List<Integer> asList = new ArrayList<>(accessedLValues);
			this.lValuesInAtomicSegment.add(asList);
		}
	}

	/**
	 * Extract all the LValues from a particular atomic segment
	 * 
	 * @param atomicSeg
	 */
	private Set<Integer> extractSharedLValues(AtomicSegment atomicSeg) {
		Body b = atomicSeg.getBody();
		Iterator<Unit> unitsInSeg = b.getUnits().iterator(atomicSeg.getFirstUnit(),
														  atomicSeg.getLastUnit());
		// For each unit in segment, for each use/def box in unit, check if
		// is an lValue
		Set<Integer> lValueIDs = new HashSet<>();
		LValueBox lVal = new LValueBox();
		int id;
		while(unitsInSeg.hasNext()) {
			for(ValueBox vb : unitsInSeg.next().getUseAndDefBoxes()) {
				if(lVal.canContainValue(vb.getValue())) {
					lVal.setValue(vb.getValue());
					id = getOrMakeID(lVal);
					lValueIDs.add(id);
				}
			}
		}
		return lValueIDs;
	}

	/**
	 * get lvb's id or make an id for lvb and return it
	 * 
	 * @param lvb
	 * @return lvb's id
	 */
	private int getOrMakeID(LValueBox lvb) {
		if(this.lValueID.containsKey(lvb)) {
			return this.lValueID.get(lvb);
		}
		int id = this.lValues.size();
		this.lValueID.put(lvb, id);
		this.lValues.add(lvb);
		return id;
	}

	/**
	 * @return the lValues (ID -> LValue)
	 */
	public List<LValueBox> getLValues() {
		return lValues;
	}

	/**
	 * @return A list whose *i*th entry is the set of LValues
	 *         accessed in atomic segment *i*
	 */
	public List<List<Integer>> getLValuesInAtomicSegment() {
		return lValuesInAtomicSegment;
	}
}
