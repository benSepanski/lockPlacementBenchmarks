package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import soot.Unit;

/**
 * Representation of an atomic segment inside a method.
 * 
 * Simply remembers the first and last unit, along with the
 * body. 
 * 
 * We assume the last unit, along with any return
 * statements inside the atomic segment, dominate the first unit.
 * 
 * We also assume that no shared values are accessed in
 * a return statement.
 * 
 * We assume the method is not static
 * 
 * Does no error checking.
 * 
 * @author Ben_Sepanski
 */
class AtomicSegment {
	private Unit firstUnit, lastUnit;
	
	/**
	 * 
	 * @param firstUnit the first unit in the atomic segment, assumed
	 * 		  to be a unit in sootBody outside of
	 *        any branch/loop statements which dominates lastUnit in
	 * 	      sootBody.BriefUnitGraph();
	 * @param lastUnit the last unit in the atomic segment, assumed
	 *        to be a unit in sootBody outside of any branch/loop
	 *        statements.
	 */
	public AtomicSegment(Unit firstUnit, Unit lastUnit) {
		this.firstUnit = firstUnit;
		this.lastUnit = lastUnit;
	}

	public Unit getFirstUnit() {
		return firstUnit;
	}
	
	public Unit getLastUnit() {
		return lastUnit;
	}
}
