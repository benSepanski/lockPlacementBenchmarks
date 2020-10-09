package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis;

import soot.Body;
import soot.Unit;

/**
 * Representation of an atomic segment inside a monitor
 * 
 * We assume the last unit, along with any return
 * statements inside the atomic segment, dominate the first unit.
 * 
 * We also assume that no shared values are accessed in
 * a return statement.
 * 
 * We assume the method is not static
 * 
 * Performs minimal error checking.
 * 
 * @author Ben_Sepanski
 */
public class AtomicSegment {
	private final Body b;
	private final Unit firstUnit, lastUnit;
	
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
	public AtomicSegment(Body b, Unit firstUnit, Unit lastUnit) {
		this.b = b;
		this.firstUnit = firstUnit;
		this.lastUnit = lastUnit;
	}

	/**
	 * @return the body
	 */
	public Body getBody() {
		return b;
	}

	/**
	 * @return the firstUnit
	 */
	public Unit getFirstUnit() {
		return firstUnit;
	}

	/**
	 * @return the lastUnit
	 */
	public Unit getLastUnit() {
		return lastUnit;
	}
}
