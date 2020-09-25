package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import soot.jimple.JimpleBody;
import soot.Unit;

/**
 * Representation of an atomic segment inside a method. 
 * 
 * Simply remembers the first and last unit, along with the
 * body.
 * 
 * Does no error checking.
 * 
 * @author Ben_Sepanski
 */
public class AtomicSegment {
	private JimpleBody sootBody;
	private Unit firstUnit, lastUnit;
	
	/**
	 * 
	 * @param sootBody 
	 * @param firstUnit the first unit in the atomic segment, assumed
	 * 		  to be a unit in sootBody outside of
	 *        any branch/loop statements which dominates lastUnit in
	 * 	      sootBody.BriefUnitGraph();
	 * @param lastUnit the last unit in the atomic segment, assumed
	 *        to be a unit in sootBody outside of any branch/loop
	 *        statements.
	 */
	public AtomicSegment(JimpleBody sootBody, Unit firstUnit, Unit lastUnit) {
		this.sootBody = sootBody;
		this.firstUnit = firstUnit;
		this.lastUnit = lastUnit;
	}

	public Unit getFirstUnit() {
		return firstUnit;
	}
	
	public Unit getLastUnit() {
		return lastUnit;
	}
	
	public JimpleBody getSootBody() {
		return sootBody;
	}
}
