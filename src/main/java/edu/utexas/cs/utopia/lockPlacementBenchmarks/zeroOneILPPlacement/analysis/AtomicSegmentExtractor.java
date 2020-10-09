package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import soot.Body;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.JimpleBody;

/**
 * We assume that non-constructor, non-static
 * methods are of the form ({...})?(waituntil(predicate method) {...:})*
 * 
 * We also assume that every method which has the name
 * "waituntil" is waituntil, and that every a method
 * is a predicate method iff it begins with PREDICATE_PREFIX
 * 
 * We assume predicate methods take no arguments
 * 
 * Defines atomic segments as:
 * 		- Points in any non-constructor, non-static,
 * 		  method
 * 	      which begin with <first non-identity statement>
 *        XOR <a call to a predicate method
 * 	      followed by a call to waituntil>
 * 		  and end immediately before the end of the
 * 		  function or <a call to another predicate method followed
 * 		  by a call to waituntil>
 * 
 * Records all atomic segments in methods of a given class
 * 
 * @author Ben_Sepanski
 */
class AtomicSegmentExtractor {
	public static final String PREDICATE_PREFIX = "waituntil$";
	private final List<AtomicSegment> atomicSegments;
	
	public AtomicSegmentExtractor(SootClass sClass) {
		atomicSegments = new ArrayList<AtomicSegment>();
		for(SootMethod meth : sClass.getMethods()) {
			extractAtomicSegments(meth);
		}
	}
	
	/**
	 * If has no body, is static, or a constructor
	 * method then has no atomic segments.
	 * 
	 * Otherwise records all atomic segments according to
	 * nextAtomicSegment
	 * 
	 * @param mthd
	 */
	private void extractAtomicSegments(SootMethod mthd) {
		if(!mthd.hasActiveBody() || mthd.isStatic() || mthd.isConstructor()) {
			return;
		}	
		Body b = mthd.getActiveBody();
		
		// Collect all atomic sections
		AtomicSegment atomicSegment = this.nextAtomicSegment(b, null);
		while(atomicSegment != null) {
			atomicSegments.add(atomicSegment);
			atomicSegment = this.nextAtomicSegment(b, atomicSegment);
		}
	}
	
	/**
	 * @param ut
	 * @return true iff ut is an assignment to a local of the result of a predicate method
	 */
	private boolean isPredicateAssignment(Unit ut) {
		if(!(ut instanceof AssignStmt)) return false;
		AssignStmt asgn = (AssignStmt) ut;
		Value rightOp = asgn.getRightOp();
		if(!(rightOp instanceof InvokeExpr)) return false;
		InvokeExpr invk = (InvokeExpr) rightOp;
		return invk.getMethod().getName().startsWith(PREDICATE_PREFIX);
	}
	
	/**
	 * @param ut
	 * @return true iff ut is an invocation of a waituntil
	 */
	private boolean isWaitUntil(Unit ut) {
		if(!(ut instanceof InvokeStmt)) return false;
		return "waituntil".equals(((InvokeStmt) ut).getInvokeExpr().getMethod().getName());
	}
	
	/**
	 * Does the unit begin an atomic segment (i.e. is the call
	 * to a predicate method or the first unit of jb)
	 * @param jb 
	 * @param ut
	 * @return
	 */
	private boolean beginsAtomicSegment(JimpleBody jb, Unit ut) {
		if(ut.equals(jb.getFirstNonIdentityStmt())) return true;
		Unit nextUnit = jb.getUnits().getSuccOf(ut);
		if(nextUnit == null) return false;
		return (isPredicateAssignment(ut) && isWaitUntil(nextUnit));
	}
	
	/**
	 * Get the next atomic segment. We assume that these
	 * atomic segments only begin on or after the first non-identity
	 * statement in the body
	 * 
	 * @param body the current body being transformed
	 * @param prevAtomicSegment the previous atomic segment, or null if there is none
	 * @return the next atomic segment, or null if there is none
	 */
	protected AtomicSegment nextAtomicSegment(Body body, AtomicSegment prevAtomicSegment) {
		JimpleBody jimpBody = (JimpleBody) body;
		// If already got to last unit, we are done
		if(prevAtomicSegment != null 
		   && prevAtomicSegment.getLastUnit().equals(body.getUnits().getLast())) {
			return null;
		}
		Unit firstUnit;
		if(prevAtomicSegment == null) {
			firstUnit = jimpBody.getFirstNonIdentityStmt();
		}
		else {
			firstUnit = jimpBody.getUnits().getSuccOf(prevAtomicSegment.getLastUnit());
		}
		String errorMsg = "non-static, non-constructor, non predicate"
				+ " methods must begin with an assignment of a predicate";
		if(!beginsAtomicSegment(jimpBody, firstUnit)) {
			throw new RuntimeException(errorMsg + ".\n Encountered " + firstUnit);
		}
		Unit nextUnit = jimpBody.getUnits().getSuccOf(firstUnit);

		// move along until we hit the next atomic segment
		Iterator<Unit> unitIter = jimpBody.getUnits().iterator(nextUnit);
		Unit lastUnit = firstUnit;
		while(unitIter.hasNext()) {
			Unit nxt = unitIter.next();
			if(beginsAtomicSegment(jimpBody, nxt)) {
				break;
			}
			lastUnit = nxt;
		}
		return new AtomicSegment(body, firstUnit, lastUnit);
	}
	
	/**
	 * 
	 * @return all atomic segments
	 */
	public List<AtomicSegment> getAtomicSegments() {
		return atomicSegments;
	}

}
