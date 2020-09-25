package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.Modifier;
import soot.PatchingChain;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethodRef;
import soot.Unit;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;

/**
 * Defines atomic segments as:
 * 		- The entire body of any non-constructor method,
 *         excluding the identity statements
 * 
 * Records all atomic segments in the body and adds a static, thread-local
 * TwoPhaseLockManager field to the class so that
 * nested locking will be feasible.
 * 
 * Note that implementing a generic using soot is tricky because
 * of type erasure. Consequently, the lock manager
 * field is of type java.lang.ThreadLocal, and casts are inserted
 * to maintain type safety.
 * 
 * @author Ben_Sepanski
 */
public class AtomicSegmentExtractor extends BodyTransformer {
	
	private static String lockManagerName = "$threadLocalTwoPhaseLockManager";
	private static SootClass 
		lockManagerClass = Scene.v().getSootClass(TwoPhaseLockManager.class.getName());
	
	private HashMap<Body, ArrayList<AtomicSegment>>
		atomicSegments = new HashMap<Body, ArrayList<AtomicSegment>>();
	private HashMap<SootClass, SootField> 
		classToTwoPhaseLockManager = new HashMap<SootClass, SootField>();
	
	/**
	 * Get the next atomic segment
	 * 
	 * @param body the current body being transformed
	 * @param prevAtomicSegment the previous atomic segment, or null if there is none
	 * @return the next atomic segment, or null if there is none
	 */
	protected AtomicSegment nextAtomicSegment(Body body, AtomicSegment prevAtomicSegment) {
		// Only one atomic segment per method
		if(prevAtomicSegment != null) return null;
		
		// Otherwise, return last non-identity -> last unit
		JimpleBody jimpBody = (JimpleBody) body;
		Unit firstUnit = jimpBody.getFirstNonIdentityStmt();
		Unit lastUnit = jimpBody.getUnits().getLast();
		return new AtomicSegment(jimpBody, firstUnit, lastUnit);
	}
	
	/**
	 * If not already done for this class,
	 * add a static two-phase lock manager field for the class.
	 * Then, return the two-phase lock manager field for the class
	 * 
	 * @param body
	 * @return a static TwoPhaseLockManager field
	 */
	protected SootField getLockManagerField(Body body) {
		SootClass bodyClass = body.getMethod().getDeclaringClass();
		// Add lock manager as field if not already done
		if(!classToTwoPhaseLockManager.containsKey(bodyClass)) {	
			SootField lockManagerField  = new SootField(lockManagerName,
												        lockManagerClass.getType(),
														Modifier.STATIC | Modifier.PRIVATE
														);
			bodyClass.addField(lockManagerField);
			classToTwoPhaseLockManager.put(bodyClass, lockManagerField);
		}	
		// return the field
		return bodyClass.getFieldByName(lockManagerName);
	}

	@Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> phaseOptions) {
		// If a static constructor, initialize this.<lockManagerName>
		JimpleBody jimpBody = (JimpleBody) body;
		if(body.getMethod().getName().equals("<clinit>")) {
			// Make a local lock manager and initialize it
			SootField lockManagerField = this.getLockManagerField(body);
			Local newLockManagerLocal = Jimple.v().newLocal(lockManagerName + "Initializer",
															lockManagerField.getType());
			SootMethodRef lockManagerInitRef = lockManagerClass.getMethod("void <init>()")
															   .makeRef();
			SpecialInvokeExpr initExpr = Jimple.v().newSpecialInvokeExpr(newLockManagerLocal,
																		 lockManagerInitRef);
			InvokeStmt newLockManagerLocalInit = Jimple.v().newInvokeStmt(initExpr);
			// Assign this.lockManager to that initialized local
			StaticFieldRef lockManagerFieldRef = Jimple.v().newStaticFieldRef(lockManagerField.makeRef());
			AssignStmt initializeLockManager = Jimple.v().newAssignStmt(lockManagerFieldRef,
																		newLockManagerLocal);
			// Add the new local to the body
			body.getLocals().add(newLockManagerLocal);
			// Now insert those instructions into the method
			Unit lastNonIdentity = jimpBody.getFirstNonIdentityStmt();
			jimpBody.getUnits().insertAfter(Arrays.asList(newLockManagerLocalInit,
													      initializeLockManager),
										    lastNonIdentity);
			return;
		}
		// If a non-static constructor, nothing to do
		if(body.getMethod().isConstructor()) {
			return;
		}	
		
		// Collect all atomic sections in list
		ArrayList<AtomicSegment> bodyAtomicSegs = new ArrayList<AtomicSegment>();
		AtomicSegment atomicSegment = this.nextAtomicSegment(body, null);
		while(atomicSegment != null) {
			int index = bodyAtomicSegs.size();
			bodyAtomicSegs.add(atomicSegment);
			atomicSegment = this.nextAtomicSegment(body, bodyAtomicSegs.get(index));
		}
		// map this body to its atomic segments
		atomicSegments.put(body,  bodyAtomicSegs);
		
		// Make a local variable and assign a reference to the lock manager
		SootField lockManagerField = this.getLockManagerField(body);
		assert(lockManagerField.isStatic());
		Local lockManagerLocal = Jimple.v().newLocal(lockManagerName,
													 lockManagerField.getType());
		StaticFieldRef lockManagerFieldRef = Jimple.v().newStaticFieldRef(lockManagerField.makeRef());
		AssignStmt lockManagerAssignmentToLocal = Jimple.v().newAssignStmt(lockManagerLocal,
																		   lockManagerFieldRef);
		// Now add the locals and assignment statements to the body
		jimpBody.getLocals().add(lockManagerLocal);
		PatchingChain<Unit> units = jimpBody.getUnits();
		Unit lastNonIdentity = jimpBody.getFirstNonIdentityStmt();
		units.insertAfter(lockManagerAssignmentToLocal, lastNonIdentity);
		
		// Get invocation expressions for atomic entrance/exit
		SootClass lockManagerClass = 
			Scene.v().getSootClass(TwoPhaseLockManager.class.getName());
		SootMethodRef lockManagerEnterRef  = 
			lockManagerClass.getMethod("void enterAtomicSegment()").makeRef();
		SootMethodRef lockManagerExitRef = 
			lockManagerClass.getMethod("void exitAtomicSegment()").makeRef();
		
		InvokeExpr lockManagerEnter = Jimple.v().newVirtualInvokeExpr(lockManagerLocal,
															          lockManagerEnterRef);
		InvokeExpr lockManagerExit = Jimple.v().newVirtualInvokeExpr(lockManagerLocal,
															    	 lockManagerExitRef);
		// Insert invocations for atomic entrance/exit before/after each segment
		for(AtomicSegment as : bodyAtomicSegs) {
			InvokeStmt enterAtomic = Jimple.v().newInvokeStmt(lockManagerEnter);
			units.insertBefore(enterAtomic, as.getFirstUnit());
			InvokeStmt exitAtomic = Jimple.v().newInvokeStmt(lockManagerExit);
			units.insertAfter(exitAtomic, as.getLastUnit());
		}
	}

}
