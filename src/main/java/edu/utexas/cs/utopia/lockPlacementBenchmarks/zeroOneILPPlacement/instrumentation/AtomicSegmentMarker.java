package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.instrumentation;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.AtomicSegment;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethodRef;
import soot.Unit;
import soot.UnitPatchingChain;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.NewExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.SpecialInvokeExpr;

/**
 * Assumes that the class has at least one <init> method
 * 
 * Adds a private
 * TwoPhaseLockManager field to the class so that
 * nested locking will be feasible.
 * Adds a enterAtomicSegment() before each atomic segment
 * and exitAtomicSegment() after each atomic segment,
 * and immediately before any return statement inside an atomic segment
 * 
 * Adds initialization of the new field to each <init> method
 * 
 * @author Ben_Sepanski
 */
public class AtomicSegmentMarker extends BodyTransformer {
	private static Logger log = LoggerFactory.getLogger(AtomicSegmentMarker.class);
	
	// The name of the field which will hold the lock manager
	private static final String lockManagerName = "$2phaseLockMngr";
	// Each method with atomic segments makes a local which is a reference
	// to the lock manager. That local has the following name:
	public static final String lockManagerLocalName = lockManagerName + "$local";
	private static final SootClass 
		lockManagerClass = Scene.v().getSootClass(TwoPhaseLockManager.class.getName());
	
	// list of all atomic segments
	private final List<AtomicSegment> atomicSegments;
	// map class to its 2-phase lock manager
	private final Map<SootClass, SootField> classTo2PhaseLM = new HashMap<>();
	
	public AtomicSegmentMarker(List<AtomicSegment> atomicSegments) {
		this.atomicSegments = atomicSegments;
	}
	
	/**
	 * If not already done for this class,
	 * add a two-phase lock manager field for the class.
	 * 
	 * Then, return the two-phase lock manager field for the class
	 * 
	 * @param body
	 * @return a TwoPhaseLockManager field
	 */
	protected SootField getLockManagerField(Body body) {
		SootClass bodyClass = body.getMethod().getDeclaringClass();
		// Add lock manager as a field if not already done
		if(!classTo2PhaseLM.containsKey(bodyClass)) {	
			SootField lockManagerField  = new SootField(lockManagerName,
												        lockManagerClass.getType(),
														Modifier.PRIVATE
														);
			bodyClass.addField(lockManagerField);
			classTo2PhaseLM.put(bodyClass, lockManagerField);
			
			// Make sure the lock manager
		}
		// return the field
		return bodyClass.getFieldByName(lockManagerName);
	}

	@Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> phaseOptions) {
		log.debug("Marking atomic segments (if any) in " + body.getMethod().getName());
		/// If a  constructor, add code to               //////////////////////
		/// initialize this.<lockManagerName> and return //////////////////////
		JimpleBody jimpBody = (JimpleBody) body;
		if(body.getMethod().getName().equals("<init>")) {
			// Make a local lock manager
			SootField lockManagerField = this.getLockManagerField(body);
			Local newLockManagerLocal = Jimple.v().newLocal(lockManagerLocalName,
															lockManagerField.getType());
			RefType lockManagerRefType = soot.RefType.v(lockManagerField.getType().toString());
			NewExpr localNewExpr = Jimple.v().newNewExpr(lockManagerRefType);
			AssignStmt localNewStmt = Jimple.v().newAssignStmt(newLockManagerLocal, localNewExpr);
			// Initialize the lock manager
			SootMethodRef lockManagerInitRef = lockManagerClass.getMethod("void <init>()")
															   .makeRef();
			SpecialInvokeExpr initExpr = Jimple.v().newSpecialInvokeExpr(newLockManagerLocal,
																		 lockManagerInitRef);
			InvokeStmt localInitStmt = Jimple.v().newInvokeStmt(initExpr);
			// Assign this.lockManager to that initialized local
			InstanceFieldRef lockManagerFieldRef = Jimple.v()
					.newInstanceFieldRef(body.getThisLocal(), lockManagerField.makeRef());
			AssignStmt initializeLockManager = Jimple.v().newAssignStmt(lockManagerFieldRef,
																		newLockManagerLocal);
			// Add the new local to the body
			body.getLocals().add(newLockManagerLocal);
			// Now insert those instructions into the method
			if(jimpBody.getUnits().size() > 0) {
				Unit lastNonIdentity = jimpBody.getFirstNonIdentityStmt();
				jimpBody.getUnits().insertAfter(Arrays.asList(localNewStmt,
														  	  localInitStmt,
													          initializeLockManager),
										        lastNonIdentity);
			}
			else {
				jimpBody.getUnits().addAll(Arrays.asList(localNewStmt,
														 localInitStmt,
														 initializeLockManager));
			}
			return;
		}
		///////////////////////////////////////////////////////////////////////
		// If a static constructor, nothing to do
		if(body.getMethod().getName().equals("<clinit>")) {
			return;
		}	
		
		
		// Make a local variable and assign the lock manager to that
		// local. If this body has atomic segments, we will add this
		// local to the body
		SootField lockManagerField = this.getLockManagerField(body);
		Local lockManagerLocal = Jimple.v().newLocal(lockManagerLocalName,
													 lockManagerField.getType());
		InstanceFieldRef lockManagerFieldRef = Jimple.v()
				.newInstanceFieldRef(body.getThisLocal(), lockManagerField.makeRef());
		AssignStmt lockManagerAssignmentToLocal = Jimple.v().newAssignStmt(lockManagerLocal,
																		   lockManagerFieldRef);
				
		UnitPatchingChain units = body.getUnits();
		/// For each atomic section in this body //////////////////////////////
		boolean hasAtomicSegment = false;
		for(AtomicSegment atSeg : atomicSegments) {
			if(!body.equals(atSeg.getBody())) continue;
			// atomic segment is in this body
			hasAtomicSegment = true;
			Unit first = atSeg.getFirstUnit(),
				 last = atSeg.getLastUnit();
			
			// insert enter atomic
			units.insertBefore(getNewEnterAtomicStmt(lockManagerLocal), first);
			
			// insert exit atomic immediately before return statements
			// and after the last unit in the atomic segment (if the
			// last unit is not a return statement)
			Iterator<Unit> atUnitIter = units.iterator(first, last);
			while(atUnitIter.hasNext()) {
				Unit atUnit = atUnitIter.next();
				boolean isLast = atUnit.equals(last);
				
				if(atUnit instanceof ReturnStmt || atUnit instanceof ReturnVoidStmt) {
					units.insertBefore(getNewExitAtomicStmt(lockManagerLocal), atUnit);
				}
				else if (isLast) {
					units.insertAfter(getNewExitAtomicStmt(lockManagerLocal), atUnit);
				}
				
				if(isLast) break;
			}
		}
		///////////////////////////////////////////////////////////////////////
		
		// Now add the locals and assignment statements to the body if it had
		// any atomic segments
		if(hasAtomicSegment) {
			jimpBody.getLocals().add(lockManagerLocal);
			Unit firstNonIdentity = jimpBody.getFirstNonIdentityStmt();
			units.insertBefore(lockManagerAssignmentToLocal, firstNonIdentity);
		}
	}
	
	/**
	 * Get a statement which invokes the enterAtomicSegment of the
	 * given lockManagerLocal
	 * 
	 * @param lockManagerLocal a TwoPhaseLockManager
	 * @return
	 */
	private InvokeStmt getNewEnterAtomicStmt(Local lockManagerLocal) {
		SootMethodRef lockManagerEnterRef  = 
				lockManagerClass.getMethod("void enterAtomicSegment()").makeRef();
		InvokeExpr lockManagerEnter = Jimple.v()
				.newVirtualInvokeExpr(lockManagerLocal, lockManagerEnterRef);
		return Jimple.v().newInvokeStmt(lockManagerEnter);
	}
	
	/**
	 * Get a statement which invokes the exitAtomicSegment of the
	 * given lockManagerLocal
	 * 
	 * @param lockManagerLocal a TwoPhaseLockManager
	 * @return
	 */
	private InvokeStmt getNewExitAtomicStmt(Local lockManagerLocal) {
		SootMethodRef lockManagerExitRef  = 
				lockManagerClass.getMethod("void exitAtomicSegment()").makeRef();
		InvokeExpr lockManagerEnter = Jimple.v()
				.newVirtualInvokeExpr(lockManagerLocal, lockManagerExitRef);
		return Jimple.v().newInvokeStmt(lockManagerEnter);
	}

}
