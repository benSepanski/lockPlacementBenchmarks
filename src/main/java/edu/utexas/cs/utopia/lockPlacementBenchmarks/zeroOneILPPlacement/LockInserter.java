package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.base.Objects;

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.NullType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;

/**
 * We assert any classes which are given a local lock
 * must have a constructor
 * 
 * @author Ben_Sepanski
 *
 */
public class LockInserter extends BodyTransformer {
	private static Logger log = LoggerFactory.getLogger(LockInserter.class);
	// We want this to be the lock manager class
	private static final SootClass 
		lockManagerClass = Scene.v().getSootClass(TwoPhaseLockManager.class.getName());
	private static final SootMethod
		obtainLockMethod = lockManagerClass.getMethod("void obtainLock(java.util.concurrent.locks.ReentrantLock)");
	
	// Locks are ordered to avoid deadlock
	private HashMap<LValueBox, Integer> lockOrder = new HashMap<>();
	// order locks according to lock order
	private Comparator<LValueLock> lockComparator;
	// the lock assignment we will compute
	private HashMap<LValueBox, LValueLock> lockAssignment;
	// the atomic segments we are given
	private HashMap<Body, ArrayList<AtomicSegment>> atomicSegments;
	// the set of accessedIn relations
	private HashMap<AtomicSegment, HashSet<LValueBox>> accessedIn;
	
	/**
	 * Use a DFS to build a lock ordering such that
	 * if v accessedBefore w and w not accessedBefore v,
	 * v < w
	 * 
	 * @param curNode
	 * @param accessedBefore
	 * @param nextNumber the number to be assigned, decreasing from n,n-1,...,1
	 */
	private int buildTopoSortOrder(LValueBox curNode,
								   HashMap<LValueBox, HashSet<LValueBox>> accessedBefore,
								   int nextNumber) {
		if(lockOrder.containsKey(curNode)) return nextNumber;
		// Mark this node as being visited and visit its neighbors
		lockOrder.put(curNode, -1);
		for(LValueBox nbr : accessedBefore.get(curNode)) {
			if(lockOrder.containsKey(nbr)) continue;
			nextNumber = buildTopoSortOrder(nbr, accessedBefore, nextNumber);
		}
		// Now that everything after this node has been given a number,
		// give this node the next number
		lockOrder.put(curNode, nextNumber--);
		return nextNumber;
	}

	/**
	 * Store the lock assignment and atomic segments and
	 * order the locks
	 * 
	 * @param lockAssignment Indicate which local or global lock to use for each lValue
	 * @param atomicSegs Give the atomic segments
	 * @param accessedBefore z -> {w | z accessedBefore w}, used to order locks
	 */
	public LockInserter(HashMap<LValueBox, LValueLock> lockAssignment,
						HashMap<Body, ArrayList<AtomicSegment>> atomicSegs,
						HashMap<AtomicSegment, HashSet<LValueBox>> accessedIn,
						HashMap<LValueBox, HashSet<LValueBox>> accessedBefore
						) {
		this.lockAssignment = lockAssignment;
		this.atomicSegments = atomicSegs;
		this.accessedIn = accessedIn;
		int nextNumber = accessedBefore.size();
		for(LValueBox lvb : accessedBefore.keySet()) {
			nextNumber = this.buildTopoSortOrder(lvb, accessedBefore, nextNumber);
		}
		lockComparator = new Comparator<LValueLock>() {
			@Override
			public int compare(LValueLock o1, LValueLock o2) {
				return lockOrder.get(o1.getLVal()) - lockOrder.get(o2.getLVal());
			}
		};
	}

	@Override
	protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
		// If no atomic segments, there is nothing to insert!
		if(!atomicSegments.containsKey(b)) return;
		
		log.debug("Inserting locks into " +
				  b.getMethod().getDeclaringClass().getName() + "." +
				  b.getMethod().getName());
		/// Get the local which has the lock manager //////////////////////////
		Local lockManager = null;
		for(Local loc : b.getLocals()) {
			if(loc.getName().equals(AtomicSegmentMarker.lockManagerLocalName)) {
				if(lockManager != null) {
					throw new RuntimeException("Multiple locals of name " +
											   loc.getName() + " in method " +
											   b.getMethod().getName());
				}
				lockManager = loc;
			}
		}
		if(lockManager == null) {
			throw new RuntimeException("No local of name " +
									   AtomicSegmentMarker.lockManagerLocalName +
									   " in method with atomic segments "+
									   b.getMethod().getName());
		}
		assert(Objects.equal(Scene.v().getSootClass(lockManager.getType().toString()),
							 lockManagerClass));
		///////////////////////////////////////////////////////////////////////
		
		/// Obtain locks at beginning of each atomic seg //////////////////////
		for(AtomicSegment atomicSeg : atomicSegments.get(b)) {
			// Get all the locks we need in order
			HashSet<LValueLock> neededLocks = new HashSet<>();
			for(LValueBox lVal : accessedIn.get(atomicSeg)) {
				neededLocks.add(lockAssignment.get(lVal));
			}
			ArrayList<LValueLock> orderedLocks = new ArrayList<LValueLock>(neededLocks);
			orderedLocks.sort(lockComparator);
			// Invocations can only accept locals: https://mailman.cs.mcgill.ca/pipermail/soot-list/2010-April/002938.html
			// So we need to store each lock in some local
			Local localReentrantLockVar = Jimple.v().newLocal("$localReentrantLockVar",
															  LValueLock.lockClass.getType());
			b.getLocals().add(localReentrantLockVar);
			// Make statements to obtain each lock
			List<Unit> lockObtainStmts = new ArrayList<Unit>();
			for(LValueLock lock : orderedLocks) {
				// Get a reference to the field
				SootFieldRef lockFieldRef = lock.createOrGetLockField().makeRef();
				Value lockVal;
				if(lock.isGlobal()) {
					lockVal = Jimple.v().newStaticFieldRef(lockFieldRef);
				}
				else {
					lockVal = Jimple.v().newInstanceFieldRef(lock.getLVal().getValue(),
															 lockFieldRef);
				}
				// Store the lock field in our localReentrantLockVar iable
				AssignStmt storeInLoc = Jimple.v()
					.newAssignStmt(localReentrantLockVar, lockVal);
				lockObtainStmts.add(storeInLoc);
				// Obtain the lock
				InvokeExpr obtainLock = Jimple.v().newVirtualInvokeExpr(lockManager,
																		obtainLockMethod.makeRef(),
																		localReentrantLockVar
																		);
				lockObtainStmts.add(Jimple.v().newInvokeStmt(obtainLock));
			}
			b.getUnits().insertBefore(lockObtainStmts, atomicSeg.getFirstUnit());
		}
		///////////////////////////////////////////////////////////////////////
	}

}
