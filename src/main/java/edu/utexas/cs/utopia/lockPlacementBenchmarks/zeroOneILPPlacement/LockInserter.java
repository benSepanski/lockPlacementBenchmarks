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

import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.NullType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceFieldRef;
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
	private static final SootClass 
		lockClass = Scene.v().getSootClass("java.util.concurrent.locks.ReentrantLock");
	private static final SootMethodRef
		lockInit = lockClass.getMethod("void <init>()").makeRef();
	
	private HashMap<LValueBox, Integer> lockOrder = new HashMap<>();
	private Comparator<LValueLock> lockComparator;
	private HashMap<LValueBox, LValueLock> lockAssignment;
	private HashMap<Body, ArrayList<AtomicSegment>> atomicSegments;
	private HashMap<AtomicSegment, HashSet<LValueBox>> accessedIn;
	
	/**
	 * Get lock name for a soot class
	 * 
	 * @param cls
	 * @param isGlobal
	 * @return
	 */
	private String getLockName(SootClass cls, boolean isGlobal) {
		String name = "$REENTRANTLOCK_RANJITsALGORITHM" + cls.getName().replace(".", "$");
		if(isGlobal) {
			return "$GLOBAL" + name;
		}
		return "$LOCAL" + name;
	}
	
	private void makeLock(SootClass cls, boolean isGlobal) {
		String fieldName = getLockName(cls, isGlobal);
		RefType fieldType = lockClass.getType();
		// Make the field if it does not already have one
		if(!cls.declaresField(fieldName, fieldType)) {
			// load as application class if not already done
			if(!cls.isApplicationClass()) {
				log.debug("Loading " + cls.getName() + " as application class");
				cls.setApplicationClass();
				Scene.v().loadNecessaryClasses();
			}
			// Add a public lock field, static for a global lock
			int mod = Modifier.PUBLIC;
			if(isGlobal) mod = mod | Modifier.STATIC;  // global locks are static
			SootField lockField = new SootField(fieldName, fieldType, mod);
			cls.addField(lockField);
			String initName = isGlobal ? "<clinit>" : "<init>";
			// In global case, make sure cls has a clinit method
        	// https://ptolemy.berkeley.edu/ptolemyII/ptII10.0/ptII10.0.1/ptolemy/copernicus/kernel/SootUtilities.java
			if(isGlobal) {
	        	if(!cls.declaresMethodByName("<clinit>")) {
	        		@SuppressWarnings({ "rawtypes", "unchecked" })
					SootMethod emptyClinit = new SootMethod("<clinit>",
			        										new LinkedList(),
			        										NullType.v(),
			        										Modifier.PUBLIC);
	        		emptyClinit.setActiveBody(Jimple.v().newBody(emptyClinit));
	        		cls.addMethod(emptyClinit);
	        	}
			}
			// In local case, assert that it has a constructor
			else {
				if(!cls.declaresMethodByName("<init>")) {
					throw new RuntimeException("Attempting to insert local lock " +
											   " attribute into " + cls.getName() +
											   " which has no constructor");
				}
			}
        	// Initialize this new field in all (cl)init methods
        	for(SootMethod meth : cls.getMethods()) {
        		if(meth.getName().equals(initName)) {
        			// Make a local reentrant lock and initialize it
        			Local localReentLock = Jimple.v().newLocal(fieldName + "Local",
        													   fieldType);
        			AssignStmt localReentLockNew = Jimple.v()
        				.newAssignStmt(localReentLock, Jimple.v().newNewExpr(fieldType));
        			SpecialInvokeExpr initExpr = Jimple.v()
        				.newSpecialInvokeExpr(localReentLock, lockInit);
        			InvokeStmt initLocalReentLock = Jimple.v().newInvokeStmt(initExpr);
        			// assign the field to that initialized local
        			AssignStmt assignField;
        			if(isGlobal) {
	        			StaticFieldRef globalLockRef = Jimple.v()
	        				.newStaticFieldRef(lockField.makeRef());
	        			assignField = Jimple.v().newAssignStmt(globalLockRef, localReentLock);
        			}
        			else {
        				InstanceFieldRef localLockRef = Jimple.v()
        					.newInstanceFieldRef(Jimple.v().newThisRef(cls.getType()),
        									     lockField.makeRef());
        				assignField = Jimple.v().newAssignStmt(localLockRef, localReentLock);
        			}
        			// Now add the local and these statements to the method body
        			List<Stmt> toInsert = Arrays.asList(localReentLockNew,
								   				        initLocalReentLock,
								   				        assignField);
        			JimpleBody body = (JimpleBody) meth.getActiveBody();
        			body.getLocals().add(localReentLock);
        			if(body.getUnits().size() > 0) {
        				Unit firstNonID = body.getFirstNonIdentityStmt();
        				body.getUnits().insertBefore(toInsert, firstNonID);
        			}
        			else {
        				for(Stmt s : toInsert) body.getUnits().add(s);
        			}
        		}
        	}
		}
	}
	
	private SootField getLock(SootClass cls, boolean isGlobal) {
		makeLock(cls, isGlobal);
		return cls.getField(getLockName(cls, isGlobal), lockClass.getType());
	}
	
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
		if(atomicSegments.containsKey(b)) return;
		// Otherwise, look at each atomic seg
		for(AtomicSegment atomicSeg : atomicSegments.get(b)) {
			ArrayList<LValueLock> neededLocks = new ArrayList<>();
			for(LValueBox lVal : accessedIn.get(atomicSeg)) {
				neededLocks.add(lockAssignment.get(lVal));
			}
			neededLocks.sort(lockComparator);
			// TODO : make local lock manager name public
			//Local lockManager = b.getLocals().get
		}
	}

}
