package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.instrumentation;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.base.Objects;

import edu.utexas.cs.utopia.lockPlacementBenchmarks.Driver;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.AtomicSegment;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.LValueBox;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.MonitorAnalysis;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
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
	
	// We will be using reentrant locks
	private static final SootClass 
		lockClass = Scene.v().getSootClass("java.util.concurrent.locks.ReentrantLock");
	private static final SootMethodRef
		lockInit = lockClass.getMethod("void <init>()").makeRef();
	// prefix of lock fields which we'll be adding to classes
	private static final String lockFieldPrefix = "$reent$lock";
	
	// the lock assignment (and local vs global)
	private final List<Integer> lockAssignment;
	private final List<Boolean> assignedToGlobal;
	// map ID -> LValue
	private final List<LValueBox> lValues;
	// the atomic segments we are given
	private final List<AtomicSegment> atomicSegments;
	// the lvalues accessed in the atomic segments
	private final List<List<Integer>> accessedIn;
	// topoAccBefore (see MonitorAnalysis)
	private final List<List<Integer>> topoAccBefore;
	
	// We will order locks to avoid deadlock
	private final HashMap<Integer, Integer> lockOrder = new HashMap<>();
	// comparator which imposes lockOrder
	private final Comparator<Integer> lockComparator;
	
	/**
	 * Store the lock assignment and atomic segments and
	 * order the locks
	 * 
	 * @param lockAssignment Indicate which local or global lock to use for each lValue
	 * @param atomicSegs Give the atomic segments
	 * @param accessedBefore z -> {w | z accessedBefore w}, used to order locks
	 */
	public LockInserter(List<Integer> lockAssignment,
						List<Boolean> assignedToGlobal,
						MonitorAnalysis mtrAnalysis
						) {
		this.lockAssignment = lockAssignment;
		this.assignedToGlobal = assignedToGlobal;
		this.lValues = mtrAnalysis.getLValues();
		this.atomicSegments = mtrAnalysis.getAtomicSegments();
		this.accessedIn = mtrAnalysis.getAccessedLValues();
		this.topoAccBefore = mtrAnalysis.getTopoAccBefore();
		
		int nextNumber = this.topoAccBefore.size();
		for(int i = 0; i < this.topoAccBefore.size(); ++i) {
			nextNumber = this.buildTopoSortOrder(i, nextNumber);
		}
		lockComparator = new Comparator<Integer>() {
			@Override
			public int compare(Integer o1, Integer o2) {
				return lockOrder.get(o1) - lockOrder.get(o2);
			}
		};
	}

	
	/**
	 * Use a DFS to build a lock ordering such that
	 * if v Topo-accessedBefore w and w not Topo-accessedBefore v,
	 * v < w
	 * 
	 * See AccessedBeforeRelation for a definition
	 * of topo-accessed before
	 * 
	 * @param curNode
	 * @param topoAccBefore
	 * @param nextNumber the number to be assigned, decreasing from n,n-1,...,1
	 */
	private int buildTopoSortOrder(int curNode,
								   int nextNumber) {
		if(this.lockOrder.containsKey(curNode)) return nextNumber;
		// Mark this node as being visited and visit its neighbors
		this.lockOrder.put(curNode, -1);
		for(int nbr : this.topoAccBefore.get(curNode)) {
			if(this.lockOrder.containsKey(nbr)) continue;
			nextNumber = buildTopoSortOrder(nbr, nextNumber);
		}
		// Now that everything after this node has been given a number,
		// give this node the next number
		this.lockOrder.put(curNode, nextNumber--);
		return nextNumber;
	}

	@Override
	protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
		// Get all the atomic segments in this body
		List<AtomicSegment> atSegsInBody = new ArrayList<>();
		List<List<Integer>> accessedInAtSeg = new ArrayList<>();
		for(int i = 0; i < this.atomicSegments.size(); ++i) {
			if(b.equals(this.atomicSegments.get(i).getBody())) {
				atSegsInBody.add(this.atomicSegments.get(i));
				accessedInAtSeg.add(this.accessedIn.get(i));
			}
		}
		// If no atomic segments, there is nothing to insert!
		if(atSegsInBody.size() <= 0) return;
		
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
		for(int i = 0; i < atSegsInBody.size(); ++i) {
			// Get all the locks we need in order
			Set<Integer> neededLocks = new HashSet<>();
			// Store which ones we need local locks and which ones we need
			// global locks
			Set<Integer> localLocks = new HashSet<>(),
						 globalLocks = new HashSet<>();
			for(int lValID : accessedInAtSeg.get(i)) {
				int lockID = this.lockAssignment.get(lValID);
				neededLocks.add(lockID);
				if(this.assignedToGlobal.get(lValID)) {
					globalLocks.add(lockID);
				}
				else {
					localLocks.add(lockID);
				}
			}
			List<Integer> orderedLocks = new ArrayList<Integer>(neededLocks);
			orderedLocks.sort(lockComparator);
			// Invocations can only accept locals: https://mailman.cs.mcgill.ca/pipermail/soot-list/2010-April/002938.html
			// So we need to store each lock in some local
			Local localReentrantLockVar = Jimple.v().newLocal("$localReentrantLockVar",
															  lockClass.getType());
			b.getLocals().add(localReentrantLockVar);
			// Make statements to obtain each lock
			Unit first = atSegsInBody.get(i).getFirstUnit();
			for(int lockID : orderedLocks) {
				if(globalLocks.contains(lockID)) {
					insertObtainLock(b, first, lockManager, localReentrantLockVar, lockID, true);
				}
				if(localLocks.contains(lockID)) {
					insertObtainLock(b, first, lockManager, localReentrantLockVar, lockID, false);
				}
			}
		}
		///////////////////////////////////////////////////////////////////////
	}
	
	/**
	 * Insert statements to store the global/local lock of lockID
	 * in localLockVar, then have localLockManager obtain that
	 * lock.
	 * 
	 * @param b the body
	 * @param unitBefore the unit to insert lock obtains before
	 * @param localLockManager the local holding a 2-phase lock manager
	 * @param localLockVar the local which will hold the lock
	 * @param lockID the LValue ID of the LValue associated to the lock
	 * @param global true iff the lock is global
	 */
	private void insertObtainLock(Body b,
								  Unit unitBefore,
								  Local localLockManager,
								  Local localLockVar,
								  int lockID,
								  boolean global) {
		// Get a reference to the field
		SootClass cls = b.getMethod().getDeclaringClass();
		SootFieldRef lockFieldRef = this.createOrGetLockField(cls, lockID, global).makeRef();
		Value lockVal;
		if(global) {
			lockVal = Jimple.v().newStaticFieldRef(lockFieldRef);
		}
		else {
			lockVal = Jimple.v().newInstanceFieldRef(this.lValues.get(lockID).getValue(),
													 lockFieldRef);
		}
		// Store the lock field in our local lock variable
		AssignStmt storeInLoc = Jimple.v().newAssignStmt(localLockVar, lockVal);
		// Obtain the lock
		InvokeExpr obtainLock = Jimple.v().newVirtualInvokeExpr(localLockManager,
																obtainLockMethod.makeRef(),
																localLockVar
																);
		InvokeStmt obtainLockStmt = Jimple.v().newInvokeStmt(obtainLock);
		// add those statements to b
		List<Stmt> toInsert = Arrays.asList(storeInLoc, obtainLockStmt);
		b.getUnits().insertBefore(toInsert, unitBefore);
	}
	
	/**
	 * If global, createOrGetLockField on globalClass with suffix
	 * "$<lockID>". Otherwise is local, so createOrGetLockField
	 * on the class of the LValue with id lockID (with no suffix)
	 * 
	 * @param globalClass
	 * @param lockID
	 * @param global
	 * @return the field
	 */
	private SootField createOrGetLockField(SootClass globalClass, int lockID, boolean global) {
		if(global) {
			return createOrGetLockField(globalClass, "$" + lockID);
		}
		LValueBox lvb = lValues.get(lockID);
		String typeName = lvb.getValue().getType().toString();
		SootClass lValClass = Scene.v().getSootClass(typeName);
		return createOrGetLockField(lValClass, "");
	}
	
	/**
	 * If cls does not have a field representing hte
	 * lock (i.e. a field of cls with name lockFieldPrefix + suffix)
	 * make such a field (it must be public, and we make global
	 * locks static)
	 * 
	 * Otherwise return the field
	 * 
	 * @param cls the soot class to look at
	 * @param fieldSuffix a string to append to lockFieldName
	 *                   (this enables a class to have multiple
	 *                    lock fields)
	 * @return the field of this lVal's class which is
	 *         the lock corresponding to this object.
	 */
	private SootField createOrGetLockField(SootClass cls, String fieldSuffix) {
		RefType fieldType = lockClass.getType();
		String lockFieldName = lockFieldPrefix + fieldSuffix;
		// Make the field if it does not already have one
		if(!cls.declaresField(lockFieldName, fieldType)) {
			// load as application class if not already done
			if(!cls.isApplicationClass()) {
				log.debug("Loading " + cls.getName() + " as application class");
				Scene.v().loadClass(cls.getName(), SootClass.BODIES);
				cls.setApplicationClass();
				Driver.addClassToWrite(cls);
			}
			/// Add a public lock field ///////////////////////////////////////
			SootField lockField = new SootField(lockFieldName, fieldType,
											    Modifier.PUBLIC);
			cls.addField(lockField);
			// assert that it has a constructor 
			if(!cls.declaresMethodByName("<init>")) {
				throw new RuntimeException("Attempting to insert local lock " +
										   " attribute into " + cls.getName() +
										   " which has no constructor");
			}
			///////////////////////////////////////////////////////////////////
        	/// Initialize this new field in all init methods /////////////////
        	for(SootMethod meth : cls.getMethods()) {
        		if(!meth.isConstructor()) continue;
    			// Make a local reentrant lock and initialize it
    			Local localReentLock = Jimple.v().newLocal(lockFieldName + "Local",
    													   fieldType);
    			AssignStmt localReentLockNew = Jimple.v()
    				.newAssignStmt(localReentLock, Jimple.v().newNewExpr(fieldType));
    			SpecialInvokeExpr initExpr = Jimple.v()
    				.newSpecialInvokeExpr(localReentLock, lockInit);
    			InvokeStmt initLocalReentLock = Jimple.v().newInvokeStmt(initExpr);
    			// assign the field to that initialized local
    			JimpleBody body = (JimpleBody) meth.getActiveBody();
				InstanceFieldRef localLockRef = Jimple.v()
					.newInstanceFieldRef(body.getThisLocal(), lockField.makeRef());
				AssignStmt assignField = Jimple.v().newAssignStmt(localLockRef, localReentLock);
    			// Now add the local and these statements to the method body
    			List<Stmt> toInsert = Arrays.asList(localReentLockNew,
							   				        initLocalReentLock,
							   				        assignField);
    			body.getLocals().add(localReentLock);
    			if(body.getUnits().size() > 0) {
    				Unit firstNonID = body.getFirstNonIdentityStmt();
    				body.getUnits().insertBefore(toInsert, firstNonID);
    			}
    			else {
    				body.getUnits().addAll(toInsert);
    			}
        	}
        	///////////////////////////////////////////////////////////////////
		}
		return cls.getField(lockFieldName, fieldType);
	}

}
