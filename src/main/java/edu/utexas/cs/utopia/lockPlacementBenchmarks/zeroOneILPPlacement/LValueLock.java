package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.base.Objects;

import edu.utexas.cs.utopia.lockPlacementBenchmarks.Driver;
import soot.Body;
import soot.Local;
import soot.NullType;
import soot.PrimType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;
import soot.jimple.SpecialInvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;

/**
 * A local/global lock associated to a certain lValue
 * 
 * @author Ben_Sepanski
 *
 */
class LValueLock {
	private static Logger log = LoggerFactory.getLogger(LValueLock.class);
	// We will be using reentrant locks
	public static final SootClass 
		lockClass = Scene.v().getSootClass("java.util.concurrent.locks.ReentrantLock");
	private static final SootMethodRef
		lockInit = lockClass.getMethod("void <init>()").makeRef();
	// Used to make sure we don't make multiple global locks for same lvalue
	private static final HashMap<LValueBox, SootClass>
		lValToGlobalLock = new HashMap<>();
	
	// These describe the lock this object represents
	private boolean isGlobal;
	private boolean isPrimitive;
	private LValueBox lVal;
	private SootClass lValClass;
	private String lockFieldName;
	
	/**
	 * Test equality by testing global/local and testing lvalue box
	 */
	@Override
	public boolean equals(Object other) {
		if(this == other) return true;
		if(!(other instanceof LValueLock)) return false;
		LValueLock that = (LValueLock) other;
		return(Objects.equal(this.lVal, that.lVal)
			    && Objects.equal(this.isGlobal, that.isGlobal));
	}
	/**
	 * hash by global/local and the lvalue box
	 */
	@Override
	public int hashCode() {
		return Objects.hashCode(this.isGlobal, this.lVal);
	}

	/**
	 * Create a new LValueLock.
	 * 
	 * @param lVal an lValue that does not correspond to an array ref
	 * @param isGlobal
	 * @param b a body in which this lValue is in scope, used for
	 *        primitive locals
	 */
	public LValueLock(LValueBox lVal, boolean isGlobal) {
		if(lVal.getValue() instanceof ArrayRef) {
			throw new IllegalArgumentException("We don't allow ArrayRefs to be associated to locks");
		}
		this.lVal = lVal;
		this.isPrimitive = (lVal.getValue().getType() instanceof PrimType);
		if(this.isPrimitive && !isGlobal) {
			throw new IllegalArgumentException("Primitive types do not have local locks");
		}
		this.isGlobal = isGlobal;
		this.lockFieldName = this.getLockFieldName();
		
		// If this is global, make a new global lock class later if necessary
		if(this.isGlobal) {
			this.lValClass = null;
		} // Otherwise, insert a lock attribute into the class
		else {
			this.lValClass = Scene.v().getSootClass(lVal.getValue().getType().toString());
		}
	}

	/**
	 * 
	 * @return true iff a global lock
	 */
	public boolean isGlobal() {
		return isGlobal;
	}

	/**
	 * 
	 * @return the LValueBox associated to this lock
	 */
	public LValueBox getLVal() {
		return lVal;
	}
	
	private SootClass makeOrGetNewGlobalLockClass() {
		if(lValToGlobalLock.containsKey(this.lVal)) return lValToGlobalLock.get(this.lVal); 
		// Get i so that we have a unique class name
		String module = "edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.",
			prefix = module + "$GLOBAL$LOCK$CLASS$";
		int i = 0;
		while(Scene.v().getSootClassUnsafe(prefix + i, false) != null) {
			i++;
		}
		// https://github.com/soot-oss/soot/wiki/Creating-a-class-from-scratch#creation-of-a-new-sootclass-object
		SootClass globalLockClass = Scene.v().makeSootClass(prefix + i,
															Modifier.PUBLIC);
		globalLockClass.setSuperclass(Scene.v().getSootClass("java.lang.Object"));
		Scene.v().addClass(globalLockClass);

		// Give the class a static lock 
		RefType lockType = lockClass.getType();
		SootField lockField = new SootField(lockFieldName, lockType,
											Modifier.PUBLIC | Modifier.STATIC);
		globalLockClass.addField(lockField);
		
		// Give the class a clinit method
    	// ://ptolemy.berkeley.edu/ptolemyII/ptII10.0/ptII10.0.1/ptolemy/copernicus/kernel/SootUtilities.java
		@SuppressWarnings({ "rawtypes", "unchecked" })
		SootMethod emptyClinit = new SootMethod("<clinit>",
        										new LinkedList(),
        										NullType.v(),
        										Modifier.PUBLIC);
		emptyClinit.setActiveBody(Jimple.v().newBody(emptyClinit));
		globalLockClass.addMethod(emptyClinit);
		
		/// Build the clinit body: ////////////////////////////////////////////
		// Make a local reentrant lock and initialize it
		Local localReentLock = Jimple.v().newLocal(lockFieldName + "Local",
												   lockType);
		AssignStmt localReentLockNew = Jimple.v()
			.newAssignStmt(localReentLock, Jimple.v().newNewExpr(lockType));
		SpecialInvokeExpr initExpr = Jimple.v()
			.newSpecialInvokeExpr(localReentLock, lockInit);
		InvokeStmt initLocalReentLock = Jimple.v().newInvokeStmt(initExpr);
		// assign the field to that initialized local
		StaticFieldRef globalLockRef = Jimple.v()
			.newStaticFieldRef(lockField.makeRef());
		AssignStmt assignField = Jimple.v().newAssignStmt(globalLockRef, localReentLock);
		// Now add the local and these statements to the method body
		Body b = emptyClinit.getActiveBody();
		b.getLocals().add(localReentLock);
		b.getUnits().addAll(Arrays.asList(localReentLockNew,
								          initLocalReentLock,
								          assignField));
		///////////////////////////////////////////////////////////////////////
		Driver.addClassToWrite(globalLockClass);
		lValToGlobalLock.put(this.lVal, globalLockClass); 
		return globalLockClass;
	}
	
	/**
	 * 
	 * @return the field name of this lock
	 */
	private String getLockFieldName() {
		return "$RANJIT$ALG$REENTRANTLOCK";
	}
	
	/**
	 * If this lValue does not have a field representing this
	 * lock (i.e. a field of lValClass with name lockFieldName)
	 * make such a field (it must be public, and we make global
	 * locks static)
	 * 
	 * Otherwise return the field
	 * 
	 * @return the field of this lVal's class which is
	 *         the lock corresponding to this object.
	 */
	public SootField createOrGetLockField() {
		RefType fieldType = lockClass.getType();
		// Make the global class if we haven't already made it
		if(this.lValClass == null) {
			assert(this.isGlobal);
			this.lValClass = makeOrGetNewGlobalLockClass();
		}
		// Make the field if it does not already have one
		if(!lValClass.declaresField(lockFieldName, fieldType)) {
			assert(!this.isGlobal);
			// load as application class if not already done
			if(!lValClass.isApplicationClass()) {
				log.debug("Loading " + lValClass.getName() + " as application class");
				Scene.v().loadClass(lValClass.getName(), SootClass.BODIES);
				lValClass.setApplicationClass();
				Driver.addClassToWrite(lValClass);
			}
			/// Add a public lock field ///////////////////////////////////////
			SootField lockField = new SootField(lockFieldName, fieldType,
											    Modifier.PUBLIC);
			lValClass.addField(lockField);
			// assert that it has a constructor 
			if(!lValClass.declaresMethodByName("<init>")) {
				throw new RuntimeException("Attempting to insert local lock " +
										   " attribute into " + lValClass.getName() +
										   " which has no constructor");
			}
			///////////////////////////////////////////////////////////////////
        	/// Initialize this new field in all init methods /////////////////
        	for(SootMethod meth : lValClass.getMethods()) {
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
		return lValClass.getField(lockFieldName, fieldType);
	}
}
