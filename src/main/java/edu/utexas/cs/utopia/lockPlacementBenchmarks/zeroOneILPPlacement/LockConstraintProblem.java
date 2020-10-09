package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.LValueBox;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.MonitorAnalysis;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.PointerAnalysis;
import soot.PrimType;
import soot.jimple.ArrayRef;

/**
 * Given
 * 	 - AccessedIn relation of lvalues to atomic segments
 *   - scope constraints of lvalues to atomic segments
 *   - AccessedBefore relation of lvalues to lvalues
 *   - Alias analysis
 *   - A cost function for global and local locks 
 * 
 * Minimize lock conflict & number of locks (see Ranjit paper
 * https://dl.acm.org/doi/pdf/10.1145/1190215.1190260
 * )
 *
 * Note that from section 3.1: LValues
 * "The
 * back-end of our analysis augments each record with a system lock
 * resource which is acquired and released with the associated locking
 * primitives." In particular, primitive types have no local locks.
 * We implement this by asserting no LValue is assigned to 
 * a local lock of a primitive LValue  
 * 
 * We add the constraint that no lValue can be assigned
 * a lock associated to an ArrayRef because... it's complicated
 * and I don't totally know how to deal with it :(
 * 
 * @author Ben_Sepanski
 *
 */
public class LockConstraintProblem {
	private static Logger log = LoggerFactory.getLogger(LockConstraintProblem.class);
	
	// i is assigned to lock of lockAssignment.get(i)
	private final List<Integer> lockAssignment = new ArrayList<>();
	// i is assigned to a global lock iff assignedToGlobal.get(i)
	private final List<Boolean> assignedToGlobal = new ArrayList<>();
	
	public LockConstraintProblem(Context ctx,
			  					 MonitorAnalysis mtrAnalysis,
								 int localCost,
								 int globalCost,
								 boolean logZ3) {
		log.debug("Building lock vars and alternate lock vars");
		int n = mtrAnalysis.getLValues().size();
		// Build variables to hold our lock assignments and an
		// alternative
		BoolExpr localLockVars[][] = new BoolExpr[n][n],
		         globalLockVars[][] = new BoolExpr[n][n],
				 altLocalLockVars[][] = new BoolExpr[n][n],
				 altGlobalLockVars[][] = new BoolExpr[n][n];

		for(int i = 0; i < n; ++i) {
			for(int j = 0; j < n; ++j) {
				localLockVars[i][j] = ctx.mkBoolConst(getLocalName(i, j, false));
				globalLockVars[i][j] = ctx.mkBoolConst(getGlobalName(i, j, false));
				altLocalLockVars[i][j] = ctx.mkBoolConst(getLocalName(i, j, true));
				altGlobalLockVars[i][j] = ctx.mkBoolConst(getGlobalName(i, j, true));
			}
		}

		// Build constraints and cost
		log.debug("Building constraints in z3");
		BoolExpr constraints = buildConstraints(ctx,
												mtrAnalysis,
												localLockVars,
												globalLockVars,
												logZ3),
				altConstraints = buildConstraints(ctx,
												  mtrAnalysis,
												  altLocalLockVars,
												  altGlobalLockVars,
												  false);
		ArithExpr cost = buildCost(ctx,
								   mtrAnalysis,
								   localCost,
								   globalCost,
								   localLockVars,
								   globalLockVars),
			altCost = buildCost(ctx,
							    mtrAnalysis,
							    localCost,
							    globalCost,
							    altLocalLockVars,
							    altGlobalLockVars);
		
		// Our solution must minimize the lock cost (conflict + numLocks),
		// i.e. any other setting satisfying the constraints
		// must cost at least as much
		BoolExpr allAlts[] = new BoolExpr[2 * n * n];
		int index = 0;
		for(int i = 0; i < n; ++i) {
			for(int j = 0; j < n; ++j) {
				allAlts[index++] = altLocalLockVars[i][j];
				allAlts[index++] = altGlobalLockVars[i][j];
			}
		}
		Solver solver = ctx.mkSolver();
		solver.add(
			constraints,
			ctx.mkForall(allAlts,
						 ctx.mkImplies(altConstraints,
								 	   ctx.mkLe(cost, altCost)
								 	   ),
						 1, null, null,
						 ctx.mkSymbol("MinimizingQuant"),
						 ctx.mkSymbol("minimizingSkolem")
						 )
		);
		
		// solve constraints
		log.debug("Checking satisfiability");
		if(log.isDebugEnabled() && logZ3) {
			log.debug("Solver: \n" + solver.toString());
		}
		if(solver.check() == Status.UNKNOWN) {
			throw new RuntimeException("0-1 ILP solve failed");
		}
		else if(solver.check() == Status.UNSATISFIABLE) {
			throw new RuntimeException("Infeasible 0-1 ILP problem");
		}
		
		/// translate into lock placement /////////////////////////////////////
		log.debug("Translating solution into lock assignment");
		Model solution = solver.getModel();
		if(log.isDebugEnabled() && logZ3) {
			log.debug("Model : \n" + solution.toString());
		}
		for(int i = 0; i < n; ++i) {
			boolean assignedLock = false;
			for(int j = 0; j < n; ++j) {
				Expr localIJ = solution.getConstInterp(localLockVars[i][j]);
				Expr globalIJ = solution.getConstInterp(globalLockVars[i][j]);
				if(localIJ.getBoolValue().toInt() > 0) {
					if(assignedLock == true) {
						throw new RuntimeException("LValue " + i + " assigned to multiple locks");
					}
					assignedLock = true;
					this.lockAssignment.add(j);
					this.assignedToGlobal.add(false);
				}
				else if(globalIJ.getBoolValue().toInt() > 0) {
					if(assignedLock == true) {
						throw new RuntimeException("LValue " + i + " assigned to multiple locks");
					}
					assignedLock = true;
					this.lockAssignment.add(j);
					this.assignedToGlobal.add(true);
				}
			}
			if(!assignedLock) {
				throw new RuntimeException("LValue " + i + " not assigned to any lock");
			}
		}
		///////////////////////////////////////////////////////////////////////
	}
	
	/**
	 * 
	 * @param ctx
	 * @param mtrAnalysis
	 * @param local
	 * @param global
	 * @param logZ3
	 * @return
	 */
	private BoolExpr buildConstraints(Context ctx,
									  MonitorAnalysis mtrAnalysis,
									  BoolExpr local[][],
									  BoolExpr global[][],
									  boolean logZ3) {		
		int n = mtrAnalysis.getLValues().size();
		// make a constraint that says each lVal must have a lock
		BoolExpr atLeastOneLockSet = ctx.mkTrue();
		for(int i = 0; i < n; ++i) {
			BoolExpr atLeastOneLockFori = ctx.mkFalse();
			for(int j = 0; j < n; ++j) {
				atLeastOneLockFori = ctx.mkOr(atLeastOneLockFori,
											  local[i][j],
											  global[i][j]);
			}
			atLeastOneLockSet = ctx.mkAnd(atLeastOneLockSet, atLeastOneLockFori);
		}
		BoolExpr constraints = atLeastOneLockSet;
		if(log.isDebugEnabled() && logZ3) {
			Solver debugSolv = ctx.mkSolver();
			debugSolv.add(atLeastOneLockSet);
			log.debug("At least one lock set: \n" + debugSolv.toString().replace("\n", "    \n"));
		}
		
		// Primitive LValues do not have local locks, so code that into
		// the constraints. 
		// At the same time, make constraints that say no lval may be assigned 
		// to an array reference as its lock
		BoolExpr primitiveAndArrayHandler = ctx.mkTrue();
		for(int j = 0; j < n; ++j) {
			LValueBox lvb = mtrAnalysis.getLValues().get(j);
			if(lvb.getValue() instanceof ArrayRef) {
				for(int i = 0; i < n; ++i) {
					primitiveAndArrayHandler = ctx.mkAnd(primitiveAndArrayHandler,
														 ctx.mkNot(local[i][j]),
														 ctx.mkNot(global[i][j]));
				}
			}
			else if(lvb.getValue().getType() instanceof PrimType) {
				for(int i = 0; i < n; ++i) {
					primitiveAndArrayHandler = ctx.mkAnd(primitiveAndArrayHandler,
										    			 ctx.mkNot(local[i][j]));
				}
			}
		}
		constraints = ctx.mkAnd(constraints, primitiveAndArrayHandler);
		if(log.isDebugEnabled() && logZ3) {
			Solver debugSolv = ctx.mkSolver();
			debugSolv.add(primitiveAndArrayHandler);
			log.debug("Primitives and array handling: \n" + debugSolv.toString().replace("\n", "    \n"));
		}
		
		// Add constraints that say if two lValues are may-aliased
		// they cannot be assigned local locks and must have the same
		// global lock,
		// and if two lValues are
		// MUST-aliased, they must have identical locks
		BoolExpr aliasConstraints = ctx.mkTrue();
		PointerAnalysis ptrAnalysis = mtrAnalysis.getPtrAnalysis();
		for(int i1 = 0; i1 < n; ++i1) {
			LValueBox lvb1 = mtrAnalysis.getLValues().get(i1);
			for(int i2 = i1+1; i2 < n; ++i2) {
				LValueBox lvb2 = mtrAnalysis.getLValues().get(i2);
				switch(ptrAnalysis.getAliasRelation(lvb1, lvb2)) {
				case MAY_ALIAS:
					for(int j = 0; j < n; ++j) {
						BoolExpr notLoc = ctx.mkNot(local[i1][j]);
						notLoc = ctx.mkAnd(ctx.mkNot(local[i2][j]));
						BoolExpr sameGlob = ctx.mkIff(global[i1][j], global[i2][j]);
						aliasConstraints = ctx.mkAnd(aliasConstraints, notLoc, sameGlob);
					}
					break;
				case MUST_ALIAS:
					for(int j = 0; j < n; ++j) {
						BoolExpr sameLoc = ctx.mkIff(local[i1][j], local[i2][j]);
						BoolExpr sameGlob = ctx.mkIff(global[i1][j], global[i2][j]);
						aliasConstraints = ctx.mkAnd(aliasConstraints, sameLoc, sameGlob);
					}
					break;
				default:
				}
			}
		}
		constraints = ctx.mkAnd(constraints, aliasConstraints);
		if(log.isDebugEnabled() && logZ3) {
			Solver debugSolv = ctx.mkSolver();
			debugSolv.add(aliasConstraints);
			log.debug("Alias constraints: \n" + debugSolv.toString().replace("\n", "    \n"));
		}
		
		// Make sure local locks are in scope:
		BoolExpr scopeConstraints = ctx.mkTrue();
		List<List<Integer>> accessedIn = mtrAnalysis.getAccessedLValues();
		List<List<Integer>> outOfScope = mtrAnalysis.getOutOfScope();
		int numAtomic = mtrAnalysis.getAtomicSegments().size();
		for(int atomicSegIndex = 0; atomicSegIndex < numAtomic; ++atomicSegIndex) {
			for(int i : accessedIn.get(atomicSegIndex)) {
				for(int j : outOfScope.get(atomicSegIndex)) {
					scopeConstraints = ctx.mkAnd(scopeConstraints,
												 ctx.mkNot(local[i][j]));
				}
			}
		}
		constraints = ctx.mkAnd(constraints, scopeConstraints);
		if(log.isDebugEnabled() && logZ3) {
			Solver debugSolv = ctx.mkSolver();
			debugSolv.add(scopeConstraints);
			log.debug("Scope constraints: \n" + debugSolv.toString().replace("\n", "    \n"));
		}
		
		// Add ordering constraints
		BoolExpr orderingConstraints = ctx.mkTrue();
		for(int i = 0; i < n; ++i) {
			for(int j : mtrAnalysis.getTopoAccBefore().get(i)) {
				orderingConstraints = ctx.mkAnd(orderingConstraints,
											    ctx.mkNot(local[i][j]));
			}
		}
		constraints = ctx.mkAnd(constraints, orderingConstraints);
		if(log.isDebugEnabled() && logZ3) {
			Solver debugSolv = ctx.mkSolver();
			debugSolv.add(orderingConstraints);
			log.debug("Ordering constraints: \n" + debugSolv.toString().replace("\n", "    \n"));
		}
		
		return constraints;
	}
	
	/**
	 * 
	 * @param ctx
	 * @param mtrAnalysis
	 * @param localCost
	 * @param globalCost
	 * @param local
	 * @param global
	 * @return
	 */
	// TODO : coument localcost/globalcost
	private ArithExpr buildCost(Context ctx,
							    MonitorAnalysis mtrAnalysis,
							    int localCost,
							    int globalCost,
							    BoolExpr local[][],
							    BoolExpr global[][]) {
		int n = mtrAnalysis.getLValues().size();
		IntExpr localCostExp = ctx.mkInt(localCost);
		IntExpr globalCostExp = ctx.mkInt(globalCost);

		// numLocks
		ArithExpr numLocks = ctx.mkInt(0);
		for(int j = 0; j < n; ++j) {
			BoolExpr someiAssignedToLocj = ctx.mkFalse(),
				someiAssignedToGlobj = ctx.mkFalse();
			for(int i = 0; i < n; ++i) {
				someiAssignedToLocj = ctx.mkOr(someiAssignedToLocj, local[i][j]);
				someiAssignedToGlobj = ctx.mkOr(someiAssignedToGlobj, global[i][j]);
			}
			numLocks = ctx.mkAdd(numLocks, 
							     ctx.mkMul(localCostExp, boolToInt(ctx, someiAssignedToLocj)),
								 ctx.mkMul(globalCostExp, boolToInt(ctx, someiAssignedToGlobj)));
		}
		
		// conflict(lock assignment) (cost(i,j) * do they share a lock for all i<=j)
		ArithExpr conflict = ctx.mkInt(0);
		int numAtomic = mtrAnalysis.getAtomicSegments().size();
		for(int a1 = 0; a1 < numAtomic; ++a1) {
			List<Integer> accessedIn1 = mtrAnalysis.getAccessedLValues().get(a1);
			for(int a2 = a1+1; a2 < numAtomic; ++a2) {
				List<Integer> accessedIn2 = mtrAnalysis.getAccessedLValues().get(a2);
				
				// Do seg1 and seg2 share any locks?
				BoolExpr shareLocLock = ctx.mkFalse(),
						 shareGlobLock = ctx.mkFalse();
				for(int k = 0; k < n; ++k) {
					// Is an lval accessed in atomic seg1 assigned to lock k?
					BoolExpr kLocLock1 = ctx.mkFalse(), kGlobLock1 = ctx.mkFalse();
					for(Integer i1 : accessedIn1) {
						kLocLock1 = ctx.mkOr(kLocLock1, local[i1][k]);
						kGlobLock1 = ctx.mkOr(kGlobLock1, global[i1][k]);
					}
					// Is an lVal accessed in atomic seg2 assigned to lock k?
					BoolExpr kLocLock2 = ctx.mkFalse(), kGlobLock2 = ctx.mkFalse();
					for(Integer i2 : accessedIn2) {
						kLocLock2 = ctx.mkOr(kLocLock2, local[i2][k]);
						kGlobLock2 = ctx.mkOr(kGlobLock2, global[i2][k]);
					}
					// Do atomic segs1 and 2 both use lock k?
					BoolExpr kLocLockBoth = ctx.mkAnd(kLocLock1, kLocLock2),
							 kGlobLockBoth = ctx.mkAnd(kGlobLock1, kGlobLock2);
					
					shareLocLock = ctx.mkOr(shareLocLock, kLocLockBoth);
					shareGlobLock = ctx.mkOr(shareGlobLock, kGlobLockBoth);
				}
				// Add conflict of seg1, seg2 to cost
				conflict = ctx.mkAdd(conflict,
									 boolToInt(ctx, shareLocLock),
									 boolToInt(ctx, shareGlobLock));
			}
		}
		
		ArithExpr cost = ctx.mkAdd(numLocks, conflict);
		return cost;
	}
	
	private IntExpr boolToInt(Context ctx, BoolExpr b) {
		return (IntExpr) ctx.mkITE(b, ctx.mkInt(1), ctx.mkInt(0));
	}
	
	private String getLocalName(int i, int j, boolean alt) {
		String name = "local__" + i + "_" + j;
		if(alt) {
			name = alt(name);
		}
		return name;
	}
	
	private String getGlobalName(int i, int j, boolean alt) {
		String name = "global_" + i + "_" + j;
		if(alt) {
			name = alt(name);
		}
		return name;
	}
	
	private String alt(String s) {
		return s + "_alt";
	}

	/**
	 * @return the lockAssignment: i assigned to lockAssignment.get(i)
	 */
	public List<Integer> getLockAssignment() {
		return lockAssignment;
	}

	/**
	 * @return i given a global lock iff assignedToGlobal.get(i)
	 */
	public List<Boolean> getAssignedToGlobal() {
		return assignedToGlobal;
	}
	
	
}
