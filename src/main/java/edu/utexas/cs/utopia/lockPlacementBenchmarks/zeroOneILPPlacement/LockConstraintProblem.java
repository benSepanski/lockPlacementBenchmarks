package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

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
	
	private HashMap<LValueBox, LValueLock> lockAssignment = new HashMap<>();
	private HashMap<LValueBox, Integer> lValIndex = new HashMap<>();

	public HashMap<LValueBox, LValueLock> getLockAssignment() {
		return lockAssignment;
	}
	
	public LockConstraintProblem(Context ctx,
			  					 HashSet<LValueBox> lValues,
								 HashMap<AtomicSegment, HashSet<LValueBox>> accessedIn,
								 HashMap<AtomicSegment, HashSet<LValueBox>> notInScope,
								 HashMap<LValueBox, HashSet<LValueBox>> accessedBefore,
								 PointerAnalysis ptrAnalysis,
								 int localCost,
								 int globalCost,
								 boolean logZ3) {		
		// give each lValue an index
		for(LValueBox lvb : lValues) {
			lValIndex.put(lvb, lValIndex.size());
			if(log.isDebugEnabled() && logZ3) {
				log.debug((lValIndex.size() - 1) + " <-> " + lvb.toString());
			}
		}

		log.debug("Building lock vars and alternate lock vars");
		// Build variables to hold our lock assignments and an
		// alternative
		BoolExpr localLockVars[][] = new BoolExpr[lValIndex.size()][lValIndex.size()],
		         globalLockVars[][] = new BoolExpr[lValIndex.size()][lValIndex.size()],
				 altLocalLockVars[][] = new BoolExpr[lValIndex.size()][lValIndex.size()],
				 altGlobalLockVars[][] = new BoolExpr[lValIndex.size()][lValIndex.size()];

		for(int i = 0; i < lValIndex.size(); ++i) {
			for(int j = 0; j < lValIndex.size(); ++j) {
				localLockVars[i][j] = ctx.mkBoolConst(getLocalName(i, j, false));
				globalLockVars[i][j] = ctx.mkBoolConst(getGlobalName(i, j, false));
				altLocalLockVars[i][j] = ctx.mkBoolConst(getLocalName(i, j, true));
				altGlobalLockVars[i][j] = ctx.mkBoolConst(getGlobalName(i, j, true));
			}
		}

		// Build constraints and cost
		log.debug("Building constraints in z3");
		BoolExpr constraints = buildConstraints(ctx,
												lValues,
												accessedIn,
												notInScope,
												accessedBefore,
												ptrAnalysis,
												localLockVars,
												globalLockVars,
												logZ3),
				altConstraints = buildConstraints(ctx,
												  lValues,
												  accessedIn,
												  notInScope,
												  accessedBefore,
												  ptrAnalysis,
												  altLocalLockVars,
												  altGlobalLockVars,
												  false);
		ArithExpr cost = buildCost(ctx,
								   accessedIn,
								   localCost,
								   globalCost,
								   localLockVars,
								   globalLockVars),
			altCost = buildCost(ctx,
							    accessedIn,
							    localCost,
							    globalCost,
							    altLocalLockVars,
							    altGlobalLockVars);
		
		// Our solution must minimize the lock cost (conflict + numLocks),
		// i.e. any other setting satisfying the constraints
		// must cost at least as much
		BoolExpr allAlts[] = new BoolExpr[2 * lValIndex.size() * lValIndex.size()];
		int index = 0;
		for(int i = 0; i < lValIndex.size(); ++i) {
			for(int j = 0; j < lValIndex.size(); ++j) {
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
		
		// translate into lock placement
		log.debug("Translating solution into lock assignment");
		Model solution = solver.getModel();
		if(log.isDebugEnabled() && logZ3) {
			log.debug("Model : \n" + solution.toString());
		}
		// TODO : Do i really need these maps to ensure uniqueness of global locks?
		HashMap<LValueBox, LValueLock> localLocks = new HashMap<>(),
				globalLocks = new HashMap<>();
		for(LValueBox lVal : lValues) {
			int i = lValIndex.get(lVal);
			for(LValueBox lockAssign : lValues) {
				int j = lValIndex.get(lockAssign);
				Expr localIJ = solution.getConstInterp(localLockVars[i][j]);
				Expr globalIJ = solution.getConstInterp(globalLockVars[i][j]);
				// assign locks if var indicates to do so
				if(localIJ.getBoolValue().toInt() > 0) {
					if(lockAssignment.containsKey(lVal)) {
						throw new RuntimeException("lVal " + lVal.toString() +
												   " assigned multiple locks");
					}
					if(!localLocks.containsKey(lockAssign)) {
						localLocks.put(lockAssign, new LValueLock(lockAssign, false));
					}
					lockAssignment.put(lVal, localLocks.get(lockAssign));
					//lockAssignment.put(lVal, new LValueLock(lockAssign, false));
				}
				if(globalIJ.getBoolValue().toInt() > 0) {
					if(lockAssignment.containsKey(lVal)) {
						throw new RuntimeException("lVal " + lVal.toString() +
												   " assigned multiple locks");
					}
					if(!globalLocks.containsKey(lockAssign)) {
						globalLocks.put(lockAssign, new LValueLock(lockAssign, true));
					}
					lockAssignment.put(lVal, globalLocks.get(lockAssign));
					//lockAssignment.put(lVal, new LValueLock(lockAssign, true));
				}
			}
		}
	}
	
	private BoolExpr buildConstraints(Context ctx,
									  HashSet<LValueBox> lValues,
									  HashMap<AtomicSegment, HashSet<LValueBox>> accessedIn,
									  HashMap<AtomicSegment, HashSet<LValueBox>> notInScope,
									  HashMap<LValueBox, HashSet<LValueBox>> accessedBefore,
									  PointerAnalysis ptrAnalysis,
									  BoolExpr localLockVars[][],
									  BoolExpr globalLockVars[][],
									  boolean logZ3) {		
		// make a constraint that says each lVal must have a lock
		BoolExpr atLeastOneLockSet = ctx.mkTrue();
		for(int i = 0; i < lValIndex.size(); ++i) {
			BoolExpr atLeastOneLockFori = ctx.mkFalse();
			for(int j = 0; j < lValIndex.size(); ++j) {
				atLeastOneLockFori = ctx.mkOr(atLeastOneLockFori, localLockVars[i][j], globalLockVars[i][j]);
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
		for(LValueBox lvb : lValues) {
			if(lvb.getValue() instanceof ArrayRef) {
				int j = lValIndex.get(lvb);
				for(int i = 0; i < lValIndex.size(); ++i) {
					primitiveAndArrayHandler = ctx.mkAnd(primitiveAndArrayHandler,
														 ctx.mkNot(localLockVars[i][j]),
														 ctx.mkNot(globalLockVars[i][j]));
				}
			}
			else if(lvb.getValue().getType() instanceof PrimType) {
				int j = lValIndex.get(lvb);
				for(int i = 0; i < lValIndex.size(); ++i) {
					primitiveAndArrayHandler = ctx.mkAnd(primitiveAndArrayHandler,
										    			 ctx.mkNot(localLockVars[i][j]));
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
		HashSet<LValueBox> seen = new HashSet<>();
		for(LValueBox lvb1 : lValues) {
			seen.add(lvb1);
			for(LValueBox lvb2 : lValues) {
				if(seen.contains(lvb2)) continue;
				int i1, i2;
				switch(ptrAnalysis.getAliasRelation(lvb1, lvb2)) {
				case MUST_ALIAS:
					// must be assigned same locks
					i1 = lValIndex.get(lvb1);
					i2 = lValIndex.get(lvb2);
					for(int j = 0; j < lValIndex.size(); ++j) {
						BoolExpr sameLoc = ctx.mkIff(localLockVars[i1][j], localLockVars[i2][j]);
						BoolExpr sameGlob = ctx.mkIff(globalLockVars[i1][j], globalLockVars[i2][j]);
						aliasConstraints = ctx.mkAnd(aliasConstraints, sameLoc, sameGlob);
					}
					break;
				case MAY_ALIAS:
					// must be assigned same global lock and no local lock
					i1 = lValIndex.get(lvb1);
					i2 = lValIndex.get(lvb2);
					for(int j = 0; j < lValIndex.size(); ++j) {
						BoolExpr notLoc = ctx.mkNot(localLockVars[i1][j]);
						notLoc = ctx.mkAnd(ctx.mkNot(localLockVars[i2][j]));
						BoolExpr sameGlob = ctx.mkIff(globalLockVars[i1][j], globalLockVars[i2][j]);
						aliasConstraints = ctx.mkAnd(aliasConstraints, notLoc, sameGlob);
					}
					break;
				default: break;
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
		for(AtomicSegment atomicSeg : accessedIn.keySet()) {
			HashSet<LValueBox> outOfScope = notInScope.get(atomicSeg);
			ArrayList<Integer> outOfScopeNdx = new ArrayList<>();
			for(LValueBox lvb : outOfScope) {
				outOfScopeNdx.add(lValIndex.get(lvb));
			}
			// for each lvalue accessed in the atomic segment, it cannot
			// be assigned to a local lock that is not in scope
			for(LValueBox lvb : accessedIn.get(atomicSeg)) {
				int i = lValIndex.get(lvb);
				for(int j : outOfScopeNdx) {
					scopeConstraints = ctx.mkAnd(scopeConstraints, ctx.mkNot(localLockVars[i][j]));
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
		for(LValueBox lvb1 : lValues) {
			int i = lValIndex.get(lvb1);
			// lvb1 accessedBefore lvb2, so lvb1 cannot be assigned lvb2 local lock
			for(LValueBox lvb2 : accessedBefore.get(lvb1)) {
				int j = lValIndex.get(lvb2);
				orderingConstraints = ctx.mkAnd(orderingConstraints, ctx.mkNot(localLockVars[i][j]));
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
	
	private ArithExpr buildCost(Context ctx,
					     		HashMap<AtomicSegment, HashSet<LValueBox>> accessedIn,
							    int localCost,
							    int globalCost,
							    BoolExpr localLockVars[][],
							    BoolExpr globalLockVars[][]) {
		IntExpr localCostExp = ctx.mkInt(localCost);
		IntExpr globalCostExp = ctx.mkInt(globalCost);

		// numLocks
		ArithExpr numLocks = ctx.mkInt(0);
		for(int j = 0; j < lValIndex.size(); ++j) {
			BoolExpr someiAssignedToLocj = ctx.mkFalse(),
				someiAssignedToGlobj = ctx.mkFalse();
			for(int i = 0; i < lValIndex.size(); ++i) {
				someiAssignedToLocj = ctx.mkOr(someiAssignedToLocj, localLockVars[i][j]);
				someiAssignedToGlobj = ctx.mkOr(someiAssignedToGlobj, globalLockVars[i][j]);
			}
			numLocks = ctx.mkAdd(numLocks, 
							     boolToInt(ctx, someiAssignedToLocj),
								 boolToInt(ctx, someiAssignedToGlobj));
		}
		
		// conflict(lock assignment) (cost(i,j) * do they share a lock for all i<=j)
		ArithExpr conflict = ctx.mkInt(0);
		HashSet<AtomicSegment> seen = new HashSet<>();
		// get atomic segment 1
		for(AtomicSegment atomicSeg1 : accessedIn.keySet()) {
			HashSet<LValueBox> accessed1 = accessedIn.get(atomicSeg1);
			// get atomic segment 2
			for(AtomicSegment atomicSeg2 : accessedIn.keySet()) {
				if(seen.contains(atomicSeg2)) continue;
				HashSet<LValueBox> accessed2 = accessedIn.get(atomicSeg2);
				// Do seg1 and seg2 share any locks?
				BoolExpr shareLocLock = ctx.mkFalse(),
						 shareGlobLock = ctx.mkFalse();
				for(int k = 0; k < lValIndex.size(); ++k) {
					// Is an lval accessed in atomic seg1 assigned to lock k?
					BoolExpr kLocLock1 = ctx.mkFalse(), kGlobLock1 = ctx.mkFalse();
					for(LValueBox lvb1 : accessed1) {
						int i1 = lValIndex.get(lvb1);
						kLocLock1 = ctx.mkOr(kLocLock1, localLockVars[i1][k]);
						kGlobLock1 = ctx.mkOr(kGlobLock1, globalLockVars[i1][k]);
					}
					// Is an lVal accessed in atomic seg2 assigned to lock k?
					BoolExpr kLocLock2 = ctx.mkFalse(), kGlobLock2 = ctx.mkFalse();
					for(LValueBox lvb2 : accessed2) {
						int i2 = lValIndex.get(lvb2);
						kLocLock2 = ctx.mkOr(kLocLock2, localLockVars[i2][k]);
						kGlobLock2 = ctx.mkOr(kGlobLock2, globalLockVars[i2][k]);
					}
					// Do atomic segs1 and 2 both use lock k?
					BoolExpr kLocLockBoth = ctx.mkAnd(kLocLock1, kLocLock2),
							 kGlobLockBoth = ctx.mkAnd(kGlobLock1, kGlobLock2);
					
					shareLocLock = ctx.mkOr(shareLocLock, kLocLockBoth);
					shareGlobLock = ctx.mkOr(shareGlobLock, kGlobLockBoth);
				}
				// Add conflict of seg1, seg2 to cost
				conflict = ctx.mkAdd(conflict,
								 ctx.mkMul(localCostExp, boolToInt(ctx, shareLocLock)),
								 ctx.mkMul(globalCostExp, boolToInt(ctx, shareGlobLock)));
			}
			seen.add(atomicSeg1);
		}
		
		ArithExpr cost = ctx.mkAdd(numLocks, conflict);
		return cost;
	}
	
	private IntExpr boolToInt(Context ctx, BoolExpr b) {
		return (IntExpr) ctx.mkITE(b, ctx.mkInt(1), ctx.mkInt(0));
	}
	
	private String getLocalName(int i, int j, boolean alt) {
		String name = "lVal_" + i + "_useLocalLock_" + j;
		if(alt) {
			name = alt(name);
		}
		return name;
	}
	
	private String getGlobalName(int i, int j, boolean alt) {
		String name = "lVal_" + i + "_useGlobalLock_" + j;
		if(alt) {
			name = alt(name);
		}
		return name;
	}
	
	private String alt(String s) {
		return "alt_" + s;
	}
}
