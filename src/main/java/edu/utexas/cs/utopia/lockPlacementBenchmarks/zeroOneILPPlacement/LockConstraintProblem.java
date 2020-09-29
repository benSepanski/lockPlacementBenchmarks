package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

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
 * @author Ben_Sepanski
 *
 */
public class LockConstraintProblem {

}
