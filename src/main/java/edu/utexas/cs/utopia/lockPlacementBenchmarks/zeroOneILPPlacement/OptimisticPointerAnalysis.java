package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.AliasRelation;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.LValueBox;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.PointerAnalysis;

/**
 * An optimistic pointer analysis which says
 * any two LValues MUST_ALIAS if they are the same
 * variable, and all other pairs of LValues are NOT_ALIAS
 * 
 * @author Ben_Sepanski
 *
 */
public class OptimisticPointerAnalysis implements PointerAnalysis {
	@Override
	public AliasRelation getAliasRelation(LValueBox lValue1, LValueBox lValue2) {
		if(lValue1.getValue().equivTo(lValue2.getValue())) {
			return AliasRelation.MUST_ALIAS;
		}
		return AliasRelation.NOT_ALIAS;
	}
}
