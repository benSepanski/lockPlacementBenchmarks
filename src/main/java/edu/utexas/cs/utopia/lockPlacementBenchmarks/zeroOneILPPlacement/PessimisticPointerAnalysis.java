package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.AliasRelation;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.LValueBox;
import edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis.PointerAnalysis;

/**
 * A trivially correct pointer analysis which says any two
 * lValues MAY_ALIAS each other
 * 
 * @author Ben_Sepanski
 *
 */
public class PessimisticPointerAnalysis implements PointerAnalysis {
	@Override
	public AliasRelation getAliasRelation(LValueBox lValue1, LValueBox lValue2) {		
		return AliasRelation.MAY_ALIAS;
	}

}
