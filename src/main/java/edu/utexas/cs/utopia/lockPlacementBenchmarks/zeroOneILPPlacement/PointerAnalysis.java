package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

public interface PointerAnalysis {
	public AliasRelation getAliasRelation(LValueBox lValue1, LValueBox lValue2);
}
