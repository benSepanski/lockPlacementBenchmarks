package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import com.google.common.base.Objects;

/**
 * Simple wrapper for a local/global lock associated to
 * a certain lvalue
 * 
 * @author Ben_Sepanski
 *
 */
class LValueLock {
	private boolean isGlobal;
	private LValueBox lVal;
	
	@Override
	public boolean equals(Object other) {
		if(this == other) return true;
		if(!(other instanceof LValueLock)) return false;
		LValueLock that = (LValueLock) other;
		return(Objects.equal(this.lVal, that.lVal)
			    && Objects.equal(this.isGlobal, that.isGlobal));
	}

	public LValueLock(LValueBox lVal, boolean isGlobal) {
		this.lVal = lVal;
		this.isGlobal = isGlobal;
	}

	public boolean isGlobal() {
		return isGlobal;
	}

	public LValueBox getLVal() {
		return lVal;
	}
}
