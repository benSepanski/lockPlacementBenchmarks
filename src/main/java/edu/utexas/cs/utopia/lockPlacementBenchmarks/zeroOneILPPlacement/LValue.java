package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import soot.AbstractValueBox;
import soot.Unit;

/**
 * Holds a value box and an associated unit
 * 
 * @author Ben_Sepanski
 *
 */
class LValue {
	private AbstractValueBox valueBox;
	private Unit statement;
	
	public LValue(AbstractValueBox _valueBox, Unit _statement) {
		// Make sure given unit uses the given value box
		if(!(_statement.getUseAndDefBoxes().contains(_valueBox))) {
			throw new IllegalArgumentException(
				"_statement must have _valueBox as a use or def box");
		}
		valueBox = _valueBox;
		statement = _statement;
	}
	
	public Unit getStatement() {
		return statement;
	}
	
	public AbstractValueBox getValueBox() {
		return valueBox;
	}
}
