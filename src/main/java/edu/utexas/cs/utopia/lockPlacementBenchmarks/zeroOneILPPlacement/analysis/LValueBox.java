package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis;

import soot.AbstractValueBox;
import soot.Local;
import soot.PrimType;
import soot.Value;
import soot.jimple.AbstractJimpleValueSwitch;
import soot.jimple.ArrayRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;

/**
 * An LValue is one of the following:
 * 	- A non-primitive Local (a JimpleLocal)
 *  - A field (an InstanceFieldRef, or a StaticFieldRef)
 *  - A ThisRef
 *  - A non-primitive ParameterRef
 *  - An array reference (a JArrayRef)
 * 
 * @author Ben_Sepanski
 *
 */
@SuppressWarnings("serial")
public class LValueBox extends AbstractValueBox {	
	/**
	 * An anonymous class which can quickly test if a Value
	 * is an LValue
	 */
	private static AbstractJimpleValueSwitch 
		lValueTest = new AbstractJimpleValueSwitch() {
			boolean result = false;
			@Override public Object getResult() {
				return result;
			}
			
			@Override public void caseLocal(Local v) {
				result = !(v.getType() instanceof PrimType);
			}
			@Override public void caseInstanceFieldRef(InstanceFieldRef v) {
				result = true;
			}
			@Override public void caseParameterRef(ParameterRef v) {
				result = !(v.getType() instanceof PrimType);
			}
			@Override public void caseStaticFieldRef(StaticFieldRef v) {
				result = true;
			}
			@Override public void caseArrayRef(ArrayRef v) {
				result = true;
			}
			@Override public void caseThisRef(ThisRef v) {
				result = true;
			}
			@Override public void defaultCase(Object v) {
				result = false;
			}
		};

	/**
	 * 
	 * @param v value to test
	 * @return True iff Value is an LValue
	 */
	@Override
	public boolean canContainValue(Value v) {
		v.apply(lValueTest);
		return (Boolean) lValueTest.getResult();
	}
	
	/**
	 * Test equality by equivalence of values
	 */
	@Override public boolean equals(Object other) {
		if(this == other) return true;
		if(!(other instanceof LValueBox)) return false;
		LValueBox that = (LValueBox) other;
		return this.getValue().equivTo(that.getValue());
	}
	/**
	 * Hash by equivalence of values
	 */
	@Override public int hashCode() {
		return this.getValue().equivHashCode();
	}
}
