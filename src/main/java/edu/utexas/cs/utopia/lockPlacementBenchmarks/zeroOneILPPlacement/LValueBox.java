package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.HashSet;

import com.google.common.base.Objects;

import soot.AbstractValueBox;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AbstractJimpleValueSwitch;
import soot.jimple.ArrayRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.Jimple;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;

/**
 * An LValue is one of the following:
 * 	- A Local (a JimpleLocal)
 *  - A field (an InstanceFieldRef, a ParameterRef, a ThisRef, or a StaticFieldRef)
 *  - An array reference (a JArrayRef)
 * 
 * @author Ben_Sepanski
 *
 */
class LValueBox extends AbstractValueBox {
	/*** Generated Serializable ID */
	private static final long serialVersionUID = -7383224985832701606L;
	
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
				result = true;
			}
			@Override public void caseInstanceFieldRef(InstanceFieldRef v) {
				result = true;
			}
			@Override public void caseParameterRef(ParameterRef v) {
				result = true;
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
		return LValueBox.isLValue(v);
	}
	
	/**
	 * Create LValueBox pointing to given Value
	 * @param v
	 */
	public LValueBox(Value v) {
		this.setValue(v);
	}
	
	/**
	 * Test equality by testing values
	 */
	@Override public boolean equals(Object other) {
		if(this == other) return true;
		if(!(other instanceof LValueBox)) return false;
		LValueBox that = (LValueBox) other;
		return Objects.equal(this.getValue(), that.getValue());
	}
	/**
	 * Hash by the value
	 */
	@Override public int hashCode() {
		return this.getValue().hashCode();
	}
	
	/**
	 * 
	 * @param v value to test
	 * @return True iff Value is an LValue
	 */
	protected static boolean isLValue(Value v) {
		v.apply(lValueTest);
		return (Boolean) lValueTest.getResult();
	}
	
	/**
	 * Extract all LValue s from the values pointed to by a list
	 * of ValueBox
	 * 
	 * @param boxes the ValueBox'es to extract from
	 * @return All the values pointed to
	 *         by ValueBoxes in boxes.
	 */
	public static HashSet<LValueBox> getAllLValues(Iterable<ValueBox> boxes) {
		HashSet<LValueBox> lVals = new HashSet<>();
		HashSet<Value> addedValues = new HashSet<>();
		for(ValueBox vb : boxes) {
			Value val = vb.getValue();
			if(LValueBox.isLValue(val) && !addedValues.contains(val)) {
				lVals.add(new LValueBox(val));
				addedValues.add(val);
			}
		}
		return lVals;
	}
}
