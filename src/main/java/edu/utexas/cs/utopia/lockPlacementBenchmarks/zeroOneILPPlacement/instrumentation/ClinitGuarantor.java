package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.instrumentation;

import java.util.LinkedList;

import soot.Modifier;
import soot.NullType;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.jimple.Jimple;

/**
 * Simple class used to guarantee existence of at least
 * one <clinit> method
 * 
 * @author Ben_Sepanski
 */
public class ClinitGuarantor {
	/**
	 * If cls has no <clinit> method, create one with
	 * an (empty) active body
	 * @param cls
	 */
	public void guaranteeClinitExists(SootClass cls) {
		if(cls.declaresMethodByName("<clinit>")) return;
		
		// create a new clinit method
		SootMethod emptyClinit = new SootMethod("<clinit>",
												new LinkedList<Type>(),
												NullType.v(),
												Modifier.PUBLIC);
		emptyClinit.setActiveBody(Jimple.v().newBody(emptyClinit));
		cls.addMethod(emptyClinit);
	}
}
