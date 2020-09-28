package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

/**
 * Two LValues (a variable or a field) are MUST_ALIAS'ed
 * if, along every execution path in which both LValues are defined,
 * they reference the same heap location.
 * 
 *  If two LValues are not MUST_ALIAS'ed, but there exists
 *  at least one execution path in which both LValues reference
 *  the same heap location, we say they are MAY_ALIAS'ed.
 *  
 *  Otherwise, we say they are NOT_ALIAS'ed.
 *  
 *  A conservative approximation of this relation must
 *  never incorrectly label two LValues as MUST_ALIAS'ed or NOT_ALIAS'ed,
 *  but may incorrectly label two LValues as MAY_ALIAS'ed.
 * 
 * @author Ben_Sepanski
 *
 */
public enum AliasRelation {
	MAY_ALIAS,
	MUST_ALIAS,
	NOT_ALIAS
}
