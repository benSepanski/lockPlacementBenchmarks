package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis;

import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootClass;

/**
 * A monitor is a program with several methods which may
 * contain atomic segments.
 * 
 * The monitor represents "the entire program", i.e.
 * global locks are treated as attributes of "this" in the
 * monitor
 * 
 * This class extracts all the information needed to build
 * the lock constraint problem from Ranjit's paper
 * https://dl.acm.org/doi/pdf/10.1145/1190215.1190260
 * 
 * @author Ben_Sepanski
 *
 */
public class MonitorAnalysis {
	private static Logger log = LoggerFactory.getLogger(MonitorAnalysis.class);

	private final PointerAnalysis ptrAnalysis;
	private final List<AtomicSegment> atomicSegments;
	private final List<List<Integer>> accessedLValues;
	private final List<LValueBox> lValues;
	private final List<List<Integer>> outOfScope;
	/*
	 *  Define TC(accessed-Before) to be the transitive closure
	 *  of the accessed before relation.
	 *  
	 *  This maps (id of v) 
	 *        -> {} if v is in a non-trivial SCC in the accessed-before graph
	 *  	  -> { (id of w) | v TC(accessed-Before) w} 
	 *  
	 *  i.e. maps (id of v) -> {(id of w) | v cannot be assigned local lock
	 *  									w due to accessed-before constraints
	 *  									in Ranjit's algorithm}
	 */
	private final List<List<Integer>> topoAccBefore;
	
	public MonitorAnalysis(SootClass monitorClass, PointerAnalysis ptrAnalysis) {
		log.info("Beginning analysis of " + monitorClass.getName());
		this.ptrAnalysis = ptrAnalysis;
		
		log.debug("Extracting atomic segments");
		AtomicSegmentExtractor 
			atomicExtractor = new AtomicSegmentExtractor(monitorClass);
		this.atomicSegments = atomicExtractor.getAtomicSegments();
		
		log.debug("Extracting LValues from atomic segments");
		LValueExtractor 
			lValExtractor = new LValueExtractor(this.atomicSegments);
		this.accessedLValues = lValExtractor.getLValuesInAtomicSegment();
		this.lValues = lValExtractor.getLValues();
		
		if(log.isDebugEnabled()) {
			log.debug("LValueIDs:");
			for(int i = 0; i < this.lValues.size(); ++i) {
				log.debug(i + " <-> " + this.lValues.get(i));
			}
		}
		
		log.debug("Determining LValues which are out of scope");
		OutOfScopeCalculator oosc = new OutOfScopeCalculator(this.atomicSegments,
														 	this.lValues);
		this.outOfScope = oosc.getOutOfScope();
		
		log.debug("Creating accessed-before relation");
		AccessedBeforeRelation 
			accBefore = new AccessedBeforeRelation(ptrAnalysis,
												   this.atomicSegments,
												   this.accessedLValues,
												   this.lValues);
		this.topoAccBefore = accBefore.getTopoAccessedBefore();
		
		log.info("Finished analyzing monitor class " + monitorClass.getName());
	}
	
	
	/**
	 * @return the pointer analysisAnalysis
	 */
	public PointerAnalysis getPtrAnalysis() {
		return ptrAnalysis;
	}

	/**
	 * @return the atomic segments
	 */
	public List<AtomicSegment> getAtomicSegments() {
		return atomicSegments;
	}

	/**
	 * @return the accessedLValues in the atomic segments
	 */
	public List<List<Integer>> getAccessedLValues() {
		return accessedLValues;
	}

	/**
	 * @return the map (lvalue id) -> lValue
	 */
	public List<LValueBox> getLValues() {
		return lValues;
	}

	/**
	 * @return the lValues which are out of scope at the beginning of each
	 * 			   atomic segment
	 */
	public List<List<Integer>> getOutOfScope() {
		return outOfScope;
	}

	/**
	 * maps (id of v) -> {(id of w) | v cannot be assigned local lock
	 *  							  w due to accessed-before constraints
	 *  							  in Ranjit's algorithm}
	 * 
	 * @return the topoAccBefore relation
	 */
	public List<List<Integer>> getTopoAccBefore() {
		return topoAccBefore;
	}
}
