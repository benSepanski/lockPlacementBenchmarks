package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Body;

/**
 * Builds an accessed before relation.
 * 
 * We say two LValues v1, v2 if there
 * exists a path in an atomic section where 
 * 		v1 is accessed
 * 	    v1 is possibly modified
 * 		v2 is accessed
 * then we say v1 accessedBefore v2.
 * 
 * This induces a graph v1 -> v2 iff v1 accessedBefore v2.
 * 
 * Topologically sort this graph, and define
 * v1 TopoAccessedBefore v2
 * iff 
 * 		v1 is in a nontrivial SCC AND one of the following hold:
 *      	v2 is in the same nontrivial SCC
 *      	v2 is in an SCC succeeding the SCC of v1 in the topological sort
 *      
 * See https://dl.acm.org/doi/pdf/10.1145/1190215.1190260 section 3.3
 * 
 * @author Ben_Sepanski
 *
 */
class AccessedBeforeRelation {
	private static Logger log = LoggerFactory.getLogger(AccessedBeforeRelation.class);
	private List<List<Integer>> topoAccessedBefore;
	
	/**
	 * Get a map from each LValueBox v to {w | v TopoAccessedBefore w}
	 * @return
	 */
	public List<List<Integer>> getTopoAccessedBefore() {
		return topoAccessedBefore;
	}
	
	public AccessedBeforeRelation(PointerAnalysis ptrAnalysis,
							      List<AtomicSegment> atomicSegments,
							      List<List<Integer>> lValuesAccessedIn,
							      List<LValueBox> lValues) {
		// Initialize access graph with no edges
		Map<Integer, Set<Integer>> edgeList = new HashMap<>();
		for(int i = 0; i < lValues.size(); ++i) {
			edgeList.put(i,  new HashSet<Integer>());
		}
		
		/// loop over all atomic segments and compute on all bodies found /////
		log.debug("Building access graph from atomic segments in class methods");
		// used to  sure we don't compute on a body more than once
		Set<Body> accessedBeforeOnBodyComputed = new HashSet<>();  
		AccessedBeforeRelationOnBody accOnBody;

		for(AtomicSegment atSeg : atomicSegments) {
			Body b = atSeg.getBody();
			if(accessedBeforeOnBodyComputed.contains(b)) continue;
			else accessedBeforeOnBodyComputed.add(b);
			
			accOnBody = new AccessedBeforeRelationOnBody(b,
												 ptrAnalysis,
											     atomicSegments,
											     lValuesAccessedIn,
											     lValues);
			Map<Integer, Set<Integer>> accBefore = accOnBody.getAccessedBefore();
			// add edges (id of v) -> (id of w) iff v accessed-Before w
			for(Entry<Integer, Set<Integer>> edges : accBefore.entrySet()) {
				edgeList.get(edges.getKey()).addAll(edges.getValue());
			}
		}
		///////////////////////////////////////////////////////////////////////
		
		/// Compute topo accessed before relation /////////////////////////////
		log.debug("Computing SCCs and topo sort of access graph");
		TarjanAlgorithm<Integer> tarjans = new TarjanAlgorithm<Integer>(edgeList);
		List<Set<Integer>> reverseTopoSCCs = tarjans.getReverseTopoSCCs();
		
		log.debug("Building accessedBefore relation from SCCs");
		// initialize topoAccessedBefore to an empty graph
		topoAccessedBefore = new ArrayList<>();
		for(int i = 0; i < lValues.size(); ++i) {
			topoAccessedBefore.add(new ArrayList<Integer>());
		}
		// We're going in reverse topo order, so at first there
		// are no sccs later in the topo sort
		List<Integer> descendants = new ArrayList<>();
		
		for(Set<Integer> scc : reverseTopoSCCs) {
			// Add this scc to the descendants
			descendants.addAll(scc);
			// If a non-trivial scc, need to add descendants
			// into topoAccessedBefore relation
			if(scc.size() > 1) {
				for(int lValueID : scc) {
					topoAccessedBefore.get(lValueID).addAll(descendants);
				}	
			}
		}
		///////////////////////////////////////////////////////////////////////
	}
}

/**
 * Just an implementation of Tarjan's algorithm....
 * @author Ben_Sepanski
 *
 * @param <N> node class
 */
class TarjanAlgorithm<N> {
	private List<Set<N>> reverseTopoSCCs = new ArrayList<>();
	private HashMap<N, Integer> discoveryIndex = new HashMap<>(),
		leastDescendant = new HashMap<>();
	private Set<N> onStack = new HashSet<>();
	private Stack<N> sccBeingDetermined = new Stack<>();
	private Map<N, Set<N>> edgeList;
	
	/**
	 * Runs Tarjan's algorithm on a graph
	 * 
	 * @param edgeList
	 */
	public TarjanAlgorithm(Map<N, Set<N>> edgeList) {
		this.edgeList = edgeList;
		for(N n : edgeList.keySet()) {
			// If already visited, we know its SCC and have nothing to do
			if(this.discoveryIndex.containsKey(n)) continue;
			this.tarjan(n);
		}
	}
	
	private void tarjan(N curNode) {
		// Mark this node's discovery number, which is also its
		// current least neighbor and put it on the stack
		leastDescendant.put(curNode, discoveryIndex.size());
		discoveryIndex.put(curNode, discoveryIndex.size());
		sccBeingDetermined.push(curNode);
		onStack.add(curNode);
		// Visit all of the node's neighbors
		for(N neighbor : edgeList.get(curNode)) {
			// if neighbor has not been seen before, visit it 
			if(!discoveryIndex.containsKey(neighbor)) {
				tarjan(neighbor);
				// update least descendant if necessary
				if(leastDescendant.get(neighbor) < leastDescendant.get(curNode)) {
					leastDescendant.put(curNode, leastDescendant.get(neighbor));
				}
			}// Otherwise possibly update least descendant
			else if (onStack.contains(neighbor)) {
				if(leastDescendant.get(neighbor) < leastDescendant.get(curNode)) {
					leastDescendant.put(curNode, leastDescendant.get(neighbor));
				}
			}
		}

		// Now check if this node is a root of an SCC
		if(leastDescendant.get(curNode).equals(discoveryIndex.get(curNode))) {
			HashSet<N> curSCC = new HashSet<>();
			N top;
			do {
				top = sccBeingDetermined.pop();
				curSCC.add(top);
				onStack.remove(top);
			} while(!top.equals(curNode));
			reverseTopoSCCs.add(curSCC);
		}
	}
	
	/**
	 * Get the SCCs of the graph in reverse topological order
	 * @return 
	 */
	public List<Set<N>> getReverseTopoSCCs() {
		return this.reverseTopoSCCs;
	}
}
