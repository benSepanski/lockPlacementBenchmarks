package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootClass;
import soot.SootMethod;

public class AccessedBeforeRelation {
	private static Logger log = LoggerFactory.getLogger(AccessedBeforeRelation.class);
	private HashMap<LValueBox, HashSet<LValueBox>> accessedBefore;
	
	/**
	 * Get a map from each LValueBox v to {w | v accessedBefore w}
	 * @return
	 */
	public HashMap<LValueBox, HashSet<LValueBox>> getAccessedBefore() {
		return accessedBefore;
	}
	
	public AccessedBeforeRelation(PointerAnalysis ptrAnalysis,
			  					  SootClass cls,
								  HashSet<LValueBox> sharedLValues) {
		// Initialize graph with no edges
		Map<LValueBox, Set<LValueBox>> edgeList = new HashMap<>();
		for(LValueBox lvb : sharedLValues) {
			edgeList.put(lvb,  new HashSet<LValueBox>());
		}
		log.debug("Building access graph from atomic segments in class methods");
		// Add edges from all method bodies
		AccessedBeforeRelationOnBody accOnBody;
		for(SootMethod mthd : cls.getMethods()) {
			accOnBody = new AccessedBeforeRelationOnBody(ptrAnalysis, mthd.getActiveBody(), sharedLValues);
			for(Entry<LValueBox, HashSet<LValueBox>> edges : accOnBody.getAccessedBefore().entrySet()) {
				LValueBox from = edges.getKey();
				for(LValueBox to : edges.getValue()) {
					edgeList.get(from).add(to);
				}
			}
		}
		log.debug("Computing SCCs and topo sort of access graph");
		TarjanAlgorithm<LValueBox> tarjans = new TarjanAlgorithm<LValueBox>(edgeList);
		ArrayList<HashSet<LValueBox>> reverseTopoSCCs = tarjans.getReverseTopoSCCs();
		
		log.debug("Building accessedBefore relation from SCCs");
		accessedBefore = new HashMap<LValueBox, HashSet<LValueBox>>();
		for(HashSet<LValueBox> scc : reverseTopoSCCs) {
			HashSet<LValueBox> descendants = new HashSet<LValueBox>();
			// If a non-trivial scc, add it
			if(scc.size() > 1) {
				descendants.addAll(scc);
			}
			//all the sccs after this scc (in the toposort)
			descendants.addAll(accessedBefore.keySet());	
			// point lvalues to descendants
			for(LValueBox lvb : scc) {
				accessedBefore.put(lvb, descendants);
			}
		}
	}
}

class TarjanAlgorithm<N> {
	private ArrayList<HashSet<N>> reverseTopoSCCs = new ArrayList<>();
	private HashMap<N, Integer> discoveryIndex = new HashMap<>(),
		leastDescendant = new HashMap<>();
	private HashSet<N> onStack = new HashSet<>();
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
	public ArrayList<HashSet<N>> getReverseTopoSCCs() {
		return this.reverseTopoSCCs;
	}
}
