package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;

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
		HashMap<LValueBox, HashSet<LValueBox>> edgeList = new HashMap<>();
		for(LValueBox lvb : sharedLValues) {
			edgeList.put(lvb,  new HashSet<LValueBox>());
		}
		log.debug("Adding accessed before relations from class methods");
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
		// Get topo sort and sccs
		ArrayList<LValueBox> revTopoSort = revTopoSortNodes(edgeList, null);
		ArrayList<HashSet<LValueBox>> sccs = getSCCs(edgeList);
		log.debug("Building accessedBefore relation");
		// Create ordering
		accessedBefore = new HashMap<>();
		for(HashSet<LValueBox> scc : sccs) {
			for(LValueBox lvb : scc) {
				// 	This is accessed before everything in its SCC
				accessedBefore.put(lvb, scc);
			}
		}
		ArrayList<LValueBox> seen = new ArrayList<>();
		for(LValueBox lvb : revTopoSort) {
			// this is accessed before everything that comes after it
			// in the topo sort
			for(LValueBox seenLVal : seen) {
				accessedBefore.get(lvb).add(seenLVal);
			}
			seen.add(lvb);
		}
	}
	
	/**
	 * Get a list of the strongly connected components
	 */
	private ArrayList<HashSet<LValueBox>> getSCCs(HashMap<LValueBox, HashSet<LValueBox>> edgeList) {
		ArrayList<LValueBox> revTopoOrder = revTopoSortNodes(edgeList, null);
		// build transpose graph
		HashMap<LValueBox, HashSet<LValueBox>> transposeEdgeList = new HashMap<>();
		for(Entry<LValueBox, HashSet<LValueBox>> entry : edgeList.entrySet()) {
			LValueBox from = entry.getKey();
			for(LValueBox to : entry.getValue()) {
				transposeEdgeList.getOrDefault(to, new HashSet<LValueBox>()).add(from);
			}
		}
		// get topo sort of transpose graph using reverse topoOrder
		ArrayList<LValueBox> transposeRevTopoOrder = revTopoSortNodes(transposeEdgeList, revTopoOrder);
		// This will map lvalues to their scc index
		HashMap<LValueBox, Integer> lValToScc = new HashMap<>();

		// In same connected component iff a <= b (topo sort)
		// and b <=_T a (transpose topo sort)
		// So, last element in topo sort has same SCC as everything
		// after it in transpose topo sort
		Iterator<LValueBox> revTopoSortIter = revTopoOrder.iterator(),
			transposeRevTopoSortIter = transposeRevTopoOrder.iterator();
		// For each value in reverse topological order
		int numSccs = 0;
		while(revTopoSortIter.hasNext()) {
			// See if we've already computed this value's SCC
			LValueBox next = revTopoSortIter.next();
			if(lValToScc.containsKey(next)) {
				continue;
			}
			// If not, add everything that comes after it in the transpose topological
			// order to its scc
			lValToScc.put(next, numSccs);
			LValueBox transposeNext = transposeRevTopoSortIter.next();
			while(!transposeNext.equals(next)) {
				lValToScc.put(transposeNext, numSccs);
				transposeNext = transposeRevTopoSortIter.next();
			}
			numSccs++;
		}
		ArrayList<HashSet<LValueBox>> sccs = new ArrayList<>();
		for(int i = 0; i < numSccs; ++i) {
			sccs.add(new HashSet<LValueBox>());
		}
		for(Entry<LValueBox, Integer> entry : lValToScc.entrySet()) {
			sccs.get(entry.getValue()).add(entry.getKey());
		}
		return sccs;
	}
	
	/**
	 * Returns a reverse topological sort of the nodes
	 * by doing a dfs and recording the visited order
	 * 
	 * Runs a dfs on each node in the order given by dfsOrder.
	 * If dfsOrder is null, the ordering is undefined.
	 * 
	 * @param edgeList
	 * @param dfsOrder
	 * @return
	 */
	private ArrayList<LValueBox> revTopoSortNodes(HashMap<LValueBox, HashSet<LValueBox>> edgeList,
											      ArrayList<LValueBox> dfsOrder) {
		// initial status is unvisited
		HashMap<LValueBox, DFS_STATUS> status = new HashMap<>();
		for(LValueBox lvb : edgeList.keySet()) {
			status.put(lvb, DFS_STATUS.UNVISITED);
		}
		// if no order given, make one
		if(dfsOrder == null) {
			dfsOrder = new ArrayList<LValueBox>(edgeList.keySet());
		}
		ArrayList<LValueBox> revTopoSort = new ArrayList<>();
		for(LValueBox lvb : dfsOrder) {
			dfs(edgeList, lvb, status, revTopoSort);
		}
		// Topo sort is reverse of visiting order
		return revTopoSort;
	}
	
	private static enum DFS_STATUS {
		UNVISITED, VISITING, VISITED
	}
	/**
	 * DFS from current node, recording status as we go.
	 * Store the order in which nodes are visited (return from dfs)
	 * in visitedOrder
	 * 
	 * @param curNode
	 * @param status
	 * @param visitedOrder
	 */
	private void dfs(HashMap<LValueBox, HashSet<LValueBox>> edgeList,
					 LValueBox curNode,
					 HashMap<LValueBox, DFS_STATUS> status,
					 ArrayList<LValueBox> visitedOrder) {
		status.put(curNode, DFS_STATUS.VISITING);
		for(LValueBox nbr : edgeList.get(curNode)) {
			if(status.get(nbr).equals(DFS_STATUS.UNVISITED)) {
				dfs(edgeList, nbr, status, visitedOrder);
			}
		}
		status.put(curNode, DFS_STATUS.VISITED);
		visitedOrder.add(curNode);
	}
}
