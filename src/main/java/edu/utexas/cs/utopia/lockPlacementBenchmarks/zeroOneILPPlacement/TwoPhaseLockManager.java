package edu.utexas.cs.utopia.lockPlacementBenchmarks.zeroOneILPPlacement;

import java.util.Stack;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Manage a 2-phase locking protocol for implementing nested atomic sections
 * by insisting:
 * 		- locks are never released while inside of an atomic section
 *      - Once outside of all atomic sections, all obtained locks 
 *        are released
 * 
 * All fields are "ThreadLocal", so all the methods are thread-safe
 * and will not be affected by other threads entering/exiting
 * atomic sections
 * 
 * Note that we rely on the user to avoid deadlock by obtaining
 * locks in a safe order.
 */
class TwoPhaseLockManager {
	// A thread local stack of locks, initializing to empty stack
	private ThreadLocal<Stack<ReentrantLock>> 
		obtainedLocks = new ThreadLocal<Stack<ReentrantLock>>() {
			@Override protected Stack<ReentrantLock> initialValue() {
				return new Stack<ReentrantLock>();
			}
		};
	// A thread local nesting count, initializing to 0
	private ThreadLocal<Integer> 
		nestedLevel = new ThreadLocal<Integer>() {
			@Override protected Integer initialValue() {
				return 0;
			}
		};
	
	/**
	 * Indicate that we have entered an atomic section by
	 * incrementing nested level
	 */
	public void enterAtomicSegment() {
		nestedLevel.set(nestedLevel.get()+1);
	}
	
	/**
	 * Exit an atomic section, and if we are no longer in
	 * any atomic segments (i.e. nested level is 0) then
	 * release all obtained locks (in the opposite order of which
	 * they were obtained)
	 */
	public void exitAtomicSegment() {
		int prevNestedLevel = nestedLevel.get();
		if(prevNestedLevel <= 0) {
			throw new RuntimeException("Unmatched exitAtomicSegment");
		}
		nestedLevel.set(prevNestedLevel-1);
		if(prevNestedLevel == 1) {
			Stack<ReentrantLock> localObtainedLocks = obtainedLocks.get();
			while(!localObtainedLocks.isEmpty()) {
				localObtainedLocks.pop().unlock();
			}
		}
	}
	
	/**
	 * Obtain a lock and record that we have it
	 * 
	 * @param lock the lock to obtain
	 */
	public void obtainLock(ReentrantLock lock) {
		lock.lock();
		obtainedLocks.get().push(lock);
	}
}
