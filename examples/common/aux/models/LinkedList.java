package aux.models;

import static aux.Assumptions.assume;

public class LinkedList<T>
{

    private T objs;

    private int size;

    public boolean isEmpty()
    {
        return size == 0;
    }

    public void add(T obj)
    {
        objs = obj;
        size++;
    }

    public T remove()
    {
        assume(size > 0);
        size--;
        return objs;
    }

    public int size()
    {
        return size;
    }
}