package aux.localsupport;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;

/**
 * Created by kferles on 11/8/17.
 */
public class LocalPredTracker
{
    private Lock l;

    private Map<Integer, Condition> waiting = new HashMap<>();

    public LocalPredTracker(Lock l)
    {
        this.l = l;
    }

    public void registerAndWait(int local)
    {
        if (!waiting.containsKey(local))
            waiting.put(local, l.newCondition());

        try
        {
            waiting.get(local).await();
        }
        catch (InterruptedException e)
        {
            throw new RuntimeException(e);
        }
    }

    public void removeAndNotify(int local)
    {
        Condition cond = waiting.remove(local);
        cond.signalAll();
    }

    public Iterator<Integer> keysIterator()
    {
        return waiting.keySet().iterator();
    }
}
