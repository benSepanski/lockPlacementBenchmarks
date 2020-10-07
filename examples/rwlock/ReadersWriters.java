package rwlock;

import static aux.wuntil.WuntilInterface.waituntil;

public class ReadersWriters
{
    private int readers = 0;
    private boolean writerIn = false;

    private boolean waituntil$pred1()
    {
        return !writerIn;
    }

    public void enterReader()
    {
        waituntil(waituntil$pred1());
        readers++;
    }

    public void exitReader()
    {
        if (readers > 0)
            readers--;
    }

    private boolean waituntil$pred2()
    {
        return readers == 0 && !writerIn;
    }

    public void enterWriter()
    {
        waituntil(waituntil$pred2());
        writerIn = true;
    }

    public void exitWriter()
    {
        writerIn = false;
    }
}
