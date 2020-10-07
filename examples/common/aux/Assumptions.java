package aux;

public class Assumptions
{
    public static void assume(boolean b)
    {
        if (!b)
        {
            throw new RuntimeException();
        }
    }
}
