package simple;

import java.util.ArrayList;

public class Incrementer {
    private int value = 0;

    /*
     * Increment value and return previous value
     */
    public int incrementValue() {
        return value++;
    }

    public static void main(String args[]) {
        Incrementer inc = new Incrementer();
        for(int i = 0; i < 10; ++i) {
            System.out.println(inc.incrementValue());
        }
    }
}
