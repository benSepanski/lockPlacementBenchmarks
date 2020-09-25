package simple;

import java.util.ArrayList;

public class Incrementer {
    private static int numIncrements = 0;
    private int value = 0;
    private ArrayList<Integer> uselessList = new ArrayList<Integer>();

    /*
     * Increment value and return previous value
     */
    public int incrementValue() {
        numIncrements++;
        uselessList.add(1);
        return value++;
    }

    public int getUselessValue() {
        return uselessList.get(uselessList.size() - 1);
    }

    public static void main(String args[]) {
        Incrementer inc = new Incrementer();
        for(int i = 0; i < 10; ++i) {
            inc.incrementValue();
            System.out.println(inc.getUselessValue());
        }
    }
}
