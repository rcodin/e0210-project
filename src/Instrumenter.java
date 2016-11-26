import java.io.*;
import java.util.*;
import java.lang.Boolean;
import java.lang.*;

public class Instrumenter {
    private static String[] threadID = new String[10001];
    private static int[] counter = new int[10001];
    private static ArrayList<HashMap<String, Integer>> methodCounters = new ArrayList(10001); //outer hashmap using thread id 
    // inner hashmap using method signature it contains the key value for 
    // Instrumenter() {
    static { 
        for (int i = 0; i < 10001; i++) {
            methodCounters.add(i, null);
            threadID[i] = "0";
        }
    }
    // }
    public synchronized static void getTIDaBID(String methodName,long bID, int count) {
        Thread curr = Thread.currentThread();
        long id = curr.getId();
        HashMap<String, Integer> methodCounter;
        // methodCounter = methodCounters.get((int)id);

        System.out.println(methodName+"\n"+threadID[(int)id]+"\n"+count+"\n"+bID);
    }
    public synchronized static int setMethodCounter(String methodName) {
        Thread curr = Thread.currentThread();
        long id = curr.getId();
        HashMap<String, Integer> methodCounter;

        methodCounter = methodCounters.get((int)id);
        if (methodCounter == null) {//initialize
            methodCounter = new HashMap();
            methodCounter.put(methodName, 0);
            // System.out.println("dddddddddd");
        }
        else {//increment counter by 1 
            if (methodCounter.get(methodName) == null) {
                methodCounter.put(methodName, 0);
                // System.out.println("dddddddddd");
            }
            else {
                // System.out.println("dddddddddd");
                methodCounter.put(methodName, methodCounter.get(methodName) + 1);
            }
        }
        methodCounters.set((int)id, methodCounter);
        return (int)methodCounter.get(methodName);
        // return 1;
    }
    public synchronized static void setTID(Thread child) {
        String temp = new String();//temporary variable to create the thread ID string
        Long cID, pID;//cID is child ID and pID is parent ID
        Thread parent;

        parent = Thread.currentThread();
        pID = parent.getId();
        cID = child.getId();
        temp = temp.concat(threadID[pID.intValue()]+"."+ String.valueOf(counter[pID.intValue()]));
        counter[pID.intValue()] ++;
        threadID[(int)child.getId()] = temp;
    }
}