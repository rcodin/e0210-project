package pop_replay;


import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.StringTokenizer;
import java.util.LinkedList;

public class PoP_Replay_Util 
{
	private static int[] counter = new int[10001];
	private static String[] threadID = new String[10001];
	private static LinkedList<ArrayList<String>> globalEntriesQueue = new LinkedList();
	private static Object obj = new Object();
    private static BufferedReader br = null;
	static {
		/* The global_trace will be copied to the current directory before running the test case */
		String globalTrace = new String();
		try {
			br = new BufferedReader(new FileReader("global_trace"));
			// globalTrace = br.toString();
    		while (true) {
                // System.out.println(br.readLine());
                // System.out.println("checkpoint");
                String line = br.readLine();
                if ((line == null)||(line.equals("\n")))
                    break;
                globalTrace = globalTrace.concat(line+"\n");
            }
            System.out.println(globalTrace);
            
		}
		catch (IOException e){
            e.printStackTrace();
			// System.err.println("sadddddddddddddddddddddd********************************");       
		}
        System.out.println("checkpoint");
		for (int i = 0; i < 10001; i++)
			threadID[i] = "0";
		//parse the global trace
		// System.out.println("checkpoint");
  //       System.out.println(globalTrace);
		StringTokenizer tokenizer = new StringTokenizer(globalTrace,"\n");
		while (tokenizer.hasMoreTokens()) {
			String globalTraceEntry = tokenizer.nextToken();
            
			StringTokenizer lineTokenizer = new StringTokenizer(globalTraceEntry,", ");			
			ArrayList<String> parseGlobalTraceEntry = new ArrayList(4);

			while (lineTokenizer.hasMoreTokens()) {
				String globalTraceEntryElement = lineTokenizer.nextToken();

				parseGlobalTraceEntry.add(globalTraceEntryElement);
                // System.out.println(globalTraceEntryElement);
			}
            if (parseGlobalTraceEntry.get(1).equals("Begin")||parseGlobalTraceEntry.get(1).equals("End")) {
                continue;
            }
			globalEntriesQueue.add(parseGlobalTraceEntry);
            // System.out.println(parseGlobalTraceEntry);
        }
	}
	public static void setTID (Thread child) {
		String temp = new String();//temporary variable to create the thread ID string
        Long cID, pID;//cID is child ID and pID is parent ID
        Thread parent;

        parent = Thread.currentThread();
        pID = parent.getId();
        cID = child.getId();
        temp = temp.concat(threadID[pID.intValue()]+"."+ String.valueOf(counter[pID.intValue()]));
        counter[pID.intValue()] ++;
        threadID[(int)child.getId()] = temp;
        System.out.println("Setting thread ID");
	}
	/* You can modify criticalBefore() to receive the required arguments */
	public static void criticalBefore () {
		ArrayList<String> globalTraceEntry = globalEntriesQueue.peek();
		String tID =  threadID[(int)Thread.currentThread().getId()];

        System.out.println(globalTraceEntry.get(0)+" "+tID);
		while (!globalTraceEntry.get(0).equals(tID)) {
            System.out.println("Inside"+globalTraceEntry.get(0)+" "+tID);
            synchronized(obj) {
       //          try {
    			// 	obj.wait();
    			// }
    			// catch (InterruptedException e) {
    			// 	e.printStackTrace();
    			// }
                globalTraceEntry = globalEntriesQueue.peek();
            }
		}
	}

	/* You can modify criticalAfter() to receive the required arguments */
	public static void criticalAfter () {
        System.out.println("criticalAfter");
        synchronized(obj) {
            globalEntriesQueue.remove();
            // obj.notifyAll();
        }
        System.out.println("paassedcriticalAfter");
	}
}
