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

	static {
		/* The global_trace will be copied to the current directory before running the test case */
		String globalTrace = new String();
		try {
			BufferedReader br = new BufferedReader(new FileReader("global_trace"));
			globalTrace = br.toString();
		// System.out.println("sadddddddddddddddddddddd********************************");
		}
		catch (IOException e){
			System.out.println("sadddddddddddddddddddddd********************************");       
		}
		for (int i = 0; i < 10001; i++)
			threadID[i] = "0";
		//parse the global trace
		
		StringTokenizer tokenizer = new StringTokenizer(globalTrace,"\n");
		while (tokenizer.hasMoreTokens()) {
			String globalTraceEntry = tokenizer.nextToken();
			StringTokenizer lineTokenizer = new StringTokenizer(globalTraceEntry,", ");			
			ArrayList<String> parseGlobalTraceEntry = new ArrayList(3);

			while (lineTokenizer.hasMoreTokens()) {
				String globalTraceEntryElement = lineTokenizer.nextToken();

				parseGlobalTraceEntry.add(globalTraceEntryElement);
			}
			globalEntriesQueue.add(parseGlobalTraceEntry);
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
		String tID =  Integer.toString((int)Thread.currentThread().getId());

		while (!globalTraceEntry.get(0).equals(tID)) {
			try {
				obj.wait();
			}
			catch (InterruptedException e) {
				e.printStackTrace();
			}
			globalTraceEntry = globalEntriesQueue.peek();
		}
	}

	/* You can modify criticalAfter() to receive the required arguments */
	public static void criticalAfter () {
		globalEntriesQueue.remove();
		obj.notifyAll();
	}
}
