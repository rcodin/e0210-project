package e0210;

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Map;
import java.util.Stack;
import java.util.StringTokenizer;

import soot.Body;
import soot.Scene;
import soot.SceneTransformer;
import soot.Unit;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ExceptionalBlockGraph;
import java.io.*;
import java.util.*;
import java.lang.Boolean;
import soot.*;
import java.lang.*;
import soot.util.*;
import soot.jimple.*;
import soot.jimple.internal.*;

import soot.Body;
import soot.BodyTransformer;
import soot.toolkits.graph.ExceptionalBlockGraph;
import soot.toolkits.graph.Block;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedWeightedMultigraph;
import org.jgrapht.traverse.TopologicalOrderIterator;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DefaultWeightedEdge;
import soot.jimple.internal.JNopStmt;
import org.jgrapht.alg.AllDirectedPaths;
import org.jgrapht.GraphPath;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.Files;
import java.nio.charset.Charset;
import java.nio.file.StandardOpenOption;

public class SymbolicExecution extends SceneTransformer {
	String project;
	String testcase;
	SymbolicExecution(String proj, String test) {
		project = proj;
		testcase = test;
	}
	/*helper function
	gets block ID list of execeptional block graph from ball ID list
	*/
	ArrayList<Integer> getBlockIDList(HashMap<Integer,LinkedList<Integer>> paths, ArrayList<Integer> ballIDs) {
		ArrayList<Integer> ret = new ArrayList(1000);
		Iterator<Integer> ballIDIt = ballIDs.iterator();
		
		while (ballIDIt.hasNext()) {
			Integer ballID = ballIDIt.next();
			ListIterator<Integer> listIt = paths.get(ballID).listIterator();
			
			while (listIt.hasNext()) {
				Integer blockID = listIt.next();
				ret.add(blockID);
			}
		}
		// System.out.println(ret);
		return ret;
	}
	ArrayList<Integer> getRemovedArrayElement() {
		ArrayList<Integer> ret = new ArrayList(1);
		
		ret.add(0, -1);
		return ret;
	}
	ArrayList<Block> getBlocks(SootMethod method) {
		ArrayList<Block> ret = new ArrayList(1000);
		ExceptionalBlockGraph bGraph = new ExceptionalBlockGraph(method.getActiveBody());
		// Iterator = 
		ret.addAll(bGraph.getBlocks());
		return ret;
	}
	@Override
	protected void internalTransform(String phaseName, Map<String, String> options) {

		
		String inPath = "Testcases/" + project + "/output/" + testcase;
		String outPath = "Testcases/" + project + "/processed-output/" + testcase;
		String metaPath = "src/e0210/process.txt";
		String methodFile = "src/e0210/method.txt";

		System.out.println("Processing " + testcase + " of " + project);
		String in = new String();
		String metaData = new String();
		String methodSigs = new String();
		PrintWriter out = null;
		try {
		// Read the contents of the output file into a string
			in = new String(Files.readAllBytes(Paths.get(inPath)));
			metaData = new String(Files.readAllBytes(Paths.get(metaPath)));
			// System.out.print(metaData);
			methodSigs = new String(Files.readAllBytes(Paths.get(methodFile)));
			out = new PrintWriter(outPath);
		}
		catch(IOException e){
			return ;
			// System.out.println(methodSigs);
		}
		int index = 0;
		StringTokenizer tokenizer = new StringTokenizer(metaData," ");
		String token;
		HashMap<Integer,LinkedList<Integer>> paths = new HashMap();
		int key = 0;
		LinkedList<Integer> path = new LinkedList();
		int vertex;


		//Making the Hashmap of the paths corresponding to ball ID
		while (tokenizer.hasMoreTokens()) {
			token = tokenizer.nextToken();
			if (token.equals("end")) {
				continue;
			}
			else if (token.contains("\n")) {
				paths.put(key, path);//Add the path to set of all paths
				path = new LinkedList();
				token = tokenizer.nextToken();
				key = Integer.parseInt(token);
				// System.out.println(key);
			}
			else {
				vertex = Integer.parseInt(token);
				path.add(vertex);
			}
		}
		paths.put(key, path);//Add the path to set of all paths

		StringTokenizer outTokenizer = new StringTokenizer(in,"\n");
		ListIterator<Integer> pathIt;
		HashMap<String,LinkedList<Integer>> threadPaths = new HashMap();
		
		int lastKey = -1;
		//<tid,<method sig,<number of time executed before, ball id>>>
		HashMap<String,HashMap<String,HashMap<Integer,ArrayList<Integer>>>> table = new HashMap();
		String tID = new String();//thread id
		String mSign = new String();//method signature
		Integer numInvoke;
		Integer ballID;
		while (outTokenizer.hasMoreTokens()) {
			mSign = outTokenizer.nextToken();//Methode signature
			tID = outTokenizer.nextToken();//Thread id
			numInvoke = Integer.parseInt(outTokenizer.nextToken());//number of method invokation
			ballID = Integer.parseInt(outTokenizer.nextToken());//ball larus id

			HashMap<String,HashMap<Integer,ArrayList<Integer>>> l1Elem = table.get(tID);
			if (l1Elem == null) {
				l1Elem = new HashMap();
				HashMap<Integer,ArrayList<Integer>> l2Elem = l1Elem.get(mSign);
				//<method sig,<number of time executed before, ball id>
				if (l2Elem == null) {
					l2Elem = new HashMap();
					ArrayList ballIDs = l2Elem.get(numInvoke); 
					//number of time executed before, ball id
					if (ballIDs == null) {
						ballIDs = new ArrayList(1000);
						ballIDs.add(ballID);
					}
					else {
						ballIDs.add(ballID);
					}
					l2Elem.put(numInvoke, ballIDs);
				}
				else {
					ArrayList ballIDs = l2Elem.get(numInvoke); 
					//number of time executed before, ball id
					if (ballIDs == null) {
						ballIDs = new ArrayList(1000);
						ballIDs.add(ballID);
					}
					else {
						ballIDs.add(ballID);
					}
					l2Elem.put(numInvoke, ballIDs);
				}
				l1Elem.put(mSign, l2Elem);
			}
			else {
				HashMap<Integer,ArrayList<Integer>> l2Elem = l1Elem.get(mSign);
				//<method sig,<number of time executed before, ball id>
				if (l2Elem == null) {
					l2Elem = new HashMap();
					ArrayList ballIDs = l2Elem.get(numInvoke); 
					//number of time executed before, ball id
					if (ballIDs == null) {
						ballIDs = new ArrayList(1000);
						ballIDs.add(ballID);
					}
					else {
						ballIDs.add(ballID);
					}
					l2Elem.put(numInvoke, ballIDs);
				}
				else {
					ArrayList ballIDs = l2Elem.get(numInvoke); 
					//number of time executed before, ball id
					if (ballIDs == null) {
						ballIDs = new ArrayList(1000);
						ballIDs.add(ballID);
					}
					else {
						ballIDs.add(ballID);
					}
					l2Elem.put(numInvoke, ballIDs);
				}
				l1Elem.put(mSign, l2Elem);
			}
			table.put(tID,l1Elem);
		}
		// System.out.println(table.toString());
		/*Start traversing through code*/
		// HashMap<String, String> orderVariables = new HashMap();
		HashMap<String, ArrayList<String>> statements = new HashMap();//the key is tid_methodName_noOfExecution_sta
		//order variable is O_tid_methodName_noOfExecution
		Stack<ArrayList<String>> functionCallStack = new Stack();//fucntion call stack(each entry tid, method name, no of invocation)
		Stack<ArrayList<Integer>> blockIDStack = new Stack();//each entry is a list of block IDs left to traverse in a function call
		Stack<Iterator<Unit>> unitItStack = new Stack();//each entry is iterator will go through Units 

		Iterator<String> threadIt = table.keySet().iterator();
		while(threadIt.hasNext()) {
			tID = threadIt.next();//tID is a String 
			//differntiate between main and thread class
			if (tID.equals("1")) { //main thread
				HashMap<String,HashMap<Integer,ArrayList<Integer>>> mainMethods = table.get("1");
				Iterator<String> mainSigs = mainMethods.keySet().iterator();
				String mainSign = new String(); //Signature of main method of main class of main thread

				while(mainSigs.hasNext()) {
					String sigs = mainSigs.next();

					if(sigs.contains(".Main: void main(java.lang.String[])")) {
						mainSign = sigs;
					// System.out.println(mainSign);
						break;
					}
				}
				Body mainBody = Scene.v().getMethod(mainSign).getActiveBody();
				ExceptionalBlockGraph bGraph = new ExceptionalBlockGraph(mainBody);
				// System.out.println(bGraph.size());
				Object[] tempObj = bGraph.getBlocks().toArray();
				Block[] blocks = new Block[1000];
				if (tempObj[0] instanceof Block) {
					for (int i = 0; i < bGraph.size(); i++)
						blocks[0] = (Block)tempObj[0];
				}
				Iterator<Integer> ballIDList = table.get(tID).get(mainSign).get(0).iterator();
				table.get(tID).get(mainSign).put(0, getRemovedArrayElement());
				ArrayList<Integer> blockIDs = new ArrayList(1000);
				while(ballIDList.hasNext()) {
					Integer temp = ballIDList.next();
					ListIterator<Integer> listIt = paths.get(temp).listIterator();
					while(listIt.hasNext())
						blockIDs.add(listIt.next());
						// System.out.println("lim");
				}
				//if function call happens put things in stack
				ArrayList<String> entryIndex = new ArrayList(3);
				entryIndex.add(tID);
				entryIndex.add(mainSign);
				entryIndex.add("0");
				functionCallStack.push(entryIndex);
				Integer blockID = blockIDs.remove(0);
				Iterator<Unit> unitIt = blocks[blockID].iterator();
				blockIDStack.push(blockIDs);
				unitItStack.push(unitIt);

				//generic code will run using stack
				outloop:
				while (!functionCallStack.empty()) {
					ArrayList<String> temp1 = functionCallStack.pop();
					// System.out.println
					blockIDs = blockIDStack.pop();
					unitIt = unitItStack.pop();
					while (unitIt.hasNext()) {
						Unit unit = unitIt.next();
						


						if(unit instanceof InvokeStmt) {
							InvokeStmt invokeStmt = (InvokeStmt)unit;
							if (invokeStmt.toString().contains("PoP_Util")) {

							}
							else if (invokeStmt.toString().contains("void start()")) {

							}
							else if (invokeStmt.toString().contains("void join()")) {

							}
							else if (invokeStmt.toString().contains("void lock()")) {

							}
							else if (invokeStmt.toString().contains("void unlock()")) {

							}
							else {
								//symbolic constraint generation
								SootMethod calledMethod = invokeStmt.getInvokeExpr().getMethod();
								int i = 0;
								while (true) {
									//push necessary entries in the stack
									if (table.get(tID).get(calledMethod.getSignature()).get(i) != null) {
										if (table.get(tID).get(calledMethod.getSignature()).get(i).get(0)
											 == -1) {
											i++;
											continue;
										}
									}
									else {
											break;
									}
									ArrayList<String> temp2 = new ArrayList(3);
									temp2.add(tID);
									temp2.add(calledMethod.getSignature());
									temp2.add(new Integer(i).toString());
									functionCallStack.push(temp2);
									blockIDs = getBlockIDList(paths, table.get(tID).
												get(calledMethod.getSignature()).get(i));
									blockID = blockIDs.remove(0);
									unitIt = blocks[blockID].iterator();
									blockIDStack.push(blockIDs);
									unitItStack.push(unitIt);
									table.get(tID).get(calledMethod.getSignature()).
												put(i, getRemovedArrayElement());

									getBlocks();









									continue outloop;
								}
							}
						}
					}
					if (blockIDs.isEmpty()) {
						continue;
					}
					else {
						functionCallStack.push(entryIndex);
						blockID = blockIDs.remove(0);
						blockIDStack.push(blockIDs);
						unitIt = blocks[blockID].iterator();
						unitItStack.push(unitIt);
					}
				}
			}
			else {//other threads
				//here run is the main method
				HashMap<String,HashMap<Integer,ArrayList<Integer>>> mainMethods = table.get(tID);
				Iterator<String> threadMethodSigns = mainMethods.keySet().iterator();
				String runMethodSign = new String(); //Signature of run method of thread class of child of main thread
				while(threadMethodSigns.hasNext()) {
					String sigs = threadMethodSigns.next();

					if(sigs.contains("void run()")) {
						runMethodSign = sigs;
					// System.out.println(mainSign);
						break;
					}
				}
			}
		}
		out.close();
		
	    return;
	}

}
