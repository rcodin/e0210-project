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
import soot.SootClass;

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
import java.util.ArrayList;
import java.io.BufferedReader;
import java.io.FileReader;


import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Status;
import com.microsoft.z3.ArithExpr;


/*
TODO
*Handle parseInt
*Handle functions with return values
*Handle arithmatic and boolean operations
*Handle clinit function *********Done (needs testing)
*boolean variables at path constraints
*/
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
		System.out.println(ret);
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
		String input = new String();
		PrintWriter out = null;

		HashMap<String, String>	config = new HashMap<String, String>();
		config.put("model", "true");
		Context ctx = new Context(config);
		Solver solver = ctx.mkSolver();
		String inpuPath = "Testcases/" + project + "/input/" + testcase;
		
		// IntExpr intExpr = ctx.mkIntConst("a");
		// IntNum intNum = ctx.mkInt("5");
		// BoolExpr boolExpr = ctx.mkEq(intExpr, intNum);
		// solver.add(boolExpr);
		// solver.check();
		// Model model = solver.getModel();
	 	// IntExpr val = (IntExpr)model.eval(intExpr, true);
	 	// String intVal = val.toString();
		try {
		// Read the contents of the output file into a string
			in = new String(Files.readAllBytes(Paths.get(inPath)));
			metaData = new String(Files.readAllBytes(Paths.get(metaPath)));
			System.out.print(metaData);
			methodSigs = new String(Files.readAllBytes(Paths.get(methodFile)));
			input = new String(Files.readAllBytes(Paths.get(inpuPath)));
			out = new PrintWriter(outPath);
		}
		catch(IOException e){
			return ;
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
				System.out.println(key);
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
		System.out.println(Scene.v().toString());
		HashMap<String, ArrayList<String>> statements = new HashMap();//the key is tid_methodName_noOfExecution_sta
		//order variable is O_tid_methodName_noOfExecution
		Stack<ArrayList<String>> functionCallStack = new Stack();//fucntion call stack(each entry tid, method name, no of invocation)
		Stack<ArrayList<Integer>> blockIDStack = new Stack();//each entry is a list of block IDs left to traverse in a function call
		Stack<Iterator<Unit>> unitItStack = new Stack();//each entry is iterator will go through Units 
		Stack<Integer> currBlockIDStack = new Stack();
		/*<tid,<event no, trace entry>>
		*/
		
		//Shared variable counter		
		HashMap<String, Integer> readRefCounter = new HashMap();
		HashMap<String, Integer> writeRefCounter = new HashMap();

		Iterator<String> threadIt = table.keySet().iterator();
		Iterator<SootClass> appClassIt = Scene.v().getApplicationClasses().iterator();
		while (appClassIt.hasNext()) {
			SootClass sootClass  = appClassIt.next();
			System.out.println(sootClass.toString());
			if (sootClass.toString().contains("popUtil.PoP_Util"))
				continue;
			Iterator<SootField> fieldIt = sootClass.getFields().iterator();
			while (fieldIt.hasNext()) {
				SootField sootField = fieldIt.next();
				if (!(sootField.getType().toString().equals("java.lang.Integer") || sootField.getType().toString().equals("java.lang.Boolean") || 
					sootField.getType().toString().equals("java.lang.Double") || sootField.getType().toString().equals("java.lang.Float")
					|| sootField.getType().toString().equals("int") || sootField.getType().toString().equals("boolean")
					|| sootField.getType().toString().equals("float") || sootField.getType().toString().equals("double")))
					continue;
				readRefCounter.put(sootField.toString(), 0);
				writeRefCounter.put(sootField.toString(), 0);
				System.out.println(sootField.toString()+" Type "+sootField.getType());
			}
		}


		// HashMap<String,HashMap<String,HashMap<Integer,ArrayList<Value>>>> localVals = new HashMap();

		/*Local variable reference count
		<var name, curr count>
		saves the type of local variables at only write
		*/
		HashMap<String, Integer> locRefCounter = new HashMap();
		HashMap<String, String> locVarType = new HashMap();
		HashMap<String, HashMap<Integer, ArrayList<String>>> trace = new HashMap();
		HashMap<String, Integer> eventCount = new HashMap();


		//structures for intra thread constraint creation
		// read/write variable accesses
		HashMap<String, ArrayList<ArrayList<String>>> readShared = new HashMap();
		HashMap<String, ArrayList<ArrayList<String>>> writeShared = new HashMap();

		//lock constraint <tID, lock event number, unlock event number>
		HashMap<String, ArrayList<ArrayList<String>>> lockUnlockPairsPerVariable = new HashMap();
		// HashMap<String, ArrayList<ArrayList<String>>> unLockEntryVars = new HashMap();
		
		//join events (fork events added at the time of trace collection itself)
		ArrayList<ArrayList<String>> joinEvents = new ArrayList(100);

		//per thread event count
		HashMap<String, Integer> eventCountPerThread = new HashMap(); 

		HashMap<String,HashMap<Integer,ArrayList<Integer>>> mainThreadMethods = table.get("0");
		Iterator<String> mainThreadMethodSigns = mainThreadMethods.keySet().iterator();
		String clinitMethod = new String();
		while(mainThreadMethodSigns.hasNext()) {
			String sigs = mainThreadMethodSigns.next();

			if(sigs.contains(" void <clinit>()")) {
				clinitMethod = sigs;
				break;
			}
		}
		Iterator<SootClass> sootClassIt = Scene.v().getApplicationClasses().iterator();
		while (sootClassIt.hasNext()) {
			SootClass sootClass = sootClassIt.next();
			Iterator<SootMethod> sootMethodIt = sootClass.getMethods().iterator();

			System.out.println(sootClass.toString());
			while (sootMethodIt.hasNext()) {
				SootMethod sootMethod = sootMethodIt.next();
				// if (sootMethod.hasActiveBody())
				// 	System.out.println(sootMethod.getActiveBody().toString());
			}
		}
		StringTokenizer inputTokenizer = new StringTokenizer(input," ");
		Integer arrayIndex = 0;

		while (inputTokenizer.hasMoreTokens()) {
			String inputElement = inputTokenizer.nextToken();//Methode signature

			locRefCounter.put("arg["+arrayIndex.toString()+"]", 1);
			locVarType.put("arg["+arrayIndex.toString()+"]", "java.lang.Integer");
			if (inputTokenizer.hasMoreTokens()) {
				IntExpr intExpr = ctx.mkIntConst("arg["+arrayIndex.toString()+"]");
				IntNum intNum = ctx.mkInt(Integer.parseInt(inputElement));
				
				BoolExpr boolExpr = ctx.mkEq(intExpr, intNum);
				solver.add(boolExpr);
			}
			arrayIndex++;
		}
		System.out.println(Scene.v().getMethod(clinitMethod).getActiveBody().toString());
		//Handle clinit <test4.Main: void <clinit>()>
		// Scene.v().getMethod(mainSign)
		while(threadIt.hasNext()) {
			tID = threadIt.next();
			Integer event_no = 0;
			HashMap<Integer,ArrayList<String>> currThreadEvents = new HashMap();
			ArrayList<String> lockUnLockPair = new ArrayList(3);

			ArrayList<String> beginEvent = new ArrayList(2);
			beginEvent.add(tID);
			beginEvent.add("Begin");
			event_no++;
			System.out.println("Begin event : "+"O_"+tID+"_"+event_no+" "+beginEvent.get(0)+", "+beginEvent.get(1));
			currThreadEvents.put(event_no, beginEvent);
			//<thread_objects, no of threads swawned before this>
			// Value temporary = null;
			HashMap<Value,Integer> threadObjs = new HashMap();
			HashMap<Value,Value> lockLocals = new HashMap();
			int no_of_thread_spawned = 0;
			int no_of_current_event = 0;

			HashMap<String,HashMap<Integer,ArrayList<Integer>>> mainMethods = table.get(tID);
			Iterator<String> mainSigs = mainMethods.keySet().iterator();
			String mainSign = new String(); //Signature of main method of main class of main thread
			if (tID.equals("0")) {
				while(mainSigs.hasNext()) {
					String sigs = mainSigs.next();

					if(sigs.contains(".Main: void main(java.lang.String[])")) {
						mainSign = sigs;
					System.out.println(mainSign);
						break;
					}
				}
			}
			else {
				while(mainSigs.hasNext()) {
					String sigs = mainSigs.next();

					if(sigs.contains(" void run()")) {
						mainSign = sigs;
					System.out.println(mainSign);
						break;
					}
				}	
			}
			ArrayList<Block> mainBlocks = getBlocks(Scene.v().getMethod(mainSign));
			// System.out.println(Scene.v().getMethod(mainSign).getActiveBody());
			ArrayList<Integer> blockIDs = new ArrayList(1000);
			blockIDs = getBlockIDList(paths, table.get(tID).get(mainSign).get(0));
			table.get(tID).get(mainSign).put(0, getRemovedArrayElement());
			ArrayList<String> entryIndex = new ArrayList(3);
			entryIndex.add(tID);
			entryIndex.add(mainSign);
			entryIndex.add("0");
			functionCallStack.push(entryIndex);
			Integer temp5 = blockIDs.remove(0);
			Iterator<Unit> unitIt = mainBlocks.get(temp5).iterator();
			currBlockIDStack.push(temp5);
			blockIDStack.push(blockIDs);
			unitItStack.push(unitIt);
			if (tID.equals("0")) {
				ArrayList<Block> clinitBlocks = getBlocks(Scene.v().getMethod(clinitMethod));
				currBlockIDStack.push(0);
				ArrayList<String> clinitEntry = new ArrayList(3);
				clinitEntry.add(tID);
				clinitEntry.add(clinitMethod);
				clinitEntry.add("0");
				functionCallStack.push(clinitEntry);
				blockIDStack.push(new ArrayList());
				unitItStack.push(clinitBlocks.get(0).iterator());
			}
			//generic code will run using stack
			outloop:
			while (!functionCallStack.empty()) {
				ArrayList<String> temp1 = functionCallStack.pop();

				blockIDs = blockIDStack.pop();
				unitIt = unitItStack.pop();
				Integer currBlockID = currBlockIDStack.pop();
				// System.out.println(Scene.v().getMethod(temp1.get(1)).getActiveBody());
				
				while (unitIt.hasNext()) {
					Unit unit = unitIt.next();

					Status stat1 = solver.check();
					int statInt1 = stat1.toInt();
					if (statInt1 == 1)
						System.out.println("\n\n"+"[SATISFIABLE]"+"\n\n");
					System.out.println(unit.toString());
					if(unit instanceof InvokeStmt) {
						InvokeStmt invokeStmt = (InvokeStmt)unit;
						if (invokeStmt.toString().contains("PoP_Util")) {

						}
						else if (invokeStmt.toString().contains("void start()")) {
							System.out.println("1");
							ArrayList<String> forkEvent = new ArrayList(3);
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();

							forkEvent.add(tID);
							forkEvent.add("Fork");
							String tmp = new String();
							System.out.println("Invoke statememt method is : "+invExpr.getBase());
							tmp = tmp.concat(tID+"."+ String.valueOf(no_of_thread_spawned));
							threadObjs.put(invExpr.getBase(), no_of_thread_spawned);
							forkEvent.add(tmp);
							no_of_thread_spawned++;
							event_no++;
							currThreadEvents.put(event_no, forkEvent);
							System.out.println("Fork event : "+"O_"+tID+"_"+event_no+" "+forkEvent.get(0)+", "+forkEvent.get(1)+", "+forkEvent.get(2));

							String eventOrderVariable = new String();

							eventOrderVariable = eventOrderVariable.concat("O_");
							eventOrderVariable = eventOrderVariable.concat(tID);
							eventOrderVariable = eventOrderVariable.concat("_"+event_no);
							System.out.println(eventOrderVariable);
							IntExpr intExpr1 = ctx.mkIntConst(eventOrderVariable);
							eventOrderVariable = new String();
							eventOrderVariable = eventOrderVariable.concat("O_");
							eventOrderVariable = eventOrderVariable.concat(tmp);
							eventOrderVariable = eventOrderVariable.concat("_1");
							IntExpr intExpr2 = ctx.mkIntConst(eventOrderVariable);
							System.out.println(eventOrderVariable);
							BoolExpr boolExpr = ctx.mkLt(intExpr1, intExpr2);
							solver.add(boolExpr);
						}
						else if (invokeStmt.toString().contains("void join()")) {
							ArrayList<String> joinEvent = new ArrayList(3);
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();

							System.out.println("2");
							joinEvent.add(tID);
							joinEvent.add("Join");
							String tmp = new String();
							System.out.println("Invoke statememt method is : "+invExpr.getBase());
							Integer threadNo = threadObjs.get(invExpr.getBase());
							tmp = tmp.concat(tID+"."+ String.valueOf(threadNo));
							joinEvent.add(tmp);
							event_no++;
							currThreadEvents.put(event_no, joinEvent);
							System.out.println("Join event : "+"O_"+tID+"_"+event_no+" "+joinEvent.get(0)+", "+joinEvent.get(1)+", "+joinEvent.get(2));
							ArrayList<String> orderVariable = new ArrayList();
							orderVariable.add(tID);
							orderVariable.add(String.valueOf((Integer)event_no));
							System.out.println(String.valueOf((Integer)event_no));
							joinEvents.add(orderVariable);
							System.out.println(joinEvent.get(0)+joinEvent.get(1)+joinEvent.get(2));

						}
						else if (invokeStmt.toString().contains("void lock()")) {
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();
							// temporary = invExpr.getBase();
							System.out.println(invExpr.getBase());
							Value local = invExpr.getBase();
							if (lockLocals.get(local) != null) {
								//<tid, Lock, Lock Object>
								System.out.println("3");
								ArrayList<String> lockEvents = new ArrayList(3);
								lockEvents.add(tID);
								lockEvents.add("Lock");
								lockEvents.add(lockLocals.get(local).toString());
								event_no++;
								currThreadEvents.put(event_no, lockEvents);
								System.out.println("Lock event : "+"O_"+tID+"_"+event_no+" "+lockEvents.get(0)+", "+lockEvents.get(1)+", "+lockEvents.get(2));
								// ArrayList<String> lockEventEntry = new ArrayList(2);
								lockUnLockPair.add(tID);
								Integer intEvent =  event_no;
								lockUnLockPair.add(intEvent.toString());
								// if (lockEntryVars.get(lockLocals.get(local).toString()) == null) {
								// 	ArrayList<ArrayList<String>> lockVarLocks = new ArrayList(1001);
								// 	lockVarLocks.add(lockEventEntry);
								// 	lockEntryVars.put(lockLocals.get(local).toString(), lockVarLocks);
								// }
								// else {
								// 	ArrayList<ArrayList<String>> lockVarLocks = lockEntryVars.get(lockLocals.get(local).toString());
								// 	lockVarLocks.add(lockEventEntry);
								// 	lockEntryVars.put(lockLocals.get(local).toString(), lockVarLocks);
								// }

							}
						}
						else if (invokeStmt.toString().contains("void unlock()")) {
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();
							// temporary = invExpr.getBase();
							System.out.println(invExpr.getBase());
							Value local = invExpr.getBase();
							if (lockLocals.get(local) != null) {
								System.out.println("4");
								ArrayList<String> unLockEvents = new ArrayList(3);
								unLockEvents.add(tID);
								unLockEvents.add("Unlock");
								unLockEvents.add(lockLocals.get(local).toString());
								event_no++;
								currThreadEvents.put(event_no, unLockEvents);
								System.out.println("Unlock event : "+"O_"+tID+"_"+event_no+" "+unLockEvents.get(0)+", "+unLockEvents.get(1)+", "+unLockEvents.get(2));
								// ArrayList<String> unLockEventEntry = new ArrayList(2);
								// unLockEventEntry.add(tID);
								Integer intEvent =  event_no;
								lockUnLockPair.add(intEvent.toString());
								if (lockUnlockPairsPerVariable.get(lockLocals.get(local).toString()) == null) {
									ArrayList<ArrayList<String>> lockUnlockPairs = new ArrayList(1001);//This is lock/unlock entry for one variable
									lockUnlockPairs.add(lockUnLockPair);
									lockUnlockPairsPerVariable.put(lockLocals.get(local).toString(), lockUnlockPairs);
								}
								else {
									ArrayList<ArrayList<String>> lockUnlockPairs = lockUnlockPairsPerVariable.get(lockLocals.get(local).toString());//This is lock/unlock entry for one variable
									lockUnlockPairs.add(lockUnLockPair);
									lockUnlockPairsPerVariable.put(lockLocals.get(local).toString(), lockUnlockPairs);
								}
								lockUnLockPair = new ArrayList(3);
							}
						}
						else if (invokeStmt.getInvokeExpr().getMethod().toString().startsWith("<java")) {
							System.out.println("ssdsddddddddddddddddddddddddddddd and stack size is : "+ functionCallStack.size());
							//Get the valueOf functions
							System.out.println("Function name is : "+invokeStmt.getInvokeExpr().getMethod().toString());

						}
						else {

							//symbolic constraint generation
							SootMethod calledMethod = invokeStmt.getInvokeExpr().getMethod();
							
							// calledMethod
							int i = 0;
							while (true) {
								//push necessary entries in the stack
								System.out.println(calledMethod.toString()+" the value of i "+i);
								if (table.get(tID).get(calledMethod.getSignature()).get(i) != null) {
									if (table.get(tID).get(calledMethod.getSignature()).get(i).get(0) == -1) {
										i++;
										continue;
									}
									else {
										i++;
										break;
									}
								}
								else {
										break;
								}	
							}
							i--;//decrement 1 to get the current entry


							functionCallStack.push(temp1);
							if ((!unitIt.hasNext())&&!(blockIDs.isEmpty())) {
								Integer blockID = blockIDs.remove(0);
								ArrayList<Block> tempBlockList = getBlocks(Scene.v().getMethod(temp1.get(1)));//get blocks for current executing function
								Iterator<Unit> stmtIt = tempBlockList.get(blockID).iterator();
								blockIDStack.push(blockIDs);
								unitItStack.push(stmtIt);
								currBlockIDStack.push(blockID);
							}
							else {
								blockIDStack.push(blockIDs);
								unitItStack.push(unitIt);
								currBlockIDStack.push(currBlockID);
							}

								//put thr function in stack
							ArrayList<String> temp2 = new ArrayList(3);
							temp2.add(tID);
							temp2.add(calledMethod.getSignature());
							temp2.add(new Integer(i).toString());
							functionCallStack.push(temp2);
							blockIDs = getBlockIDList(paths, table.get(tID).get(calledMethod.getSignature()).get(i));
							Integer blockID = blockIDs.remove(0);
							ArrayList<Block> blockList = getBlocks(calledMethod);
							unitIt = blockList.get(blockID).iterator();//fix issue using current methods blocks
							blockIDStack.push(blockIDs);
							unitItStack.push(unitIt);
							currBlockIDStack.push(blockID);
							table.get(tID).get(calledMethod.getSignature()).
										put(i, getRemovedArrayElement());
							// ArrayList<Integer> ret =  getRemovedArrayElement();
							continue outloop;
							// }
						}
					}
					else if (unit instanceof AssignStmt) {
						System.out.println("AssignStmt");
						// java.lang.Integer, java.lang.Double, java.lang.Character, java.lang.Boolean, int, double, char and boolean.
						AssignStmt assign = (AssignStmt)unit;
						if (assign.toString().contains("PoP_Util")) {
							continue;
						}
						Value leftOp = assign.getLeftOp();
						Value rightOP = assign.getRightOp();
						String typeStr = leftOp.getType().toString();
						
						if (rightOP instanceof BinopExpr) {
							BinopExpr binopExpr = (BinopExpr)rightOP;
							Value op1 = binopExpr.getOp1();
							Value op2 = binopExpr.getOp2();
							boolean isOp1Constant = false;
							boolean isOp2Constant = false;
							String leftSymName = new String();

							

							if ((binopExpr instanceof AddExpr)||(binopExpr instanceof SubExpr)||
								(binopExpr instanceof RemExpr)||(binopExpr instanceof MulExpr)||
									(binopExpr instanceof DivExpr)) {
								System.out.println("Have arith ops");
								IntExpr intExprOp1 = null;
								IntExpr intExprOp2 = null;
								IntNum intNumOp1 = null;
								IntNum intNumOp2 = null;
								ArithExpr arithExpr = null;
								

								if (op1 instanceof IntConstant) {
									isOp1Constant = true;
									intNumOp1 = ctx.mkInt(op1.toString());
								}
								else {
									intExprOp1 = ctx.mkIntConst(op1.toString()+"_"+locRefCounter.get(op1.toString()));
								}
								if (op2 instanceof IntConstant) {
									isOp2Constant = true;
									intNumOp2 = ctx.mkInt(op2.toString());
								}
								else {
									intExprOp2 = ctx.mkIntConst(op2.toString()+"_"+locRefCounter.get(op2.toString()));
								}
								if (locRefCounter.get(leftOp.toString()) != null)
									locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
								else
									locRefCounter.put(leftOp.toString(), 1);
								locVarType.put(leftOp.toString(), typeStr);
								leftSymName = leftSymName.concat(leftOp.toString());
								leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
								if (binopExpr instanceof AddExpr) {
									System.out.println("add expression is : "+ assign);
									if (isOp1Constant) {
										if (isOp2Constant)
											arithExpr = ctx.mkAdd(intNumOp1, intNumOp2);
										else
											arithExpr = ctx.mkAdd(intNumOp1, intExprOp2);
									}
									else {
										if (isOp2Constant)
											arithExpr = ctx.mkAdd(intExprOp1, intNumOp2);
										else
											arithExpr = ctx.mkAdd(intExprOp1, intExprOp2);
									}

								}
								else if (binopExpr instanceof SubExpr) {
									System.out.println("sub expression is : "+ assign);
									if (isOp1Constant) {
										if (isOp2Constant)
											arithExpr = ctx.mkSub(intNumOp1, intNumOp2);
										else
											arithExpr = ctx.mkSub(intNumOp1, intExprOp2);
									}
									else {
										if (isOp2Constant)
											arithExpr = ctx.mkSub(intExprOp1, intNumOp2);
										else
											arithExpr = ctx.mkSub(intExprOp1, intExprOp2);
									}
								}
								
								else if (binopExpr instanceof RemExpr) {
									System.out.println("Mod expression is : "+ assign);
									if (isOp1Constant) {
										if (isOp2Constant)
											arithExpr = ctx.mkRem(intNumOp1, intNumOp2);
										else
											arithExpr = ctx.mkRem(intNumOp1, intExprOp2);
									}
									else {
										if (isOp2Constant)
											arithExpr = ctx.mkRem(intExprOp1, intNumOp2);
										else
											arithExpr = ctx.mkRem(intExprOp1, intExprOp2);
									}
								}
								else if (binopExpr instanceof MulExpr) {
									System.out.println("Mul expression is : "+ assign);
									if (isOp1Constant) {
										if (isOp2Constant)
											arithExpr = ctx.mkMul(intNumOp1, intNumOp2);
										else
											arithExpr = ctx.mkMul(intNumOp1, intExprOp2);
									}
									else {
										if (isOp2Constant)
											arithExpr = ctx.mkMul(intExprOp1, intNumOp2);
										else
											arithExpr = ctx.mkMul(intExprOp1, intExprOp2);
									}
								}							
								else if (binopExpr instanceof DivExpr) {
									System.out.println("Div expression is : "+ assign);
									if (isOp1Constant) {
										if (isOp2Constant)
											arithExpr = ctx.mkDiv(intNumOp1, intNumOp2);
										else
											arithExpr = ctx.mkDiv(intNumOp1, intExprOp2);
									}
									else {
										if (isOp2Constant)
											arithExpr = ctx.mkDiv(intExprOp1, intNumOp2);
										else
											arithExpr = ctx.mkDiv(intExprOp1, intExprOp2);
									}
								}
								IntExpr leftExpr = ctx.mkIntConst(leftSymName);
								solver.add(ctx.mkEq(leftExpr, arithExpr));
							}
							else {
								System.out.println("Have logic ops");
								BoolExpr boolExprOp1 = null;
								BoolExpr boolExprOp2 = null;
								BoolExpr boolNumOp1 = null;
								BoolExpr boolNumOp2 = null;
								BoolExpr boolExpr = null;
								boolean boolVal = false;

								if (op1 instanceof IntConstant) {
									isOp1Constant = true;
									if (op1.toString().equals("1"))
										boolVal = true;
									boolNumOp1 = ctx.mkBool(boolVal);
								}
								else {
									boolExprOp1 = ctx.mkBoolConst(op1.toString()+"_"+locRefCounter.get(op1.toString()));
								}
								if (op2 instanceof IntConstant) {
									isOp2Constant = true;
									boolVal = false;
									if (op2.toString().equals("1"))
										boolVal = true;
									boolNumOp2 = ctx.mkBool(boolVal);
								}
								else {
									boolExprOp2 = ctx.mkBoolConst(op2.toString()+"_"+locRefCounter.get(op2.toString()));
								}
								if (locRefCounter.get(leftOp.toString()) != null)
									locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
								else
									locRefCounter.put(leftOp.toString(), 1);
								locVarType.put(leftOp.toString(), typeStr);
								leftSymName = leftSymName.concat(leftOp.toString());
								leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
								if (binopExpr instanceof AndExpr) {
									System.out.println("And expression is : "+ assign);
									if (isOp1Constant) {
										if (isOp2Constant)
											boolExpr = ctx.mkAnd(boolNumOp1, boolNumOp2);
										else
											boolExpr = ctx.mkAnd(boolNumOp1, boolExprOp2);
									}
									else {
										if (isOp2Constant)
											boolExpr = ctx.mkAnd(boolExprOp1, boolNumOp2);
										else
											boolExpr = ctx.mkAnd(boolExprOp1, boolExprOp2);
									}
								}
								if (binopExpr instanceof XorExpr) {
									System.out.println("Xor expression is : "+ assign);
									if (isOp1Constant) {
										if (isOp2Constant)
											boolExpr = ctx.mkXor(boolNumOp1, boolNumOp2);
										else
											boolExpr = ctx.mkXor(boolNumOp1, boolExprOp2);
									}
									else {
										if (isOp2Constant)
											boolExpr = ctx.mkXor(boolExprOp1, boolNumOp2);
										else
											boolExpr = ctx.mkXor(boolExprOp1, boolExprOp2);
									}
								}
								else if (binopExpr instanceof XorExpr) {
									System.out.println("Xor expression is : "+ assign);
									if (isOp1Constant) {
										if (isOp2Constant)
											boolExpr = ctx.mkXor(boolNumOp1, boolNumOp2);
										else
											boolExpr = ctx.mkXor(boolNumOp1, boolExprOp2);
									}
									else {
										if (isOp2Constant)
											boolExpr = ctx.mkXor(boolExprOp1, boolNumOp2);
										else
											boolExpr = ctx.mkXor(boolExprOp1, boolExprOp2);
									}
								}
								BoolExpr leftExpr = ctx.mkBoolConst(leftSymName);
								solver.add(ctx.mkEq(leftExpr, boolExpr));
							}
						}
						else if (rightOP.toString().contains("java.util.concurrent.locks.Lock")) {
							lockLocals.put(leftOp, rightOP);
							continue;
						}
						else if (assign.containsInvokeExpr()) {
							
							InvokeExpr invokeExpr = assign.getInvokeExpr();

							SootMethod calledMethod = invokeExpr.getMethod();
							if (calledMethod.toString().startsWith("<java")) {
								//<tID, Write, var name , ref number, value, type, Constant/Variable>
								ArrayList<String> writeEvents = new ArrayList(7);
								
								writeEvents.add(tID);
								writeEvents.add("Write");
								writeEvents.add(leftOp.toString());
								if (typeStr.equals("java.lang.Integer")) {
									if (calledMethod.toString().contains("java.lang.Integer: java.lang.Integer valueOf(int)")) {
										System.out.println("The invoke expression is : "+assign.toString());
										if (invokeExpr.getArg(0) instanceof IntConstant) {
											IntConstant intConst = (IntConstant)invokeExpr.getArg(0);
											System.out.println(assign.toString()+invokeExpr.getArg(0));
											int value = intConst.value;
											String symName = new String();

											if (writeRefCounter.get(leftOp.toString()) != null) {
												System.out.println("5");
												writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
												writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
												
												symName = symName.concat("Write_");
												symName = symName.concat(leftOp.toString());
												symName = symName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());
												
												Integer temp = (Integer)value;
												writeEvents.add(temp.toString());
												writeEvents.add("java.lang.Integer");
												writeEvents.add("Constant");
												event_no++;
												currThreadEvents.put(event_no, writeEvents);
												System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
															writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
															+", "+writeEvents.get(6));


												ArrayList<String> writeEventEntry = new ArrayList(2);
												writeEventEntry.add(tID);
												Integer intEvent =  event_no;
												writeEventEntry.add(intEvent.toString());
												if (writeShared.get(leftOp.toString()) == null) {
													ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
													sharedVarWrites.add(writeEventEntry);
													writeShared.put(leftOp.toString(), sharedVarWrites);
												}
												else {
													ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
													sharedVarWrites.add(writeEventEntry);
													writeShared.put(leftOp.toString(), sharedVarWrites);
												}
											}
											//put it directly in z3
											else if (locRefCounter.get(leftOp.toString()) != null) {
												System.out.println("6");
												locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
												symName = symName.concat(leftOp.toString());
												symName = symName.concat("_"+locRefCounter.get(leftOp.toString()).toString());
											}
											else {
												System.out.println("7");
												locRefCounter.put(leftOp.toString(), 1);
												symName = symName.concat(leftOp.toString());
												symName = symName.concat("_"+locRefCounter.get(leftOp.toString()).toString());	
											}
											locVarType.put(leftOp.toString(), typeStr);

											IntExpr intExpr = ctx.mkIntConst(symName);
											IntNum intNum = ctx.mkInt(value);
											
											BoolExpr boolExpr = ctx.mkEq(intExpr, intNum);
											solver.add(boolExpr);

										}
										else {

											String arg = invokeExpr.getArg(0).toString();
											System.out.println(unit);

											if (readRefCounter.get(arg) != null) {//argument is a global variable
												System.out.println("fuck");
											}
											else if (locRefCounter.get(arg) != null) {
												System.out.println("fuck");
												String readVal = new String();
												String leftSymName = new String();

												// readVal = readVal.concat("Read_");
												readVal = readVal.concat(arg);
												readVal = readVal.concat("_"+locRefCounter.get(arg));
												if (writeRefCounter.get(leftOp.toString()) != null) {
													writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
													writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());

													leftSymName = leftSymName.concat("Write_");
													leftSymName = leftSymName.concat(leftOp.toString());
													leftSymName = leftSymName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());
													// writeEvents.add(temp.toString());
													writeEvents.add(readVal);
													writeEvents.add("java.lang.Integer");
													writeEvents.add("Variable");
													event_no++;


													ArrayList<String> writeEventEntry = new ArrayList(2);
													writeEventEntry.add(tID);
													Integer intEvent =  event_no;
													writeEventEntry.add(intEvent.toString());
													currThreadEvents.put(event_no, writeEvents);
													System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
															+", "+writeEvents.get(6));
													if (writeShared.get(leftOp.toString()) == null) {
														ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
														sharedVarWrites.add(writeEventEntry);
														writeShared.put(leftOp.toString(), sharedVarWrites);
														System.out.println("8");
													}
													else {
														ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
														sharedVarWrites.add(writeEventEntry);
														writeShared.put(leftOp.toString(), sharedVarWrites);
														System.out.println("9");
													}
												}
												//put it directly in z3
												else if (locRefCounter.get(leftOp.toString()) != null) {
													System.out.println(unit);
													locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
													leftSymName = leftSymName.concat(leftOp.toString());
													leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
													System.out.println("10");
												}
												else {
													System.out.println("11");
													System.out.println("fuck");
													System.out.println(unit);
													locRefCounter.put(leftOp.toString(), 1);
													leftSymName = leftSymName.concat(leftOp.toString());
													leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
												}
												System.out.println("fuck");
												locVarType.put(leftOp.toString(), typeStr);
												IntExpr intExpr1 = ctx.mkIntConst(readVal);
												IntExpr intExpr2 = ctx.mkIntConst(leftSymName);
												BoolExpr boolExpr = ctx.mkEq(intExpr1 , intExpr2);
												solver.add(boolExpr);	
											}
											else {
												System.out.println("fuck");
												//this case is not possible because there should be write before a read
											}
										}
									}

								}
								else if (typeStr.equals("int")) {
									
									if (calledMethod.toString().contains("<java.lang.Integer: int intValue()>")) {
										InstanceInvokeExpr instInvokeExpr = (InstanceInvokeExpr)assign.getInvokeExpr();
										Value calledObj = instInvokeExpr.getBase();

										String readVal = new String();
										String leftSymName = new String();
										
										System.out.println("assign : "+assign);
										readVal = readVal.concat(calledObj.toString());
										readVal = readVal.concat("_"+locRefCounter.get(calledObj.toString()));
										System.out.println("Read value is : " + readVal);
										if (writeRefCounter.get(leftOp.toString()) != null) {
											writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
											writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());

											leftSymName = leftSymName.concat("Write_");
											leftSymName = leftSymName.concat(leftOp.toString());
											leftSymName = leftSymName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());
											// readVal = readVal.concat("Read_");
											
											// writeEvents.add(temp.toString());
											writeEvents.add("int");
											writeEvents.add("Variable");
											event_no++;
											currThreadEvents.put(event_no, writeEvents);
											System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
														+", "+writeEvents.get(6));


											ArrayList<String> writeEventEntry = new ArrayList(2);
											writeEventEntry.add(tID);
											Integer intEvent =  event_no;
											writeEventEntry.add(intEvent.toString());
											if (writeShared.get(leftOp.toString()) == null) {
												System.out.println("12");
												ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
												sharedVarWrites.add(writeEventEntry);
												writeShared.put(leftOp.toString(), sharedVarWrites);
											}
											else {
												System.out.println("13");
												ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
												sharedVarWrites.add(writeEventEntry);
												writeShared.put(leftOp.toString(), sharedVarWrites);
											}
										}
										else if (locRefCounter.get(leftOp.toString()) != null) {
											System.out.println("14");
											locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
											leftSymName = leftSymName.concat(leftOp.toString());
											leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
										}
										else {
											System.out.println("15");
											locRefCounter.put(leftOp.toString(), 1);
											leftSymName = leftSymName.concat(leftOp.toString());
											leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
										}
										System.out.println("Write var name : " + leftSymName);
										locVarType.put(leftOp.toString(), typeStr);
										IntExpr intExpr1 = ctx.mkIntConst(leftSymName);
										IntExpr intExpr2 = ctx.mkIntConst(readVal);
										BoolExpr boolExpr = ctx.mkEq(intExpr1 , intExpr2);

										solver.add(boolExpr);	
									}
									else if (calledMethod.toString().contains("java.lang.Integer: int parseInt(java.lang.String)")) {
										System.out.println("Inside parseInt");
										if (invokeExpr.getArg(0) instanceof IntConstant) {
											IntConstant intConst = (IntConstant)invokeExpr.getArg(0);
											System.out.println(assign.toString()+invokeExpr.getArg(0));
											int value = intConst.value;
											String symName = new String();

											if (writeRefCounter.get(leftOp.toString()) != null) {
												
												writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
												writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
												
												symName = symName.concat("Write_");
												symName = symName.concat(leftOp.toString());
												symName = symName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());
												
												Integer temp = (Integer)value;
												writeEvents.add(temp.toString());
												writeEvents.add("int");
												writeEvents.add("Constant");
												event_no++;
												currThreadEvents.put(event_no, writeEvents);
												System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
															writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
															+", "+writeEvents.get(6));


												ArrayList<String> writeEventEntry = new ArrayList(2);
												writeEventEntry.add(tID);
												Integer intEvent =  event_no;
												writeEventEntry.add(intEvent.toString());
												if (writeShared.get(leftOp.toString()) == null) {
													ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
													sharedVarWrites.add(writeEventEntry);
													writeShared.put(leftOp.toString(), sharedVarWrites);
												}
												else {
													ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
													sharedVarWrites.add(writeEventEntry);
													writeShared.put(leftOp.toString(), sharedVarWrites);
												}
											}
											//put it directly in z3
											else if (locRefCounter.get(leftOp.toString()) != null) {
												System.out.println("6");
												locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
												symName = symName.concat(leftOp.toString());
												symName = symName.concat("_"+locRefCounter.get(leftOp.toString()).toString());
											}
											else {
												System.out.println("7");
												locRefCounter.put(leftOp.toString(), 1);
												symName = symName.concat(leftOp.toString());
												symName = symName.concat("_"+locRefCounter.get(leftOp.toString()).toString());	
											}
											locVarType.put(leftOp.toString(), typeStr);

											IntExpr intExpr = ctx.mkIntConst(symName);
											IntNum intNum = ctx.mkInt(value);
											
											BoolExpr boolExpr = ctx.mkEq(intExpr, intNum);
											solver.add(boolExpr);

										}
										else {
											System.out.println("not constant");
											String arg = invokeExpr.getArg(0).toString();
											System.out.println(unit);

											if (readRefCounter.get(arg) != null) {//argument is a global variable
												System.out.println("fuck");
											}
											else if (locRefCounter.get(arg) != null) {
												System.out.println("fuck");
												String readVal = new String();
												String leftSymName = new String();

												// readVal = readVal.concat("Read_");
												readVal = readVal.concat(arg);
												readVal = readVal.concat("_"+locRefCounter.get(arg));
												if (writeRefCounter.get(leftOp.toString()) != null) {
													writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
													writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());

													leftSymName = leftSymName.concat("Write_");
													leftSymName = leftSymName.concat(leftOp.toString());
													leftSymName = leftSymName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());
													// writeEvents.add(temp.toString());
													writeEvents.add(readVal);
													writeEvents.add("int");
													writeEvents.add("Variable");
													event_no++;


													ArrayList<String> writeEventEntry = new ArrayList(2);
													writeEventEntry.add(tID);
													Integer intEvent =  event_no;
													writeEventEntry.add(intEvent.toString());
													currThreadEvents.put(event_no, writeEvents);
													System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
															+", "+writeEvents.get(6));
													if (writeShared.get(leftOp.toString()) == null) {
														ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
														sharedVarWrites.add(writeEventEntry);
														writeShared.put(leftOp.toString(), sharedVarWrites);
														System.out.println("8");
													}
													else {
														ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
														sharedVarWrites.add(writeEventEntry);
														writeShared.put(leftOp.toString(), sharedVarWrites);
														System.out.println("9");
													}
												}
												//put it directly in z3
												else if (locRefCounter.get(leftOp.toString()) != null) {
													System.out.println(unit);
													locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
													leftSymName = leftSymName.concat(leftOp.toString());
													leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
													System.out.println("10");
												}
												else {
													System.out.println("11");
													System.out.println("fuck");
													System.out.println(unit);
													locRefCounter.put(leftOp.toString(), 1);
													leftSymName = leftSymName.concat(leftOp.toString());
													leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
												}
												System.out.println("fuck");
												locVarType.put(leftOp.toString(), typeStr);
												IntExpr intExpr1 = ctx.mkIntConst(readVal);
												IntExpr intExpr2 = ctx.mkIntConst(leftSymName);
												BoolExpr boolExpr = ctx.mkEq(intExpr1 , intExpr2);
												solver.add(boolExpr);	
											}
											else {
												System.out.println("fuck");
												//this case is not possible because there should be write before a read
											}
										}
									}	
								}
								else if (typeStr.equals("java.lang.Boolean")) {
									if (calledMethod.toString().contains("<java.lang.Boolean: java.lang.Boolean valueOf(boolean)>")) {
										IntConstant intConst = (IntConstant)invokeExpr.getArg(0);
										System.out.println(assign.toString()+invokeExpr.getArg(0));
										int value = intConst.value;
										String symName = new String();

										if (writeRefCounter.get(leftOp.toString()) != null) {
											writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
											writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());

											symName = symName.concat("Write_");
											symName = symName.concat(leftOp.toString());
											symName = symName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());
												
											Integer temp = (Integer)value;
											writeEvents.add(temp.toString());
											writeEvents.add("java.lang.Boolean");
											writeEvents.add("Constant");
											event_no++;
											currThreadEvents.put(event_no, writeEvents);
											System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
														+", "+writeEvents.get(6));


											ArrayList<String> writeEventEntry = new ArrayList(2);
											writeEventEntry.add(tID);
											Integer intEvent =  event_no;
											writeEventEntry.add(intEvent.toString());
											if (writeShared.get(leftOp.toString()) == null) {
												ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
												sharedVarWrites.add(writeEventEntry);
												writeShared.put(leftOp.toString(), sharedVarWrites);
												System.out.println("16");
											}
											else {
												ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
												sharedVarWrites.add(writeEventEntry);
												writeShared.put(leftOp.toString(), sharedVarWrites);
												System.out.println("15");
											}
										}
										else if (locRefCounter.get(leftOp.toString()) != null) {
											System.out.println("16");
											locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
											symName = symName.concat(leftOp.toString());
											symName = symName.concat("_"+locRefCounter.get(leftOp.toString()).toString());
										}
										else {
											System.out.println("17");
											locRefCounter.put(leftOp.toString(), 1);
											symName = symName.concat(leftOp.toString());
											symName = symName.concat("_"+locRefCounter.get(leftOp.toString()).toString());
										}
										locVarType.put(leftOp.toString(), typeStr);
										boolean boolVal = false;
										if (value == 1)
											boolVal = true;
										BoolExpr boolExpr = ctx.mkBoolConst(symName);
										BoolExpr boolNum = ctx.mkBool(boolVal);
										BoolExpr boolExpr1 = ctx.mkEq(boolExpr, boolNum);
										solver.add(boolExpr1);
									}
								}
								else if (typeStr.equals("boolean")) {
									InstanceInvokeExpr instInvokeExpr = (InstanceInvokeExpr)assign.getInvokeExpr();
									Value calledObj = instInvokeExpr.getBase();
									System.out.println(calledObj);

									String readVal = new String();
									String leftSymName = new String();
										
										System.out.println(assign);
									readVal = readVal.concat(calledObj.toString());
									readVal = readVal.concat("_"+locRefCounter.get(calledObj.toString()));
									if (calledMethod.toString().contains("<java.lang.Boolean: boolean booleanValue()>")) {
										if (writeRefCounter.get(leftOp.toString()) != null) {
											writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
											writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
											// String readVal = new String();
											// readVal = readVal.concat("Read_");
											// readVal = readVal.concat(calledObj.toString());
											// readVal = readVal.concat("_"+locRefCounter.get(calledObj.toString()));
											// writeEvents.add(temp.toString());

											leftSymName = leftSymName.concat("Write_");
											leftSymName = leftSymName.concat(leftOp.toString());
											leftSymName = leftSymName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());

											writeEvents.add("int");
											writeEvents.add("Variable");
											event_no++;
											currThreadEvents.put(event_no, writeEvents);
											System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
														+", "+writeEvents.get(6));


											ArrayList<String> writeEventEntry = new ArrayList(2);
											writeEventEntry.add(tID);
											Integer intEvent =  event_no;
											writeEventEntry.add(intEvent.toString());
											if (writeShared.get(leftOp.toString()) == null) {
												System.out.println("18");
												ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
												sharedVarWrites.add(writeEventEntry);
												writeShared.put(leftOp.toString(), sharedVarWrites);
											}
											else {
												System.out.println("19");
												ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
												sharedVarWrites.add(writeEventEntry);
												writeShared.put(leftOp.toString(), sharedVarWrites);
											}
										} 
										else if (locRefCounter.get(leftOp.toString()) != null) {
											System.out.println("20");
											locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
											leftSymName = leftSymName.concat(leftOp.toString());
											leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
										}
										else {
											System.out.println("21");
											locRefCounter.put(leftOp.toString(), 1);
											leftSymName = leftSymName.concat(leftOp.toString());
											leftSymName = leftSymName.concat("_"+ locRefCounter.get(leftOp.toString()).toString());
										}
										locVarType.put(leftOp.toString(), typeStr);
										BoolExpr intExpr1 = ctx.mkBoolConst(leftSymName);
										BoolExpr intExpr2 = ctx.mkBoolConst(readVal);
										BoolExpr boolExpr = ctx.mkEq(intExpr1 , intExpr2);
										solver.add(boolExpr);
									}
								}
								else if (typeStr.equals("java.lang.Double")) {
									
								}
								else if (typeStr.equals("double")) {
									
								}
								else if (typeStr.equals("java.lang.Float")) {
									
								}
								else if (typeStr.equals("float")) {
									
								}
								continue;
							}
							// calledMethod
							int i = 0;
							while (true) {
								//push necessary entries in the stack
								System.out.println(calledMethod.toString()+" the value of i "+i);
								if (table.get(tID).get(calledMethod.getSignature()).get(i) != null) {
									if (table.get(tID).get(calledMethod.getSignature()).get(i).get(0) == -1) {
										i++;
										continue;
									}
									else {
										i++;
										break;
									}
								}
								else {
										break;
								}	
							}
							i--;//decrement 1 to get the current entry


							functionCallStack.push(temp1);
							if ((!unitIt.hasNext())&&!blockIDs.isEmpty()) {
								Integer blockID = blockIDs.remove(0);
								ArrayList<Block> tempBlockList = getBlocks(Scene.v().getMethod(temp1.get(1)));//get blocks for current executing function
								Iterator<Unit> stmtIt = tempBlockList.get(blockID).iterator();
								blockIDStack.push(blockIDs);
								unitItStack.push(stmtIt);
								currBlockIDStack.push(blockID);
							}
							else {
								blockIDStack.push(blockIDs);
								unitItStack.push(unitIt);
								currBlockIDStack.push(currBlockID);	
							}

								//put thr function in stack
							ArrayList<String> temp2 = new ArrayList(3);
							temp2.add(tID);
							temp2.add(calledMethod.getSignature());
							temp2.add(new Integer(i).toString());
							functionCallStack.push(temp2);
							blockIDs = getBlockIDList(paths, table.get(tID).get(calledMethod.getSignature()).get(i));
							Integer blockID = blockIDs.remove(0);
							ArrayList<Block> blockList = getBlocks(calledMethod);
							unitIt = blockList.get(blockID).iterator();//fix issue using current methods blocks
							blockIDStack.push(blockIDs);
							unitItStack.push(unitIt);
							currBlockIDStack.push(blockID);
							table.get(tID).get(calledMethod.getSignature()).
										put(i, getRemovedArrayElement());
							continue outloop;
						}
						//$i = 5 or $i = $r
						else {
							boolean isConstant = false;//flag to specify there is concrete value present in the write side or not
							if (rightOP.toString().contains("args[")) {
								System.out.println("args");
								String rightSym = new String();
								String leftSym = new String();

								rightSym = rightSym.concat(rightOP.toString()+"_"+locRefCounter.get(rightOP.toString()));
								if (locRefCounter.get(leftOp.toString()) != null) {
									locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
									locVarType.put(leftOp.toString(), "int");
									System.out.println("28");
								}
								else {
									locRefCounter.put(leftOp.toString(), 1);
									locVarType.put(leftOp.toString(), "int");
									System.out.println("29");
								}
								leftSym = leftSym.concat(leftOp.toString()+"_"+locRefCounter.get(leftOp.toString()));

								IntExpr intExpr1 = ctx.mkIntConst(leftSym);
								IntExpr intExpr2 = ctx.mkIntConst(rightSym);
								BoolExpr boolExpr = ctx.mkEq(intExpr1, intExpr2);
								solver.add(boolExpr);
							}
							if (typeStr.equals("java.lang.Integer") || typeStr.equals("java.lang.Boolean") || 
								typeStr.equals("java.lang.Double") || typeStr.equals("java.lang.Float") || 
								typeStr.equals("int") || typeStr.equals("float") || typeStr.equals("boolean") 
								|| typeStr.equals("double")) {
								ArrayList<String> rwConstraints = new ArrayList(5);
								String readVal = new String();
								// <tid, Read/Write, var name, ref number, type>
								rwConstraints.add(tID);
								readVal = rightOP.toString();
								if (readRefCounter.get(rightOP.toString()) != null) {
									//shared variable
									readRefCounter.put(rightOP.toString(), readRefCounter.get(rightOP.toString()) + 1);
									ArrayList<String> readEvent = new ArrayList(5);
									readEvent.add(tID);
									readEvent.add("Read");
									readEvent.add(rightOP.toString());
									readEvent.add(readRefCounter.get(rightOP.toString()).toString());
									readEvent.add(typeStr);
									event_no++;

									ArrayList<String> readEventEntry = new ArrayList(2);
									readEventEntry.add(tID);
									Integer intEvent =  event_no;
									readEventEntry.add(intEvent.toString());
									currThreadEvents.put(event_no, readEvent);
									if (readShared.get(rightOP.toString()) == null) {
										ArrayList<ArrayList<String>> sharedVarReads = new ArrayList(1001);
										sharedVarReads.add(readEventEntry);
										readShared.put(rightOP.toString(), sharedVarReads);
										System.out.println("22");
									}
									else {
										ArrayList<ArrayList<String>> sharedVarReads = readShared.get(rightOP.toString());
										sharedVarReads.add(readEventEntry);
										readShared.put(rightOP.toString(), sharedVarReads);
										System.out.println("23");
									}
									System.out.println(unit.toString());
									System.out.println("O_"+tID+"_"+event_no+" "+readEvent.get(0)+", "+readEvent.get(1)+", "+readEvent.get(2)+", "+readEvent.get(3)+", "+readEvent.get(4));
								}
								else {
									if (rightOP instanceof Constant) {
										//<tID, Write, var name , ref number, value, type, Constant/Variable>
										ArrayList<String> writeEvents = new ArrayList(7);
										String symName = new String();


										writeEvents.add(tID);
										writeEvents.add("Write");
										writeEvents.add(leftOp.toString());
										isConstant = true;
										System.out.println("constant");
										//add directly to z3
										if (typeStr.equals("java.lang.Integer")) {
											if (writeRefCounter.get(leftOp.toString()) != null) {
												// writeEvents.add(3, );
												System.out.println("24");
											}
										}
										else if (typeStr.equals("int")) {
											IntConstant intConst = (IntConstant)rightOP; 
											if (writeRefCounter.get(leftOp.toString()) != null) {
												writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());

												//for z3
												symName = symName.concat("Write_");
												symName = symName.concat(leftOp.toString());
												symName = symName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());
												

												writeEvents.add(intConst.toString());
												writeEvents.add(typeStr);
												writeEvents.add("Constant");
												event_no++;
												currThreadEvents.put(event_no, writeEvents);
												System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
													writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
													+", "+writeEvents.get(6));


												ArrayList<String> writeEventEntry = new ArrayList(2);
												writeEventEntry.add(tID);
												Integer intEvent =  event_no;
												writeEventEntry.add(intEvent.toString());
												if (writeShared.get(leftOp.toString()) == null) {
													ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
													sharedVarWrites.add(writeEventEntry);
													writeShared.put(leftOp.toString(), sharedVarWrites);
													System.out.println("25");
												}
												else {
													ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
													sharedVarWrites.add(writeEventEntry);
													writeShared.put(leftOp.toString(), sharedVarWrites);
													System.out.println("26");
												}
											}
											else {
												//local variable
												System.out.println(leftOp.toString());
												
												if (locRefCounter.get(leftOp.toString()) != null) {
													locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
													locVarType.put(leftOp.toString(), typeStr);
													System.out.println("28");
												}
												else {
													locRefCounter.put(leftOp.toString(), 1);
													locVarType.put(leftOp.toString(), typeStr);
													System.out.println("29");
												}
												symName = symName.concat(leftOp.toString());
												symName = symName.concat("_"+locRefCounter.get(leftOp.toString()).toString());
											}
											IntExpr intExpr = ctx.mkIntConst(symName);
											IntNum intNum = ctx.mkInt(intConst.toString());
	
											BoolExpr boolExpr = ctx.mkEq(intExpr, intNum);
											solver.add(boolExpr);
											System.out.println(intConst.toString());
										}
										else if (typeStr.equals("java.lang.Boolean")) {
											
										}
										else if (typeStr.equals("boolean")) {
											System.out.println("boolean");
											//boolean is represented as 32 bit int in soot
											if (rightOP instanceof IntConstant) {
												IntConstant intConst = (IntConstant)rightOP;
												
												if (writeRefCounter.get(leftOp.toString()) != null) {
													writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
													writeEvents.add(intConst.toString());

													symName = symName.concat("Write_");
													symName = symName.concat(leftOp.toString());
													symName = symName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());


													writeEvents.add(typeStr);
													writeEvents.add("Constant");
													event_no++;
													System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
														+", "+writeEvents.get(6));
													currThreadEvents.put(event_no, writeEvents);


													ArrayList<String> writeEventEntry = new ArrayList(2);
													writeEventEntry.add(tID);
													Integer intEvent =  event_no;
													writeEventEntry.add(intEvent.toString());
													if (writeShared.get(leftOp.toString()) == null) {
														ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
														sharedVarWrites.add(writeEventEntry);
														writeShared.put(leftOp.toString(), sharedVarWrites);
														System.out.println("30");
													}
													else {
														ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
														sharedVarWrites.add(writeEventEntry);
														writeShared.put(leftOp.toString(), sharedVarWrites);
														System.out.println("31");
													}
												}
												else {
													//local variable
													if (locRefCounter.get(leftOp.toString()) != null) {
														locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
														locVarType.put(leftOp.toString(), typeStr);
														System.out.println("32");
													}
													else {
														locRefCounter.put(leftOp.toString(), 1);
														locVarType.put(leftOp.toString(), typeStr);
														System.out.println("33");
													}
													symName = symName.concat(leftOp.toString());
													symName = symName.concat("_"+locRefCounter.get(leftOp.toString()).toString());
												}
												boolean boolVal = false;
												if (intConst.value == 1)
													boolVal = true;
												BoolExpr boolExpr = ctx.mkBoolConst(symName);
												BoolExpr boolNum = ctx.mkBool(boolVal);
												BoolExpr boolExpr1 = ctx.mkEq(boolExpr, boolNum);
												solver.add(boolExpr1);

											}								
										}
										else if (typeStr.equals("java.lang.Double")) {
											
										}
										else if (typeStr.equals("double")) {
											
										}
										else if (typeStr.equals("java.lang.Float")) {
											
										}
										else if (typeStr.equals("float")) {
											
										}
									}
									else {

									}
								}
								if (isConstant) {

								}
								else if (writeRefCounter.get(leftOp.toString()) != null) {
									//<tID, Write, var name , ref number, value, type, Constant/Variable>
									ArrayList<String> writeEvents = new ArrayList(7);
									String symName = new String(); //for z3

									writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
									writeEvents.add(tID);
									writeEvents.add("Write");
									writeEvents.add(leftOp.toString());
									writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
									readVal = new String();
									// readVal = readVal.concat("Read_");
									readVal = readVal.concat(rightOP.toString());
									readVal = readVal.concat("_");
									//error 
									System.out.println("Stmt is "+unit+" Left op is "+assign.getLeftOp().getType()+" Right op is "+assign.getRightOp().getType());
									readVal = readVal.concat(locRefCounter.get(rightOP.toString()).toString());


									symName = symName.concat("Write_");
									symName = symName.concat(leftOp.toString());
									symName = symName.concat("_"+writeRefCounter.get(leftOp.toString()).toString());

									writeEvents.add(readVal);
									writeEvents.add(typeStr);
									writeEvents.add("Variable");

									IntExpr intExpr1 = ctx.mkIntConst(symName);
									IntExpr intExpr2 = ctx.mkIntConst(readVal);
									BoolExpr boolExpr = ctx.mkEq(intExpr1 , intExpr2);
									event_no++;
									solver.add(boolExpr);
									System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
											writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
											+", "+writeEvents.get(6));
									currThreadEvents.put(event_no, writeEvents);


									System.out.println("Read value is : "+readVal+"Write value is : "+symName);
									ArrayList<String> writeEventEntry = new ArrayList(2);
									writeEventEntry.add(tID);
									Integer intEvent =  event_no;
									writeEventEntry.add(intEvent.toString());
									if (writeShared.get(leftOp.toString()) == null) {
										ArrayList<ArrayList<String>> sharedVarWrites = new ArrayList(1001);
										sharedVarWrites.add(writeEventEntry);
										writeShared.put(leftOp.toString(), sharedVarWrites);
										System.out.println("34");
									}
									else {
										ArrayList<ArrayList<String>> sharedVarWrites = writeShared.get(leftOp.toString());
										sharedVarWrites.add(writeEventEntry);
										writeShared.put(leftOp.toString(), sharedVarWrites);
										System.out.println("35");
									}

								}
								else {
									if (locRefCounter.get(leftOp.toString()) != null)
										locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
									else
										locRefCounter.put(leftOp.toString(), 1);
									String symName = new String(); //for z3
									readVal = new String();

									symName = symName.concat(leftOp.toString());
									symName = symName.concat("_"+locRefCounter.get(leftOp.toString()).toString());
									if (readRefCounter.get(rightOP.toString()) != null) {
										readVal = readVal.concat("Read_");
										readVal = readVal.concat(rightOP.toString());
										readVal = readVal.concat("_" + readRefCounter.get(rightOP.toString()));
										System.out.println("45");
									}
									else {
										readVal = readVal.concat(rightOP.toString());
										readVal = readVal.concat("_" + locRefCounter.get(rightOP.toString()));
										System.out.println("36");
									}

									IntExpr intExpr1 = ctx.mkIntConst(symName);
									IntExpr intExpr2 = ctx.mkIntConst(readVal);
									BoolExpr boolExpr = ctx.mkEq(intExpr1 , intExpr2);
									solver.add(boolExpr);

										//<tID, Write, var name , ref number, value, type, Constant/variable>
									// ArrayList<String> writeEvents = new ArrayList(7);

									// //saves the type at write
									// locVarType.put(leftOp.toString(), typeStr);
									// writeEvents.add(tID);
									// writeEvents.add("Write");
									// writeEvents.add(leftOp.toString());
									// writeEvents.add(locRefCounter.get(leftOp.toString()).toString());
									// readVal = new String();
									// //right operator is a global
									// if (readRefCounter.get(rightOP.toString()) != null) {
									// 	// readVal = readVal.concat("Read_");
									// 	readVal = readVal.concat(rightOP.toString());
									// 	readVal = readVal.concat("_" + readRefCounter.get(rightOP.toString()));
									// }
									// else {
									// 	// readVal = readVal.concat("Read_");
									// 	readVal = readVal.concat(rightOP.toString());
									// 	readVal = readVal.concat("_" + locRefCounter.get(rightOP.toString()));
									// }
									// writeEvents.add(readVal);
									// writeEvents.add(typeStr);
									// writeEvents.add("Variable");									
								}
							}
						}
					}
					else if (unit instanceof IfStmt) {

						IfStmt ifStmt = (IfStmt)unit;
						Value condition = ifStmt.getCondition(); 
						System.out.println(ifStmt.toString());
						System.out.println("Condition : "+ifStmt.getCondition());
						if (condition instanceof BinopExpr) {
							BinopExpr binopExpr = (BinopExpr)ifStmt.getCondition();
							Value op1 = binopExpr.getOp1();
							Value op2 = binopExpr.getOp2();
							//Path Constraints
							System.out.println("IfStmt");
							//by default branch is not taken
							boolean isBranchTaken = true;
							boolean isRightConstant = false;
							Integer nextBlockID = blockIDs.get(0);
							if (nextBlockID == (currBlockID + 1)) {
								//branch not taken
								isBranchTaken = false;
								System.out.println("Branch not taken");
							}
							else {
								System.out.println("Branch taken");		
							}
							if (op2 instanceof IntConstant) {
								System.out.println("out");
								isRightConstant = true;
							}

							//handle bool
							String loc_Sym_val = new String();
							loc_Sym_val = loc_Sym_val.concat(op1.toString());//right oparand
							loc_Sym_val = loc_Sym_val.concat("_"+locRefCounter.get(op1.toString()));
							System.out.println("Operator 1 value is : " + loc_Sym_val);
							IntExpr intExpr1 = ctx.mkIntConst(loc_Sym_val);
							IntExpr intExpr2 = null;
							IntNum intNum = null;
							if (isRightConstant) {
								IntConstant intConst = (IntConstant)op2;
								String intVal = intConst.toString();
								intNum = ctx.mkInt(intVal);
							}
							else {
								loc_Sym_val = new String();
								loc_Sym_val = loc_Sym_val.concat(op2.toString());//left operand
								loc_Sym_val = loc_Sym_val.concat("_"+locRefCounter.get(op2.toString()));
								intExpr2 = ctx.mkIntConst(loc_Sym_val);
							}
							if (locVarType.get(op1.toString()).equals("boolean")||locVarType.get(op1.toString()).equals("java.lang.Boolean")) {
								System.out.println("Have boolena path");
								BoolExpr boolExpr1 = ctx.mkBoolConst(loc_Sym_val);
								BoolExpr boolExpr2 = null;

								if (isRightConstant) {
									IntConstant intConst = (IntConstant)op2;
									boolean boolVal = false;

									if (intConst.toString().equals("1"))
										boolVal = true;
									boolExpr2 = ctx.mkBool(boolVal);
								}
								else {
									loc_Sym_val = new String();
									loc_Sym_val = loc_Sym_val.concat(op2.toString());//left operand
									loc_Sym_val = loc_Sym_val.concat("_"+locRefCounter.get(op2.toString()));
									boolExpr2 = ctx.mkBoolConst(loc_Sym_val);
								}
								if (binopExpr instanceof EqExpr) {
									if (isBranchTaken) {									
										// if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkEq(boolExpr1, boolExpr2);
											solver.add(boolExpr);
										// }
										// else {
										// 	BoolExpr boolExpr = ctx.mkEq(intExpr1, intExpr2);
										// 	solver.add(boolExpr);	
										// }
									}
									else {
										//flip the condition
										// if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkEq(boolExpr1, boolExpr2);
											boolExpr = ctx.mkNot(boolExpr);
											solver.add(boolExpr);
										// }
										// else {
										// 	BoolExpr boolExpr = ctx.mkEq(intExpr1, intExpr2);
										// 	boolExpr = ctx.mkNot(boolExpr);
										// 	solver.add(boolExpr);
										// }
									}
								}
								else if (binopExpr instanceof NeExpr) {
									if (isBranchTaken) {									
										// if (isRightConstant) {
										BoolExpr boolExpr = ctx.mkEq(boolExpr1, boolExpr2);
										boolExpr = ctx.mkNot(boolExpr);
										solver.add(boolExpr);
									}
									else {
										BoolExpr boolExpr = ctx.mkEq(boolExpr1, boolExpr2);
										solver.add(boolExpr);
									}
								}	
							}
							else {
								if (binopExpr instanceof EqExpr) {
									
									System.out.println("EqExpr");
									if (isBranchTaken) {									
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkEq(intExpr1, intNum);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkEq(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
									else {
										//flip the condition
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkEq(intExpr1, intNum);
											boolExpr = ctx.mkNot(boolExpr);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkEq(intExpr1, intExpr2);
											boolExpr = ctx.mkNot(boolExpr);
											solver.add(boolExpr);
										}
									}
								}
								else if (binopExpr instanceof GeExpr) {
									System.out.println("NeExpr");
									if (isBranchTaken) {									
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkGe(intExpr1, intNum);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkGe(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
									else {
										//flip the condition
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkLt(intExpr1, intNum);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkLt(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
								}
								else if (binopExpr instanceof GtExpr) {
									System.out.println("Greater than expression is : "+binopExpr.toString());
									if (isBranchTaken) {									
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkGt(intExpr1, intNum);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkGt(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
									else {
										//flip the condition
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkLe(intExpr1, intNum);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkLe(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
								}
								else if (binopExpr instanceof LeExpr) {
									if (isBranchTaken) {									
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkLe(intExpr1, intNum);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkLe(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
									else {
										//flip the condition
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkGt(intExpr1, intNum);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkGt(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
								}
								else if (binopExpr instanceof  LtExpr) {
									if (isBranchTaken) {									
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkLt(intExpr1, intNum);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkLt(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
									else {
										//flip the condition
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkGe(intExpr1, intNum);
											solver.add(boolExpr);
										}
										else {
											BoolExpr boolExpr = ctx.mkGe(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
								}
								else if (binopExpr instanceof NeExpr) {
									if (isBranchTaken) {	
										System.out.println(tID+"Branch taken : ");								
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkEq(intExpr1, intNum);
											boolExpr = ctx.mkNot(boolExpr);
											solver.add(boolExpr);
											System.out.println("Constant");
										}
										else {
											BoolExpr boolExpr = ctx.mkEq(intExpr1, intExpr2);
											boolExpr = ctx.mkNot(boolExpr);
											solver.add(boolExpr);	
										}
									}
									else {
										//flip the condition
										if (isRightConstant) {
											BoolExpr boolExpr = ctx.mkEq(intExpr1, intNum);
											solver.add(boolExpr);
											System.out.println("Constant");
										}
										else {
											BoolExpr boolExpr = ctx.mkEq(intExpr1, intExpr2);
											solver.add(boolExpr);	
										}
									}
								}
							}
						}
					}
				}
				if (blockIDs.isEmpty()) {
					continue;
				}
				else {
					functionCallStack.push(temp1);
					Integer blockID = blockIDs.remove(0);
					blockIDStack.push(blockIDs);
					ArrayList<Block> blockList = getBlocks(Scene.v().getMethod(temp1.get(1)));
					Iterator<Unit> stmtIt = blockList.get(blockID).iterator();
					unitItStack.push(stmtIt);
					currBlockIDStack.push(blockID);
				}
			}

			// }
			ArrayList<String> endEvent = new ArrayList(2);
			endEvent.add(tID);
			endEvent.add("End");
			event_no++;
			currThreadEvents.put(event_no, endEvent);
			System.out.println("O_"+tID+"_"+event_no+" "+endEvent.get(0)+", "+endEvent.get(1));
			trace.put(tID, currThreadEvents);
			eventCount.put(tID, (Integer)event_no);
			System.out.println("No of events in tID : "+tID+" "+event_no);
			//program order constraints
			for (Integer iii = 1; iii < event_no; iii++) {
				String eventOrderVariable = new String();

				eventOrderVariable = eventOrderVariable.concat("O_");
				eventOrderVariable = eventOrderVariable.concat(tID);
				eventOrderVariable = eventOrderVariable.concat("_"+iii.toString());

				IntExpr intExpr1 = ctx.mkIntConst(eventOrderVariable);
				eventOrderVariable = new String();
				eventOrderVariable = eventOrderVariable.concat("O_");
				eventOrderVariable = eventOrderVariable.concat(tID);
				iii++;
				eventOrderVariable = eventOrderVariable.concat("_"+ iii.toString());
				iii--;
				IntExpr intExpr2 = ctx.mkIntConst(eventOrderVariable);
				BoolExpr boolExpr = ctx.mkLt(intExpr1, intExpr2);
				solver.add(boolExpr);
			}
		}

		System.out.println("Local Ref counter : " + locRefCounter);
		Iterator<ArrayList<String>> joinEventIt = joinEvents.iterator();
		while (joinEventIt.hasNext()) {
			ArrayList<String> joinEntry = joinEventIt.next();
			System.out.println(joinEntry.get(0)+" "+joinEntry.get(1));
			ArrayList<String> joinEvent = trace.get(joinEntry.get(0)).get(Integer.parseInt((joinEntry.get(1))));
			System.out.println("Join event entry : "+ joinEvent.get(0)+" "+joinEvent.get(1));
			String parentTID = joinEvent.get(0);
			String childTID = joinEvent.get(2);
			String eventOrderVariable = new String();

			eventOrderVariable = eventOrderVariable.concat("O_");
			eventOrderVariable = eventOrderVariable.concat(parentTID);
			eventOrderVariable = eventOrderVariable.concat("_"+joinEntry.get(1));

			IntExpr intExpr1 = ctx.mkIntConst(eventOrderVariable);
			eventOrderVariable = new String();
			eventOrderVariable = eventOrderVariable.concat("O_");
			eventOrderVariable = eventOrderVariable.concat(childTID);
			eventOrderVariable = eventOrderVariable.concat("_"+eventCount.get(childTID));
			IntExpr intExpr2 = ctx.mkIntConst(eventOrderVariable);
			BoolExpr boolExpr = ctx.mkGt(intExpr1, intExpr2);
			solver.add(boolExpr);
		}
		

		Iterator<String> lockVarIt = lockUnlockPairsPerVariable.keySet().iterator();
		System.out.println("Lock Unlock pair : "+lockUnlockPairsPerVariable);
		while (lockVarIt.hasNext()) {
			String lockVar = lockVarIt.next();
			System.out.println(lockVar);

			Iterator<ArrayList<String>> lockUnLockPairIt = lockUnlockPairsPerVariable.get(lockVar).iterator();
			while (lockUnLockPairIt.hasNext()) {
				ArrayList<String> lockUnLockPair = lockUnLockPairIt.next();
				System.out.println("Lock Unlock pair : "+lockUnLockPair.get(0)+" "+lockUnLockPair.get(1)+" "+lockUnLockPair.get(2));
				Iterator<ArrayList<String>> lockUnLockPairItIn = lockUnlockPairsPerVariable.get(lockVar).iterator();

				while (lockUnLockPairItIn.hasNext()) {
					ArrayList<String> lockUnLockPairIn = lockUnLockPairItIn.next();
					if (!((lockUnLockPair.get(0) == lockUnLockPairIn.get(0))&&
						(lockUnLockPair.get(1) == lockUnLockPairIn.get(1))&&(lockUnLockPair.get(2) == lockUnLockPairIn.get(2)))) {
							System.out.println("Lock Unlock pair : "+lockUnLockPair.get(0)+" "+lockUnLockPair.get(1)+" "+lockUnLockPair.get(2));
							System.out.println("Lock Unlock pair : "+lockUnLockPairIn.get(0)+" "+lockUnLockPairIn.get(1)+" "+lockUnLockPairIn.get(2)+"\n");
							
							//order variables
							IntExpr lockEvent = ctx.mkIntConst("O_"+lockUnLockPair.get(0)+"_"+lockUnLockPair.get(1));
							IntExpr unLockEvent = ctx.mkIntConst("O_"+lockUnLockPair.get(0)+"_"+lockUnLockPair.get(2));
							IntExpr lockEvent1 = ctx.mkIntConst("O_"+lockUnLockPairIn.get(0)+"_"+lockUnLockPairIn.get(1));
							IntExpr unLockEvent1 = ctx.mkIntConst("O_"+lockUnLockPairIn.get(0)+"_"+lockUnLockPairIn.get(2));
							BoolExpr boolExpr1 = ctx.mkLt(unLockEvent, lockEvent1); 
							BoolExpr boolExpr2 = ctx.mkLt(unLockEvent1, lockEvent);
							BoolExpr boolExpr = ctx.mkOr(boolExpr1, boolExpr2);
							solver.add(boolExpr);
					}
				}
			}
		}
		
		System.out.println("Reads are : "+readShared);
		System.out.println("writes are : " + writeShared);
		//build read/write constraints
		Iterator<String> sharedVarIt = readShared.keySet().iterator();

		while (sharedVarIt.hasNext()) {
			String sharedVar = sharedVarIt.next();

			Iterator<ArrayList<String>> readSharedIt = readShared.get(sharedVar).iterator();
			while (readSharedIt.hasNext()) {
				ArrayList<String> readEntry = readSharedIt.next();
				Iterator<ArrayList<String>> writeSharedIt = writeShared.get(sharedVar).iterator();

				ArrayList<String> readEvent = trace.get(readEntry.get(0)).get(Integer.parseInt(readEntry.get(1)));
				IntExpr readVal = ctx.mkIntConst("Read_"+sharedVar+"_"+readEvent.get(3));
				// System.out.println("Read_"+sharedVar+"_"+readEvent.get(3));
				BoolExpr boolExprOuter = null;
				while (writeSharedIt.hasNext()) {
					ArrayList<String> writeEntry_i = writeSharedIt.next();

					Iterator<ArrayList<String>> writeSharedItIn = writeShared.get(sharedVar).iterator();
					// <tid, Read/Write, var name, ref number, type>
					//<tID, Write, var name , ref number, value, type, Constant/Variable>
					ArrayList<String> writeEvent_i = trace.get(writeEntry_i.get(0)).get(Integer.parseInt(writeEntry_i.get(1)));
					IntExpr writeVal_i = ctx.mkIntConst("Write_"+sharedVar+"_"+writeEvent_i.get(3));
					BoolExpr boolExpr = ctx.mkEq(readVal, writeVal_i);
					IntExpr readOrderVar = ctx.mkIntConst("O_"+readEntry.get(0)+"_"+readEntry.get(1));
					IntExpr writeOrderVar_i = ctx.mkIntConst("O_"+writeEntry_i.get(0)+"_"+writeEntry_i.get(1));
					boolExpr = ctx.mkAnd(boolExpr, ctx.mkLt(writeOrderVar_i, readOrderVar));
					// System.out.println("Read_"+sharedVar+"_"+readEvent.get(3)+"\n"+"Write_"+sharedVar+"_"+writeEvent_i.get(3));
					while (writeSharedItIn.hasNext()) {
					
						ArrayList<String> writeEntry_j = writeSharedItIn.next();

						if (!((writeEntry_i.get(0) == writeEntry_j.get(0))&&(writeEntry_i.get(1) == writeEntry_j.get(1)))) {
							System.out.println(readEntry);
							System.out.println(writeEntry_i);
							System.out.println(writeEntry_j+"\n");
							IntExpr writeOrderVar_j = ctx.mkIntConst("O_"+writeEntry_j.get(0)+"_"+writeEntry_j.get(1));
							BoolExpr boolExpr1 = ctx.mkLt(writeOrderVar_j, writeOrderVar_i);
							BoolExpr boolExpr2 = ctx.mkGt(writeOrderVar_j, readOrderVar);

							BoolExpr boolExprInner = ctx.mkOr(boolExpr1, boolExpr2);
							boolExpr = ctx.mkAnd(boolExpr, boolExprInner);
						}
					}
					if (boolExprOuter == null)
						boolExprOuter = boolExpr;
					else
						boolExprOuter = ctx.mkOr(boolExprOuter, boolExpr);
				}
				solver.add(boolExprOuter);
				Status stat = solver.check();
				int statInt = stat.toInt();
				if (statInt == 1)
					System.out.println("\n\n"+"[SATISFIABLE]"+"\n\n");
			}
		}
		System.out.println(readShared);
		System.out.println(writeShared);


		HashMap<Integer, ArrayList<ArrayList<String>>> globalOrder = new HashMap();
		int base = 0;
		Status stat = solver.check();
		int statInt = stat.toInt();
		int maxVal = -1000000;
		if (statInt == 1) {
			System.out.println("\n\n"+"[SATISFIABLE]"+"\n\n");
			Iterator<String> tIDIt = trace.keySet().iterator();
			Model model = solver.getModel();
		 	IntExpr val = (IntExpr)model.eval(ctx.mkIntConst("O_0_1"), true);
		 	String intVal = val.toString();
		 	System.out.println("base is : "+intVal);
			base = Integer.parseInt(intVal);
			while (tIDIt.hasNext()) {
				tID = tIDIt.next();

				int event_no = eventCount.get(tID);
				for (int iii = 1; iii <= event_no; iii++) {
					IntExpr orderVar = ctx.mkIntConst("O_"+tID+"_"+iii);

					model = solver.getModel();
				 	val = (IntExpr)model.eval(orderVar, true);
				 	intVal = val.toString();
				 	System.out.println("O_"+tID+"_"+iii+" "+intVal);
				 	if (globalOrder.get(Integer.parseInt(intVal) - base) == null) {
				 		ArrayList<ArrayList<String>>  traceEntriesperValue = new ArrayList(101);//trace entries per order variable;

				 		traceEntriesperValue.add(trace.get(tID).get(iii));
				 		globalOrder.put((Integer.parseInt(intVal) - base), traceEntriesperValue);
				 	}
				 	else {
				 		ArrayList<ArrayList<String>>  traceEntriesperValue = globalOrder.get(Integer.parseInt(intVal) - base);
				 		traceEntriesperValue.add(trace.get(tID).get(iii));
				 		globalOrder.put((Integer.parseInt(intVal) - base), traceEntriesperValue);
				 	}
				 	if (maxVal < ((Integer.parseInt(intVal) - base)))
				 		maxVal = Integer.parseInt(intVal) - base;
				}
			}
		}
		// // Model model = solver.getModel();
		// // IntExpr orderVar = ctx.mkIntConst("Read_<test1.Main: java.lang.Integer shared_int_a>_1");
	 // // 	IntExpr val = (IntExpr)model.eval(orderVar, true);
	 // // 	String intVal = val.toString();
		// System.out.println("Read_<test1.Main: java.lang.Integer shared_int_a>_1 "+intVal);
		// // model = solver.getModel();
		// // orderVar = ctx.mkIntConst("Read_<test1.Main: java.lang.Integer shared_int_a>_2");
	 // // 	val = (IntExpr)model.eval(orderVar, true);
	 // // 	intVal = val.toString();
		// System.out.println("Read_<test1.Main: java.lang.Integer shared_int_a>_2 "+intVal);
		// // model = solver.getModel();
		// // orderVar = ctx.mkIntConst("Read_<test1.Main: java.lang.Integer shared_int_a>_3");
	 // // 	val = (IntExpr)model.eval(orderVar, true);
	 // // 	intVal = val.toString();
		// System.out.println("Read_<test1.Main: java.lang.Integer shared_int_a>_3 "+intVal);



		// // model = solver.getModel();
		// // orderVar = ctx.mkIntConst("$i0_1");
	 // // 	val = (IntExpr)model.eval(orderVar, true);
	 // // 	intVal = val.toString();
		// System.out.println("$i0_1 "+intVal);
		// // model = solver.getModel();
		// // orderVar = ctx.mkIntConst("$i0_2");
	 // // 	val = (IntExpr)model.eval(orderVar, true);
	 // // 	intVal = val.toString();
		// System.out.println("$i0_2 "+intVal);
		// // model = solver.getModel();
		// // orderVar = ctx.mkIntConst("$i0_3");
	 // // 	val = (IntExpr)model.eval(orderVar, true);
	 // // 	intVal = val.toString();
		// System.out.println("$i0_3 "+intVal);

		System.out.println("maxVal : "+maxVal);
		String toPrint = new String();
		for (Integer iii = 0; iii <= maxVal; iii++) {
			if (globalOrder.get(iii) != null) {
				Iterator<ArrayList<String>> traceEntriesperValueIt = globalOrder.get(iii).iterator();

				while (traceEntriesperValueIt.hasNext()) {
					ArrayList<String> traceEntry = traceEntriesperValueIt.next();
					if (traceEntry != null) {
						if (traceEntry.get(1).equals("Begin")||traceEntry.get(1).equals("End")) {
							toPrint = toPrint.concat(traceEntry.get(0)+", "+traceEntry.get(1)+"\n");
						}
						else if (traceEntry.get(1).equals("Read")||traceEntry.get(1).equals("Write")) {
							toPrint = toPrint.concat(traceEntry.get(0)+", "+traceEntry.get(1)+", "+traceEntry.get(2)+"\n");
						}
						else if (traceEntry.get(1).equals("Lock")||traceEntry.get(1).equals("Unlock")) {
							toPrint = toPrint.concat(traceEntry.get(0)+", "+traceEntry.get(1)+", "+traceEntry.get(2)+"\n");
						}
						else if (traceEntry.get(1).equals("Fork")||traceEntry.get(1).equals("Join")) {
							toPrint = toPrint.concat(traceEntry.get(0)+", "+traceEntry.get(1)+", "+traceEntry.get(2)+"\n");
						}
						System.out.println("ls");
					}
				}
			}
		}

		System.out.println(toPrint);
		// synchronized(this) {
		// 	try {
	 //    		Files.write(Paths.get("Testcases/project-3/processed-output/"+testcase+".global_trace"), toPrint.getBytes(), StandardOpenOption.APPEND);
		// 	}catch (IOException e) {
	 //    		//exception handling left as an exercise for the reader
		// 		e.printStackTrace();
		// 	}
		// }
		try {
			String globalTraceOutPath = "Testcases/" + project + "/processed-output/" + testcase + ".global_trace";
			System.out.println(globalTraceOutPath);
			PrintWriter globalTraceWriter = new PrintWriter(globalTraceOutPath);
			globalTraceWriter.print(toPrint);
	      
			globalTraceWriter.close();
		}
		catch (IOException e) {

		}
		out.close();
		
	    return;
	}

}
	// Iterator<String> tIDIt = trace.keySet().iterator();
		// while (tIDIt.hasNext()) {
		// 	tID = tIDIt.next();
			// System.out.println("Thread ID is : "+tID);
		// 	HashMap<Integer, ArrayList<String>> threadEvents = trace.get(tID);
		// 	for (Integer event_no = 0; event_no <= eventCount.get(tID); event_no++) {
		// 		System.out.println(threadEvents.get(event_no));
		// 	}
		// }
		//build locking constraint
		// Iterator<String> lockVarIt = lockEntryVars.keySet().iterator();
		// while (lockVarIt.hasNext()) {
		// 	String lockVar = lockVarIt.next();

		// 	Iterator<ArrayList<String>> lockEntries = lockEntryVars.get(lockVar).iterator();//lock events per variable
		// 	while (lockEntries.hasNext()) {
		// 		ArrayList<String> lockEntry = lockEntries.next();

		// 		Iterator<ArrayList<String>> unLockEntries = unLockEntryVars.get(lockVar).iterator();
		// 		while (unLockEntries.hasNext()) {
		// 			ArrayList<String> unLockEntry = unLockEntries.next();

		// 			if (lockEntry.get(0) == unLockEntry.get(0)) {
		// 				System.out.println(lockEntry.get(0)+" "+unLockEntry.get(0));
		// 				System.out.println(lockEntry.get(1)+" "+unLockEntry.get(1)+"\n");
		// 				if (Integer.parseInt(lockEntry.get(1)) < Integer.parseInt(unLockEntry.get(1))) {

		// 					break;
		// 				}
		// 			}
		// 		}
		// 	}
		// }