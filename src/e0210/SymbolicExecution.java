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


import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Model;

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

		HashMap<String, String>	config = new HashMap<String, String>();
		config.put("model", "true");
		Context ctx = new Context(config);
		Solver solver = ctx.mkSolver();

		
		// IntExpr intExpr = ctx.mkIntConst("a");
		// IntNum intNum = ctx.mkInt("5");
		// BoolExpr boolExpr = ctx.mkEq(intExpr, intNum);
		// solver.add(boolExpr);
		// solver.check();
		// Model model = solver.getModel();
	 	// IntExpr val = (IntExpr)model.eval(intExpr, true);
	 	// String intVal = val.toString();
	 	// System.out.println(intVal);
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
		// System.out.println(Scene.v().toString());
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
			// System.out.println(sootClass.toString());
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
				// System.out.println(sootField.toString()+" Type "+sootField.getType());
			}
		}


		// HashMap<String,HashMap<String,HashMap<Integer,ArrayList<Value>>>> localVals = new HashMap();
		// System.out.println(Scene.v().getMethod("<test14.Main: void <clinit>()>").getActiveBody());

		/*Local variable reference count
		<var name, curr count>
		saves the type of local variables at only write
		*/
		HashMap<String, Integer> locRefCounter = new HashMap();
		HashMap<String, String> locVarType = new HashMap();
		HashMap<String, HashMap<Integer, ArrayList<String>>> trace = new HashMap();
		HashMap<Integer,ArrayList<String>> currThreadEvents = new HashMap();
		while(threadIt.hasNext()) {
			tID = threadIt.next();
			Integer event_no = 0;
			
			ArrayList<String> beginEvent = new ArrayList(2);
			beginEvent.add(tID);
			beginEvent.add("Begin");
			event_no++;
			// System.out.println("Begin event : "+"O_"+tID+"_"+event_no+" "+beginEvent.get(0)+", "+beginEvent.get(1));
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
					// System.out.println(mainSign);
						break;
					}
				}
			}
			else {
				while(mainSigs.hasNext()) {
					String sigs = mainSigs.next();

					if(sigs.contains(" void run()")) {
						mainSign = sigs;
					// System.out.println(mainSign);
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
			
			//generic code will run using stack
			outloop:
			while (!functionCallStack.empty()) {
				ArrayList<String> temp1 = functionCallStack.pop();
				// System.out.println
				blockIDs = blockIDStack.pop();
				unitIt = unitItStack.pop();
				Integer currBlockID = currBlockIDStack.pop();
				// System.out.println(Scene.v().getMethod(temp1.get(1)).getActiveBody());
				while (unitIt.hasNext()) {
					Unit unit = unitIt.next();

					// System.out.println(unit.toString());
					if(unit instanceof InvokeStmt) {
						InvokeStmt invokeStmt = (InvokeStmt)unit;
						if (invokeStmt.toString().contains("PoP_Util")) {

						}
						else if (invokeStmt.toString().contains("void start()")) {
							ArrayList<String> forkEvent = new ArrayList(3);
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();

							forkEvent.add(tID);
							forkEvent.add("Fork");
							String tmp = new String();
							// System.out.println("Invoke statememt method is : "+invExpr.getBase());
							tmp = tmp.concat(tID+"."+ String.valueOf(no_of_thread_spawned));
							threadObjs.put(invExpr.getBase(), no_of_thread_spawned);
							forkEvent.add(tmp);
							// System.out.println(forkConstraint.get(0)+forkConstraint.get(1)+forkConstraint.get(2));
							no_of_thread_spawned++;
							event_no++;
							currThreadEvents.put(event_no, forkEvent);
							// System.out.println("Fork event : "+"O_"+tID+"_"+event_no+" "+forkEvent.get(0)+", "+forkEvent.get(1)+", "+forkEvent.get(2));
						}
						else if (invokeStmt.toString().contains("void join()")) {
							ArrayList<String> joinEvent = new ArrayList(3);
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();

							joinEvent.add(tID);
							joinEvent.add("Join");
							String tmp = new String();
							// System.out.println("Invoke statememt method is : "+invExpr.getBase());
							Integer threadNo = threadObjs.get(invExpr.getBase());
							tmp = tmp.concat(tID+"."+ String.valueOf(threadNo));
							joinEvent.add(tmp);
							event_no++;
							currThreadEvents.put(event_no, joinEvent);
							// System.out.println("Join event : "+"O_"+tID+"_"+event_no+" "+joinEvent.get(0)+", "+joinEvent.get(1)+", "+joinEvent.get(2));	
							// System.out.println(joinEvent.get(0)+joinEvent.get(1)+joinEvent.get(2));
						}
						else if (invokeStmt.toString().contains("void lock()")) {
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();
							// temporary = invExpr.getBase();
							// System.out.println(invExpr.getBase());
							Value local = invExpr.getBase();
							if (lockLocals.get(local) != null) {
								//<tid, Lock, Lock Object>
								ArrayList<String> lockEvents = new ArrayList(3);
								lockEvents.add(tID);
								lockEvents.add("Lock");
								lockEvents.add(lockLocals.get(local).toString());
								event_no++;
								currThreadEvents.put(event_no, lockEvents);
								// System.out.println("Lock event : "+"O_"+tID+"_"+event_no+" "+lockEvents.get(0)+", "+lockEvents.get(1)+", "+lockEvents.get(2));	
							}
						}
						else if (invokeStmt.toString().contains("void unlock()")) {
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();
							// temporary = invExpr.getBase();
							// System.out.println(invExpr.getBase());
							Value local = invExpr.getBase();
							if (lockLocals.get(local) != null) {
								ArrayList<String> unLockEvents = new ArrayList(3);
								unLockEvents.add(tID);
								unLockEvents.add("Unlock");
								unLockEvents.add(lockLocals.get(local).toString());
								event_no++;
								currThreadEvents.put(event_no, unLockEvents);
								// System.out.println("Unlock event : "+"O_"+tID+"_"+event_no+" "+unLockEvents.get(0)+", "+unLockEvents.get(1)+", "+unLockEvents.get(2));	
							}
						}
						else if (invokeStmt.getInvokeExpr().getMethod().toString().startsWith("<java")) {
							// System.out.println("ssdsddddddddddddddddddddddddddddd and stack size is : "+ functionCallStack.size());
							//Get the valueOf functions
							// System.out.println("Function name is : "+invokeStmt.getInvokeExpr().getMethod().toString());

						}
						else {

							//symbolic constraint generation
							SootMethod calledMethod = invokeStmt.getInvokeExpr().getMethod();
							
							// calledMethod
							int i = 0;
							while (true) {
								// System.out.println("fucke");
								//push necessary entries in the stack
								// System.out.println(calledMethod.toString()+" the value of i "+i);
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
										// System.out.println("fucked");
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
							// System.out.println("return value of arraylist is : "+ ret.get(0));
							continue outloop;
							// }
						}
					}
					else if (unit instanceof AssignStmt) {
						// System.out.println("AssignStmt");
						// java.lang.Integer, java.lang.Double, java.lang.Character, java.lang.Boolean, int, double, char and boolean.
						AssignStmt assign = (AssignStmt)unit;
						if (assign.toString().contains("PoP_Util")) {
							continue;
						}
						Value leftOp = assign.getLeftOp();
						Value rightOP = assign.getRightOp();
						String typeStr = leftOp.getType().toString();
						if (rightOP.toString().contains("java.util.concurrent.locks.Lock")) {
							lockLocals.put(leftOp, rightOP);
						}
						// System.out.println("Stmt is "+unit+" Left op is "+assign.getLeftOp().getType()+" Right op is "+assign.getRightOp().getType());
						if (assign.containsInvokeExpr()) {
							// System.out.println("The invoke expression is : "+assign.toString());
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
										if (invokeExpr.getArg(0) instanceof IntConstant) {	
											IntConstant intConst = (IntConstant)invokeExpr.getArg(0);
											// System.out.println(assign.toString()+invokeExpr.getArg(0));
											int value = intConst.value;

											if (writeRefCounter.get(leftOp.toString()) != null) {
												writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
												writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
												Integer temp = (Integer)value;
												writeEvents.add(temp.toString());
												writeEvents.add("java.lang.Integer");
												writeEvents.add("Constant");
												event_no++;
												currThreadEvents.put(event_no, writeEvents);
												// System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
															// writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
															// +", "+writeEvents.get(6));
											}
											//put it directly in z3
											else if (locRefCounter.get(leftOp.toString()) != null)
												locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
											else
												locRefCounter.put(leftOp.toString(), 1);
											locVarType.put(leftOp.toString(), typeStr);
										}
										else {
											String arg = invokeExpr.getArg(0).toString();

											if (readRefCounter.get(arg) != null) {//argument is a global variable
												
											}
											else if (locRefCounter.get(arg) != null) {
												if (writeRefCounter.get(leftOp.toString()) != null) {
													writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
													writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
													String readVal = new String();
													readVal = readVal.concat("Read_");
													readVal = readVal.concat(arg);
													readVal = readVal.concat("_"+locRefCounter.get(arg));
													// writeEvents.add(temp.toString());
													writeEvents.add("java.lang.Integer");
													writeEvents.add("Variable");
													event_no++;
													currThreadEvents.put(event_no, writeEvents);
												// System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
															// writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
															// +", "+writeEvents.get(6));
												}
												//put it directly in z3
												else if (locRefCounter.get(leftOp.toString()) != null)
													locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
												else
													locRefCounter.put(leftOp.toString(), 1);
												locVarType.put(leftOp.toString(), typeStr);
											}
											else {
												//this case is not possible because there should be write before a read
											}
										}
									}			
								}
								else if (typeStr.equals("int")) {
									// System.out.println(assign);
									if (calledMethod.toString().contains("<java.lang.Integer: int intValue()>")) {
										InstanceInvokeExpr instInvokeExpr = (InstanceInvokeExpr)assign.getInvokeExpr();
										Value calledObj = instInvokeExpr.getBase();
										if (writeRefCounter.get(leftOp.toString()) != null) {
											writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
											writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
											String readVal = new String();
											readVal = readVal.concat("Read_");
											readVal = readVal.concat(calledObj.toString());
											readVal = readVal.concat("_"+locRefCounter.get(calledObj.toString()));
											// writeEvents.add(temp.toString());
											writeEvents.add("int");
											writeEvents.add("Variable");
											event_no++;
											currThreadEvents.put(event_no, writeEvents);
											// System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														// writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
														// +", "+writeEvents.get(6));
										}
										else if (locRefCounter.get(leftOp.toString()) != null)
											locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
										else
											locRefCounter.put(leftOp.toString(), 1);
										locVarType.put(leftOp.toString(), typeStr);
									}
								}
								else if (typeStr.equals("java.lang.Boolean")) {
									if (calledMethod.toString().contains("<java.lang.Boolean: java.lang.Boolean valueOf(boolean)>")) {
										IntConstant intConst = (IntConstant)invokeExpr.getArg(0);
										// System.out.println(assign.toString()+invokeExpr.getArg(0));
										int value = intConst.value;

										if (writeRefCounter.get(leftOp.toString()) != null) {
											writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
											writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
											Integer temp = (Integer)value;
											writeEvents.add(temp.toString());
											writeEvents.add("java.lang.Boolean");
											writeEvents.add("Constant");
											event_no++;
											currThreadEvents.put(event_no, writeEvents);
											// System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														// writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
														// +", "+writeEvents.get(6));
										}
										else if (locRefCounter.get(leftOp.toString()) != null)
											locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
										else
											locRefCounter.put(leftOp.toString(), 1);
										locVarType.put(leftOp.toString(), typeStr);
									}
								}
								else if (typeStr.equals("boolean")) {
									InstanceInvokeExpr instInvokeExpr = (InstanceInvokeExpr)assign.getInvokeExpr();
									Value calledObj = instInvokeExpr.getBase();
									// System.out.println(calledObj);

									if (calledMethod.toString().contains("<java.lang.Boolean: boolean booleanValue()>")) {
										if (writeRefCounter.get(leftOp.toString()) != null) {
											writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
											writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
											String readVal = new String();
											readVal = readVal.concat("Read_");
											readVal = readVal.concat(calledObj.toString());
											readVal = readVal.concat("_"+locRefCounter.get(calledObj.toString()));
											// writeEvents.add(temp.toString());
											writeEvents.add("int");
											writeEvents.add("Variable");
											event_no++;
											currThreadEvents.put(event_no, writeEvents);
											// System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														// writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
														// +", "+writeEvents.get(6));
										}
										else if (locRefCounter.get(leftOp.toString()) != null)
											locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
										else
											locRefCounter.put(leftOp.toString(), 1);
										locVarType.put(leftOp.toString(), typeStr);
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
								// System.out.println("fucke");
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
										// System.out.println("fucked");
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
							// ArrayList<Integer> ret =  getRemovedArrayElement();
							// System.out.println("return value of arraylist is : "+ ret.get(0));
							continue outloop;
						}
						else {
							boolean isConstant = false;//flag to specify there is concrete value present in the write side or not
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
									// System.out.println("O_"+tID+"_"+event_no+" "+readEvent.get(0)+", "+readEvent.get(1)+", "+readEvent.get(2)+", "+readEvent.get(3)+", "+readEvent.get(4));
								}
								else {
									if (rightOP instanceof Constant) {
										//<tID, Write, var name , ref number, value, type, Constant/Variable>
										ArrayList<String> writeEvents = new ArrayList(7);
										
										writeEvents.add(tID);
										writeEvents.add("Write");
										writeEvents.add(leftOp.toString());
										isConstant = true;
										// System.out.println("constant");
										//add directly to z3
										if (typeStr.equals("java.lang.Integer")) {
											if (writeRefCounter.get(leftOp.toString()) != null) {
												// writeEvents.add(3, );
											}
										}
										else if (typeStr.equals("int")) {
											IntConstant intConst = (IntConstant)rightOP; 
											if (writeRefCounter.get(leftOp.toString()) != null) {
												writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
												writeEvents.add(intConst.toString());
												writeEvents.add(typeStr);
												writeEvents.add("Constant");
												event_no++;
												// System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
													// writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
													// +", "+writeEvents.get(6));
											}
											else {
												//local variable
												// System.out.println(leftOp.toString());
												
												if (locRefCounter.get(leftOp.toString()) != null) {
													locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
													locVarType.put(leftOp.toString(), typeStr);
												}
												else {
													locRefCounter.put(leftOp.toString(), 1);
													locVarType.put(leftOp.toString(), typeStr);
												}
											}
											// System.out.println(intConst.toString());
										}
										else if (typeStr.equals("java.lang.Boolean")) {
											
										}
										else if (typeStr.equals("boolean")) {
											// System.out.println("boolean");
											//boolean is represented as 32 bit int in soot
											if (rightOP instanceof IntConstant) {
												IntConstant intConst = (IntConstant)rightOP;
												
												if (writeRefCounter.get(leftOp.toString()) != null) {
													writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
													writeEvents.add(intConst.toString());
													writeEvents.add(typeStr);
													writeEvents.add("Constant");
													event_no++;
													// System.out.println("O_"+tID+"_"+event_no+" "+writeEvents.get(0)+", "+writeEvents.get(1)+", "+
														// writeEvents.get(2)+", "+writeEvents.get(3)+", "+writeEvents.get(4)+", "+writeEvents.get(5)
														// +", "+writeEvents.get(6));
												}
												else {
													//local variable
													if (locRefCounter.get(leftOp.toString()) != null) {
														locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
														locVarType.put(leftOp.toString(), typeStr);
													}
													else {
														locRefCounter.put(leftOp.toString(), 1);
														locVarType.put(leftOp.toString(), typeStr);
													}
												}
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

									writeRefCounter.put(leftOp.toString(), writeRefCounter.get(leftOp.toString()) + 1);
									writeEvents.add(tID);
									writeEvents.add("Write");
									writeEvents.add(leftOp.toString());
									writeEvents.add(writeRefCounter.get(leftOp.toString()).toString());
									readVal = new String();
									readVal = readVal.concat("Read_");
									readVal = readVal.concat(rightOP.toString());
									readVal = readVal.concat("_");
									//error 
									// System.out.println("Stmt is "+unit+" Left op is "+assign.getLeftOp().getType()+" Right op is "+assign.getRightOp().getType());
									readVal = readVal.concat(locRefCounter.get(rightOP.toString()).toString());
									writeEvents.add(readVal);
									writeEvents.add(typeStr);
									writeEvents.add("Variable");
								}
								else {
									if (locRefCounter.get(leftOp.toString()) != null) {
										locRefCounter.put(leftOp.toString(), locRefCounter.get(leftOp.toString()) + 1);
									}
									else {
										locRefCounter.put(leftOp.toString(), 1);
									}
										//<tID, Write, var name , ref number, value, type, Constant/variable>
									ArrayList<String> writeEvents = new ArrayList(7);

									//saves the type at write
									locVarType.put(leftOp.toString(), typeStr);
									writeEvents.add(tID);
									writeEvents.add("Write");
									writeEvents.add(leftOp.toString());
									writeEvents.add(locRefCounter.get(leftOp.toString()).toString());
									readVal = new String();
									//right operator is a global
									if (readRefCounter.get(rightOP.toString()) != null) {
										readVal = readVal.concat("Read_");
										readVal = readVal.concat(rightOP.toString());
										readVal = readVal.concat("_" + readRefCounter.get(rightOP.toString()));
									}
									else {
										readVal = readVal.concat("Read_");
										readVal = readVal.concat(rightOP.toString());
										readVal = readVal.concat("_" + locRefCounter.get(rightOP.toString()));
									}
									writeEvents.add(readVal);
									writeEvents.add(typeStr);
									writeEvents.add("Variable");									
								}
							}
						}
					}
					else if (unit instanceof IfStmt) {

						IfStmt ifStmt = (IfStmt)unit;
						Value condition = ifStmt.getCondition(); 
						// System.out.println(ifStmt.toString());
						System.out.println("Condition : "+ifStmt.getCondition());
						if (condition instanceof BinopExpr) {
							BinopExpr binopExpr = (BinopExpr)ifStmt.getCondition();
							Value op1 = binopExpr.getOp1();
							Value op2 = binopExpr.getOp2();
							//Path Constraints
							// System.out.println("IfStmt");
							//by default branch is not taken
							boolean isBranchTaken = true;
							boolean isRightConstant = false;
							Integer nextBlockID = blockIDs.get(0);
							if (nextBlockID == (currBlockID + 1)) {
								//branch not taken
								isBranchTaken = false;
								// System.out.println("Branch not taken");
							}
							else {
								// System.out.println("Branch taken");		
							}
							if (op2 instanceof IntConstant) {
								// System.out.println("out");
								isRightConstant = true;
							}


							String loc_Sym_val = new String();
							loc_Sym_val = loc_Sym_val.concat(op1.toString());//right oparand
							loc_Sym_val = loc_Sym_val.concat("_"+locRefCounter.get(op1.toString()));
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

							if (binopExpr instanceof EqExpr) {
								
								// System.out.println("EqExpr");
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
								// System.out.println("NeExpr");
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
								else {
									//flip the condition
									if (isRightConstant) {
										BoolExpr boolExpr = ctx.mkEq(intExpr1, intNum);
										solver.add(boolExpr);
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
		}
		out.close();
		
	    return;
	}

}
