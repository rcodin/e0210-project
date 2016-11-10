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
		// System.out.println(Scene.v().toString());
		HashMap<String, ArrayList<String>> statements = new HashMap();//the key is tid_methodName_noOfExecution_sta
		//order variable is O_tid_methodName_noOfExecution
		Stack<ArrayList<String>> functionCallStack = new Stack();//fucntion call stack(each entry tid, method name, no of invocation)
		Stack<ArrayList<Integer>> blockIDStack = new Stack();//each entry is a list of block IDs left to traverse in a function call
		Stack<Iterator<Unit>> unitItStack = new Stack();//each entry is iterator will go through Units 
		/*<tid,<event no, trace entry>>
		*/
		HashMap<String, HashMap<Integer, ArrayList<String>>> trace = new HashMap();
		
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
					sootField.getType().toString().equals("java.lang.Double") || sootField.getType().toString().equals("java.lang.Float")))
					continue;
				readRefCounter.put(sootField.toString(), 0);
				writeRefCounter.put(sootField.toString(), 0);
				System.out.println(sootField.toString()+" Type "+sootField.getType());
			}
		}


		// HashMap<String,HashMap<String,HashMap<Integer,ArrayList<Value>>>> localVals = new HashMap();
		// System.out.println(Scene.v().getMethod("<test14.Main: void <clinit>()>").getActiveBody());

		/*Local variable reference count
		<var name, curr count>
		saves the type of local variables
		*/
		HashMap<String, Integer> locRefCount = new HashMap();
		HashMap<String, String> locVarType = new HashMap();
		while(threadIt.hasNext()) {
			//<thread_objects, no of threads swawned before this>
			// Value temporary = null;
			HashMap<Value,Integer> threadObjs = new HashMap();
			HashMap<Value,Value> lockLocals = new HashMap();

			int no_of_thread_spawned = 0;
			int no_of_current_event = 0;

			tID = threadIt.next();//tID is a String 
			//differntiate between main and thread class
			if (trace.get(tID) == null) {

			}
			else {
				
			}
			int event_no = 0;
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
			blockIDStack.push(blockIDs);
			unitItStack.push(unitIt);

			//generic code will run using stack
			outloop:
			while (!functionCallStack.empty()) {
				ArrayList<String> temp1 = functionCallStack.pop();
				// System.out.println
				blockIDs = blockIDStack.pop();
				unitIt = unitItStack.pop();
				System.out.println(Scene.v().getMethod(temp1.get(1)).getActiveBody());
				while (unitIt.hasNext()) {
					Unit unit = unitIt.next();

					// System.out.println(unit.toString());
					if(unit instanceof InvokeStmt) {
						InvokeStmt invokeStmt = (InvokeStmt)unit;
						if (invokeStmt.toString().contains("PoP_Util")) {

						}
						else if (invokeStmt.toString().contains("void start()")) {
							ArrayList<String> forkConstraint = new ArrayList(3);
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();

							forkConstraint.add(tID);
							forkConstraint.add("Fork");
							String tmp = new String();
							// System.out.println("Invoke statememt method is : "+invExpr.getBase());
							tmp = tmp.concat(tID+"."+ String.valueOf(no_of_thread_spawned));
							threadObjs.put(invExpr.getBase(), no_of_thread_spawned);
							forkConstraint.add(tmp);
							// System.out.println(forkConstraint.get(0)+forkConstraint.get(1)+forkConstraint.get(2));
							no_of_thread_spawned++;
							no_of_current_event++;
						}
						else if (invokeStmt.toString().contains("void join()")) {
							ArrayList<String> joinConstraint = new ArrayList(3);
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();

							joinConstraint.add(tID);
							joinConstraint.add("Join");
							String tmp = new String();
							// System.out.println("Invoke statememt method is : "+invExpr.getBase());
							Integer threadNo = threadObjs.get(invExpr.getBase());
							tmp = tmp.concat(tID+"."+ String.valueOf(threadNo));
							joinConstraint.add(tmp);
							// System.out.println(joinConstraint.get(0)+joinConstraint.get(1)+joinConstraint.get(2));
							no_of_current_event++;
						}
						else if (invokeStmt.toString().contains("void lock()")) {
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();
							// temporary = invExpr.getBase();
							// System.out.println(invExpr.getBase());
							Value local = invExpr.getBase();
							if (lockLocals.get(local) != null) {
								ArrayList<String> lockConstraint = new ArrayList(3);
								lockConstraint.add(tID);
								lockConstraint.add("Lock");
								lockConstraint.add(lockLocals.get(local).toString());
							}
						}
						else if (invokeStmt.toString().contains("void unlock()")) {
							InstanceInvokeExpr invExpr = (InstanceInvokeExpr)invokeStmt.getInvokeExpr();
							// temporary = invExpr.getBase();
							// System.out.println(invExpr.getBase());
							Value local = invExpr.getBase();
							if (lockLocals.get(local) != null) {
								ArrayList<String> unLockConstraint = new ArrayList(3);
								unLockConstraint.add(tID);
								unLockConstraint.add("Unlock");
								unLockConstraint.add(lockLocals.get(local).toString());
							}
						}
						else if (invokeStmt.getInvokeExpr().getMethod().toString().startsWith("<java")) {
							// System.out.println("ssdsddddddddddddddddddddddddddddd and stack size is : "+ functionCallStack.size());
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
							if ((!unitIt.hasNext())&&blockIDs.isEmpty()) {
								Integer blockID = blockIDs.remove(0);
								ArrayList<Block> tempBlockList = getBlocks(Scene.v().getMethod(temp1.get(1)));//get blocks for current executing function
								Iterator<Unit> stmtIt = tempBlockList.get(blockID).iterator();
								blockIDStack.push(blockIDs);
								unitItStack.push(stmtIt);
							}
							else {
								blockIDStack.push(blockIDs);
								unitItStack.push(unitIt);	
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
						Value leftOp = assign.getLeftOp();
						Value rightOP = assign.getRightOp();
						if (rightOP.toString().contains("java.util.concurrent.locks.Lock")) {
							lockLocals.put(leftOp, rightOP);
						}
						System.out.println("Stmt is "+unit+" Left op is "+assign.getLeftOp().getType()+" Right op is "+assign.getRightOp().getType());
						if (assign.containsInvokeExpr()) {
							// System.out.println("The invoke expression is : "+assign.getInvokeExpr());
							InvokeExpr invokeExpr = assign.getInvokeExpr();

							SootMethod calledMethod = invokeExpr.getMethod();
							if (calledMethod.toString().startsWith("<java")) {
								continue;
							}
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
							if ((!unitIt.hasNext())&&blockIDs.isEmpty()) {
								Integer blockID = blockIDs.remove(0);
								ArrayList<Block> tempBlockList = getBlocks(Scene.v().getMethod(temp1.get(1)));//get blocks for current executing function
								Iterator<Unit> stmtIt = tempBlockList.get(blockID).iterator();
								blockIDStack.push(blockIDs);
								unitItStack.push(stmtIt);
							}
							else {
								blockIDStack.push(blockIDs);
								unitItStack.push(unitIt);	
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
							table.get(tID).get(calledMethod.getSignature()).
										put(i, getRemovedArrayElement());
							// ArrayList<Integer> ret =  getRemovedArrayElement();
							// System.out.println("return value of arraylist is : "+ ret.get(0));
							continue outloop;
						}
						else {
							String typeStr = leftOp.getType().toString();
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
									ArrayList<String> readConstraints = new ArrayList(5);
									readConstraints.add(tID);
									readConstraints.add("Read");
									readConstraints.add(readVal);
									readConstraints.add(readRefCounter.get(rightOP.toString()).toString());
									readConstraints.add(typeStr);
								}
								else {
									if (rightOP instanceof Constant) {
										isConstant = true;
										System.out.println("constant");
										//add directly to z3
										if (typeStr.equals("java.lang.Integer")) {
											
										}
										else if (typeStr.equals("int")) {
											
										}
										else if (typeStr.equals("java.lang.Boolean")) {
											
										}
										else if (typeStr.equals("boolean")) {
											
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
									writeRefCounter.put(rightOP.toString(), readRefCounter.get(rightOP.toString()) + 1);
									ArrayList<String> writeConstraints = new ArrayList(5);
									writeConstraints.add(tID);
									writeConstraints.add("Write");
									readVal = new String();
									readVal = readVal.concat("Read_");
									readVal = readVal.concat(rightOP.toString()));
									locRefCount.get(rightOP.toString()).toString()
									writeConstraints.add();
									writeConstraints.add(writeRefCounter.get(rightOP.toString()).toString());
									writeConstraints.add(typeStr);
								}
								else {

								}
							}
						}
					}
					else if (unit instanceof IfStmt) {
						// System.out.println("IfStmt");
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
				}
			}
			// }
		}
		Context ctx = new Context(new HashMap<String, String>());
		Solver solver = ctx.mkSolver();
		out.close();
		
	    return;
	}

}
