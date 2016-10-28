package e0210;

/*
 * @author Sridhar Gopinath		-		g.sridhar53@gmail.com
 * 
 * Course project,
 * Principles of Programming Course, Fall - 2016,
 * Computer Science and Automation (CSA),
 * Indian Institute of Science (IISc),
 * Bangalore
 */

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

public class Analysis extends BodyTransformer {
	static SootClass instrumenterClass;
	static SootMethod getTIDaBID, setTID, setMethodCounter;
	static int inc = 0;
	static boolean isFileCreated = false;
	static {
		instrumenterClass = Scene.v().loadClassAndSupport("Instrumenter");
		getTIDaBID = instrumenterClass.getMethod("void getTIDaBID(java.lang.String,long,int)");
		setTID = instrumenterClass.getMethod("void setTID(java.lang.Thread)");
		setMethodCounter = instrumenterClass.getMethod("int setMethodCounter(java.lang.String)");
  	}
	// public void writer(String toprint){
	// 	try {

	// 		File postProcessFile = new File("src/e0210/process.txt");

	// 		// if file doesnt exists, then create it
	// 		postProcessFile.createNewFile();

	// 		} catch (IOException e) {
	// 			e.printStackTrace();
	// 		}
	// }
	@Override
	protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
		DirectedWeightedMultigraph<Block, DefaultWeightedEdge> graph = new DirectedWeightedMultigraph<>(DefaultWeightedEdge.class);
		DirectedWeightedMultigraph<Integer, DefaultWeightedEdge> intGraph = new DirectedWeightedMultigraph<>(DefaultWeightedEdge.class);		
		Block[] blockArray;
		PatchingChain<Unit> units= b.getUnits();
		TopologicalOrderIterator<Integer, DefaultWeightedEdge> topoIt;
		int base;
		// System.out.println(b.toString());
		ExceptionalBlockGraph bGraph = new ExceptionalBlockGraph(b);
		Iterator<Block> blockIt = bGraph.getBlocks().iterator();
		Iterator<DefaultWeightedEdge> edgeIt;
		int size = bGraph.size();
		int index = 0;
		
		Stack<Integer> stack = new Stack();
		HashMap<Integer, Integer> numPaths = new HashMap();
		LinkedList<ArrayList<Integer>> loop = new LinkedList();
		Local ballID = Jimple.v().newLocal("ballID", LongType.v());
		Local printRef, printLong;
		b.getLocals().add(ballID);
		AllDirectedPaths<Integer, DefaultWeightedEdge> paths = new AllDirectedPaths(intGraph);
		if (b.getMethod().getSignature().contains("Instrumenter"))
			return;
		if (b.getMethod().getSignature().contains("PoP_Util"))
			return;
		//Insert the block to make the unique thread ID
		Iterator unitIt = b.getUnits().snapshotIterator();
		Stmt stmt;

		Local methodeInvokeNumber = Jimple.v().newLocal("methodeInvokeNumber", IntType.v());//the number of time a method is called
		b.getLocals().add(methodeInvokeNumber);
		while (unitIt.hasNext()) {
			stmt = (Stmt)unitIt.next();
			InvokeExpr inv;
			InvokeStmt invStmt;
			if (stmt instanceof InvokeStmt) {
				inv = stmt.getInvokeExpr();
				if (inv instanceof VirtualInvokeExpr) {
					VirtualInvokeExpr vInv = (VirtualInvokeExpr)inv;
					if(stmt.toString().contains("void start()")) {
						Local tLoc = (Local)vInv.getBase();//thread local variable
						//  
						InvokeStmt setStmt = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(setTID.makeRef(),
						  tLoc));
						units.insertBefore(setStmt, stmt);
						// Local loc = ;
					}
				}
			}
		}
		synchronized(this) {
			inc = inc + 1000;
			base = inc;
			if (!isFileCreated) {
				try {
					Files.deleteIfExists(Paths.get("src/e0210/process.txt"));
					File postProcessFile = new File("src/e0210/process.txt");
					postProcessFile.createNewFile();
					Files.deleteIfExists(Paths.get("src/e0210/method.txt"));
					File methodFile = new File("src/e0210/method.txt");//Stores the method names
					methodFile.createNewFile();
				}catch (IOException e) {
					e.printStackTrace();
				}
			}
			isFileCreated = true;
		}
		
		// System.out.println(size);
		Integer entry = -1;
		Integer exit = size;


		for (index = -1; index <= size; index++) {
			intGraph.addVertex(index);
		}

		Iterator<Block> heads = bGraph.getHeads().iterator();
		while (heads.hasNext()) {
			Block head = heads.next();
			Integer id = head.getIndexInMethod();
			intGraph.addEdge(entry, id);
		}
		Iterator<Block> tails = bGraph.getTails().iterator();
		while (tails.hasNext()) {
			Block tail = tails.next();
			Integer id = tail.getIndexInMethod();
			intGraph.addEdge(id, exit);
		}
		Block temp;
		Integer source;
		Integer target;
		String blockStr;
		ArrayList<Block> exitBlocks = new ArrayList();
		blockArray = new Block[size];
		index = 0;
		while (blockIt.hasNext()) {
			Block block = blockIt.next();
			blockArray[index] = block;
			source = block.getIndexInMethod();
			Unit uExit;
			// intGraph.addVertex(source);
			blockStr = block.toString();
			if (blockStr.contains("exit")) {
				intGraph.addEdge(source, size);
				exitBlocks.add(block);
				// System.out.println(source+"is an exit node");
				index++;
				continue;
			}
			Iterator<Block> succIt = bGraph.getSuccsOf(block).iterator();
			while (succIt.hasNext()) {
				temp = succIt.next();
				target = temp.getIndexInMethod();
				// intGraph.addVertex(target);
				// System.out.println(source+"loop->"+target);
				if (source >= target) {
					ArrayList<Integer> loop_edge = new ArrayList();
					intGraph.addEdge(-1, target);
					intGraph.addEdge(source, size);
					loop_edge.add(0,source);
					loop_edge.add(1,target);
					loop.add(loop_edge);
				}
				else {
					intGraph.addEdge(source, target);
				}
				
			}
			index++;
			// System.out.println(block.toString());			
		}



		// System.out.println(b.toString());
		Integer node;//node in integer graph(of block IDs)
		topoIt = new TopologicalOrderIterator(intGraph);
		while (topoIt.hasNext()) {
			node = topoIt.next();
			stack.push(node);
			// System.out.println("Block ID of node in : " + node);
		}
		for (index = -1; index < (size + 1); index++) {
			numPaths.put(index,-1);
		}
		int stackSize = stack.size();
		for (index = 0; index < stackSize; index++) {
			Integer v = stack.pop();
			Integer w;
			// System.out.println(v.getIndexInMethod());
			DefaultWeightedEdge edge;
			if (intGraph.outDegreeOf(v) == 0) {
				numPaths.put(v, 1);
				// System.out.println(v);
			}
			else {
				numPaths.put(v, 0);
				edgeIt = intGraph.outgoingEdgesOf(v).iterator();
				while (edgeIt.hasNext()) {
					edge = edgeIt.next();
					w = intGraph.getEdgeTarget(edge);
					// if (numPaths.get(w) == null)
						// System.out.println("Null found in temp with Block ID " + temp.getIndexInMethod());
					int num = numPaths.get(v);
					intGraph.setEdgeWeight(edge, num);
					numPaths.put(v, numPaths.get(v) + numPaths.get(w));
					// System.out.println(v+"->"+w+"val : "+ num);
					// System.out.println(v +"->"+ w);
				}
				// System.out.println(v);
			}
		}
		blockIt = bGraph.getTails().iterator();
		int maxval = 0;//maximum val of any edge
		for (index = 0; index < size; index++) {
			int val;
			Unit endOfIn, startOfOut;
			Block in, out;//edges start Block and End block
			DefaultWeightedEdge edge;
			in = blockArray[index];
			if (intGraph.outDegreeOf(index) > 0) {
				edgeIt = intGraph.outgoingEdgesOf(index).iterator();
				while (edgeIt.hasNext()) {
					ArrayList<Unit> stmts = new ArrayList();
					edge = edgeIt.next();
					target = intGraph.getEdgeTarget(edge);
					if (target < size) {
						val = (int) intGraph.getEdgeWeight(edge);
						if (maxval < val)
							maxval = val;
						out = blockArray[target];
						//instrument here
						endOfIn = in.getTail();
						startOfOut = out.getHead();
						// InvokeExpr incExpr= Jimple.v().newStaticInvokeExpr(increaseCounter.makeRef(),
							// IntConstant.v(val));
						// Stmt incStmt = Jimple.v().newInvokeStmt(incExpr);
						// units.insertOnEdge(incStmt, endOfIn, startOfOut);
						// if (!isInitialized) {
							// isInitialized = true;
						// }
						// System.out.println(index+"------------------>"+target);
						stmts.add(Jimple.v().newAssignStmt(ballID,
                                 Jimple.v().newAddExpr(ballID, LongConstant.v(val))));
						try {
							units.insertOnEdge(stmts, endOfIn, startOfOut);
							// throw 5;
						}
						catch(Exception e)
						{

						}
					}
				}
			}
		}
		String methodSignature = b.getMethod().getSignature();
		while (blockIt.hasNext()) {
			// System.out.println(b.toString());
			SootClass javaIoPrintStream;
			javaIoPrintStream = Scene.v().getSootClass("java.io.PrintStream");
			Block tail;
			tail = blockIt.next();
			Unit end;
			end = tail.getTail();
			// printRef = Jimple.v().newLocal("printRef", RefType.v("java.io.PrintStream"));
			// b.getLocals().add(printRef);
			// printLong = Jimple.v().newLocal("printLong", LongType.v());
			// b.getLocals().add(printLong);
			// units.insertBefore(Jimple.v().newAssignStmt( 
			// printRef, Jimple.v().newStaticFieldRef( 
			// Scene.v().getField("<java.lang.System: java.io.PrintStream out>").makeRef())), end);

			// SootMethod toCall = javaIoPrintStream.getMethod("void println(long)");                    
			// units.insertBefore(Jimple.v().newInvokeStmt(
			// Jimple.v().newVirtualInvokeExpr(printRef, toCall.makeRef(), ballID)), end);
			
			InvokeStmt getStmt = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
				getTIDaBID.makeRef(), StringConstant.v(methodSignature),ballID, methodeInvokeNumber));
			units.insertBefore(getStmt, end);
			// System.out.println("should print");

		}
		//Handling loop
		ListIterator<ArrayList<Integer>> arrayIt = loop.listIterator();
		while (arrayIt.hasNext()) {
			DefaultWeightedEdge edge;
			Unit endOfSource, startOfTarget;
			ArrayList<Unit> stmts = new ArrayList();
			ArrayList<Integer> loop_edge = arrayIt.next();
			int val1, val2; //val1 is source to exit val and val2 is entry to target val

			edge = intGraph.getEdge(loop_edge.get(0), size);//size is exit node
			val1 = (int) intGraph.getEdgeWeight(edge);
			edge = intGraph.getEdge(-1, loop_edge.get(1));// is exit node
			val2 = (int) intGraph.getEdgeWeight(edge);

			stmts.add(Jimple.v().newAssignStmt(ballID,
                                 Jimple.v().newAddExpr(ballID, LongConstant.v(val1))));
			SootClass javaIoPrintStream;
			javaIoPrintStream = Scene.v().getSootClass("java.io.PrintStream");



			// printRef = Jimple.v().newLocal("printRef", RefType.v("java.io.PrintStream"));
			// b.getLocals().add(printRef);
			// printLong = Jimple.v().newLocal("printLong", LongType.v());
			// b.getLocals().add(printLong);
			// stmts.add(Jimple.v().newAssignStmt( 
			// printRef, Jimple.v().newStaticFieldRef( 
			// Scene.v().getField("<java.lang.System: java.io.PrintStream out>").makeRef())));
			// SootMethod toCall = javaIoPrintStream.getMethod("void println(long)");
			// stmts.add(Jimple.v().newInvokeStmt(
			// Jimple.v().newVirtualInvokeExpr(printRef, toCall.makeRef(), ballID)));
			stmts.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
				getTIDaBID.makeRef(), StringConstant.v(methodSignature), ballID, methodeInvokeNumber)));

			stmts.add(Jimple.v().newAssignStmt(ballID, 
											LongConstant.v(val2 + base)));

			// InvokeStmt getStmt = ;
			// units.insertBefore(getStmt, end);

			endOfSource = blockArray[loop_edge.get(0)].getTail();
			startOfTarget = blockArray[loop_edge.get(1)].getHead();
			// System.out.println(loop_edge.get(0)+"<<<<<<<>>>>>>>"+loop_edge.get(1));
			try {
				units.insertOnEdge(stmts, endOfSource, startOfTarget);

			}
			catch(Exception e)
			{

			}
			
			
		}
		//handling System.exit
		ListIterator<Block> exitIt = exitBlocks.listIterator();
		while (exitIt.hasNext()) {
			Block exitBlk = exitIt.next();
			SootClass javaIoPrintStream;
			javaIoPrintStream = Scene.v().getSootClass("java.io.PrintStream");
			Unit end = exitBlk.getHead();
			Iterator<Unit> lines = exitBlk.iterator();
			// Iterator lineIterator = b.getUnits().snapshotIterator();
			while(lines.hasNext()) {
				Stmt s = (Stmt) lines.next();
				end = s;
				if (!(s instanceof IdentityStmt)) {
					break;
				}
			}	
			// printRef = Jimple.v().newLocal("printRef", RefType.v("java.io.PrintStream"));
			// b.getLocals().add(printRef);
			// printLong = Jimple.v().newLocal("printLong", LongType.v());
			// b.getLocals().add(printLong);
			// units.insertBefore(Jimple.v().newAssignStmt( 
			// printRef, Jimple.v().newStaticFieldRef( 
			// Scene.v().getField("<java.lang.System: java.io.PrintStream out>").makeRef())), end);

			// SootMethod toCall = javaIoPrintStream.getMethod("void println(long)");                    
			// units.insertBefore(Jimple.v().newInvokeStmt(
			// Jimple.v().newVirtualInvokeExpr(printRef, toCall.makeRef(), ballID)), end);
			InvokeStmt getStmt = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(
				getTIDaBID.makeRef(), StringConstant.v(methodSignature),ballID, methodeInvokeNumber));
			units.insertBefore(getStmt, end);
			
		}


		Iterator lineIterator = b.getUnits().snapshotIterator();
		while(lineIterator.hasNext()) {
			Stmt s = (Stmt) lineIterator.next();
			if (!(s instanceof IdentityStmt)) {
				units.insertBefore(Jimple.v().newAssignStmt(methodeInvokeNumber, Jimple.v().newStaticInvokeExpr(
				setMethodCounter.makeRef(), StringConstant.v(methodSignature))),s);
				// System.out.println("damn");
				units.insertBefore(Jimple.v().newAssignStmt(ballID, 
											LongConstant.v(0L + base)),s);
				break;
			}
		}
		boolean boots = Boolean.FALSE;

		GraphPath<Integer,DefaultWeightedEdge> path;
		List<GraphPath<Integer,DefaultWeightedEdge>> allpaths;
		allpaths = paths.getAllPaths(-1, size, true, null);
		ListIterator<GraphPath<Integer,DefaultWeightedEdge>> listIt= allpaths.listIterator();

		HashMap<Integer, LinkedList<Integer>> blPaths = new HashMap();
		int maxPathWeight = 0;
		while (listIt.hasNext()) {
			LinkedList<Integer> vertices = new LinkedList();
			DefaultWeightedEdge edge;
			LinkedList<Integer> vertList = new LinkedList();
			int pathWeight;
			int vert;

			path = listIt.next();
			edgeIt = path.getEdgeList().iterator();
			pathWeight = (int)base;
			if (maxPathWeight < pathWeight)
				maxPathWeight = pathWeight;
			while (edgeIt.hasNext()) {
				edge = edgeIt.next();
				pathWeight += intGraph.getEdgeWeight(edge);
				// System.out.print("->"+intGraph.getEdgeWeight(edge)+"->");
				vert = intGraph.getEdgeTarget(edge);
				if ((vert < size) && (vert >= 0)){
					vertices.add(vert);
					// System.out.println(vert);
				}
				
			}
			// System.out.println(":::::::"+pathWeight + "is the Path Weight");
			blPaths.put(pathWeight, vertices);
			// System.out.println(pathWeight);
		}
		// System.out.println(blPaths.toString());
		String toPrint = new String();
		for (index = base; index < (blPaths.size()+base); index++) {
			LinkedList<Integer> vertices = new LinkedList();
			int vertex;
			Integer intClass = index;
			ListIterator<Integer> vertIt;

			toPrint =  toPrint.concat("\n");
			toPrint = toPrint.concat(" ");
			vertices = blPaths.get(index);
			// System.out.println(index+base);
			if (vertices == null)
				continue;
			// System.out.println(vertices.toString());
			// System.out.println(blPaths.toString());
			// System.out.println("llm");
			vertIt = vertices.listIterator();
			toPrint = toPrint.concat(intClass.toString());
			toPrint = toPrint.concat(" ");
			while (vertIt.hasNext()) {
				intClass = vertIt.next();
				toPrint = toPrint.concat((String)intClass.toString());
				toPrint = toPrint.concat(" ");
			}	
		}
		// System.out.println(b.getMethod().getSignature());
		String methodName = new String();
		methodName = methodName.concat(b.getMethod().getSignature());
		methodName = methodName.concat("^"+base+"\n");
		// System.out.println(methodName);
		toPrint = toPrint.concat("end");
		synchronized(this) {
			try {
	    		Files.write(Paths.get("src/e0210/process.txt"), toPrint.getBytes(), StandardOpenOption.APPEND);
	    		Files.write(Paths.get("src/e0210/method.txt"), methodName.getBytes(), StandardOpenOption.APPEND);
			}catch (IOException e) {
	    		//exception handling left as an exercise for the reader
				e.printStackTrace();
			}
		}
		System.out.println(b.toString());
		// System.out.println(bGraph.toString());
		// writer(toPrint);
		
		return;
	}
}

// System.out.println(intGraph.toString());
		// JNopStmt nopStmt1 = new JNopStmt();
		// JNopStmt nopStmt2 = new JNopStmt();
		// Block entry = new Block(nopStmt1, nopStmt1, b, size, 1, bGraph);
		// Block exit = new Block(nopStmt2, nopStmt2, b, size + 1, 1, bGraph);
		// graph.addVertex(entry);
		// graph.addVertex(exit);
		// System.out.println(size);
		// System.out.println(bGraph.size());
		// System.out.println(nopStmt1);
		// System.out.println(entry.getTail().toString());
		// System.out.println(exit.toString());
		//Adding the dummy head
		// Iterator<Block> heads = bGraph.getHeads().iterator();
		// while (heads.hasNext()) {
		// 	Block head = heads.next();
		// 	graph.addEdge(entry, head);
		// }
		// Iterator<Block> tails = bGraph.getTails().iterator();
		// while (tails.hasNext()) {
		// 	Block tail = tails.next();
		// 	graph.addEdge(tail, exit);
		// }




		// topoIt = new TopologicalOrderIterator(intGraph);
		// while (topoIt.hasNext()) {
		// 	temp = topoIt.next();
		// 	stack.push(temp);
		// }

		// int stackSize = stack.size();
		// for (index = 0; index < stackSize; index++) {
		// 	Block v = stack.pop();
		// 	// System.out.println(v.getIndexInMethod());
		// 	DefaultWeightedEdge edge;
		// 	if (graph.outDegreeOf(v) == 0) {
		// 		numPaths.put(v, 1);
		// 	}
		// 	else {
		// 		numPaths.put(v, 0);
		// 		edgeIt = graph.outgoingEdgesOf(v).iterator();
		// 		while (edgeIt.hasNext()) {
		// 			edge = edgeIt.next();
		// 			temp = (Block) graph.getEdgeTarget(edge);
		// 			// if (numPaths.get(temp) == null)
		// 				// System.out.println("Null found in temp with Block ID " + temp.getIndexInMethod());
		// 			int num = numPaths.get(v);
		// 			graph.setEdgeWeight(edge, num);
		// 			numPaths.put(v, numPaths.get(v) + numPaths.get(temp));
		// 		}
		// 	}
		// }
		// System.out.println(b.toString());