package pop_replay;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.HashMap;

import soot.Body;
import soot.PatchingChain;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.NullConstant;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.VirtualInvokeExpr;
import soot.util.Chain;
import soot.Local;
import soot.jimple.InvokeExpr;
import soot.jimple.AssignStmt;
import soot.SootField;

public class PoP_Replay_Instrumentor extends SceneTransformer
{
	static SootClass poP_Replay_Util_Class;
	static SootMethod setTID, criticalBefore, criticalAfter;
	// static {
	// poP_Replay_Util_Class = Scene.v().loadClassAndSupport("PoP_Replay_Util");
	// getTIDaBID = instrumenterClass.getMethod("void getTIDaBID(java.lang.String,long,int)");
	// setTID =  poP_Replay_Util_Class.getMethod("void setTID(java.lang.Thread)");
	// setMethodCounter = instrumenterClass.getMethod("int setMethodCounter(java.lang.String)");
	// }
	@Override
	protected void internalTransform(String arg0, Map<String, String> arg1) {
		poP_Replay_Util_Class = Scene.v().loadClassAndSupport("pop_replay.PoP_Replay_Util");
		// getTIDaBID = instrumenterClass.getMethod("void getTIDaBID(java.lang.String,long,int)");
		setTID = poP_Replay_Util_Class.getMethod("void setTID(java.lang.Thread)");
		criticalBefore = poP_Replay_Util_Class.getMethod("void criticalBefore()");
		criticalAfter = poP_Replay_Util_Class.getMethod("void criticalAfter()");
		Chain<SootClass> allClasses = Scene.v().getApplicationClasses();
		HashMap<String, Integer> sharedVars = new HashMap();
		for (SootClass curClass: allClasses) {
			Iterator<SootField> fieldIt = curClass.getFields().iterator();
			while (fieldIt.hasNext()) {
				SootField sootField = fieldIt.next();
				if ((sootField.getType().toString().equals("java.lang.Integer"))) {
					sharedVars.put(sootField.toString(), 0);
					// System.out.println("Global var"+sootField.toString());
				} 
			}
			/* These classes must be skipped */
			if (curClass.getName().contains("pop_replay.PoP_Replay_Util")
			|| curClass.getName().contains("popUtil.PoP_Util")) {
				continue;
			}
			// System.out.println(curClass.toString());
			// PoP_Replay_Util poUtil = new PoP_Replay_Util();
			List<SootMethod> allMethods = curClass.getMethods();
			for (SootMethod curMethod: allMethods) {
				// System.out.println(curMethod.toString());
				if (curMethod.hasActiveBody()) {
					Body body = curMethod.getActiveBody();
					Iterator<Unit> unitIt = body.getUnits().snapshotIterator();
					PatchingChain<Unit> units= body.getUnits();

					while (unitIt.hasNext()) {
						Stmt stmt = (Stmt)unitIt.next();

						InvokeExpr inv;
						InvokeStmt invStmt;
						if (stmt instanceof InvokeStmt) {
							inv = stmt.getInvokeExpr();
							if (inv instanceof VirtualInvokeExpr) {
								VirtualInvokeExpr vInv = (VirtualInvokeExpr)inv;
								if(stmt.toString().contains("void start()")) {
									System.out.println("setting tiD");
									Local tLoc = (Local)vInv.getBase();//thread local variable  
									InvokeStmt setStmt = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(setTID.makeRef(), tLoc));
									units.insertBefore(setStmt, stmt);
									// System.out.println(stmt.toString()+" is instrumented for tid");
								}
							}
						}
						if (stmt.toString().contains("void start()")||stmt.toString().contains("void join()")||
							stmt.toString().contains("void lock()")||stmt.toString().contains("void unlock()")) {
							InvokeStmt criticalBeforeStmt = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(criticalBefore.makeRef()));
							units.insertBefore(criticalBeforeStmt, stmt);
							InvokeStmt criticalAfterStmt = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(criticalAfter.makeRef()));
							units.insertAfter(criticalAfterStmt, stmt);
							// System.out.println(stmt.toString()+" is instrumented");
						}
						else if (stmt instanceof AssignStmt) {
							AssignStmt assign  = (AssignStmt)stmt;
							String leftOp = assign.getLeftOp().toString();
							String rightOp = assign.getRightOp().toString();

							if ((sharedVars.get(leftOp) != null)||(sharedVars.get(rightOp) != null)) {
								InvokeStmt criticalBeforeStmt = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(criticalBefore.makeRef()));
								units.insertBefore(criticalBeforeStmt, stmt);
								InvokeStmt criticalAfterStmt = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(criticalAfter.makeRef()));
								units.insertAfter(criticalAfterStmt, stmt);
								// System.out.println(stmt.toString()+" is instrumented");
								continue;
							}
							// System.out.println(stmt.toString()+" is not instrumented");
						}
						else {
							// System.out.println(stmt.toString()+" is not instrumented");
						}
					}
				}
			}
		} 
	}
}
