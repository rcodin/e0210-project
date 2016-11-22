
package pop_replay;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
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

public class PoP_Replay_Instrumentor extends SceneTransformer
{
    
    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        Chain<SootClass> allClasses = Scene.v().getApplicationClasses();
        for (SootClass curClass: allClasses) {
        
            /* These classes must be skipped */
            if (curClass.getName().contains("pop_replay.PoP_Replay_Util")
             || curClass.getName().contains("popUtil.PoP_Util")) {
                continue;
            }
            // PoP_Replay_Util poUtil = new PoP_Replay_Util();
            List<SootMethod> allMethods = curClass.getMethods();
            for (SootMethod curMethod: allMethods) {   
                
            }  
        }  
    }
}
