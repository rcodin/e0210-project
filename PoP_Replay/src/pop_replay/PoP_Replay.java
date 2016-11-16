package pop_replay;

import java.util.ArrayList;
import soot.PackManager;
import soot.Scene;
import soot.Transform;

public class PoP_Replay 
{
    public static void main(String[] args) 
    {
        if (args.length < 2)
        {
            System.out.println("args[0] - project");
            System.out.println("args[1] - testcase ");
            return;
        }
        String project = args[0];
	    String testcase = args[1];
     
        ArrayList<String> base_args = new ArrayList<String>();

        // This is done so that SOOT can find java.lang.Object
        base_args.add("-prepend-classpath");

        base_args.add("-w");

        // Consider the Main Class as an application and not as a library
        base_args.add("-app");

        // Validate the Jimple IR at the end of the analysis
        base_args.add("-validate");

        // Exclude these classes and do not construct call graph for them
        base_args.add("-exclude");
        base_args.add("jdk.net");
        base_args.add("-exclude");
        base_args.add("java.lang");
        base_args.add("-exclude");
        base_args.add("jdk.internal.*"); 
        base_args.add("-no-bodies-for-excluded");

        // Retain variable names from the bytecode
        base_args.add("-p");
        base_args.add("jb");
        base_args.add("use-original-names:true");

        // Output the file as .class (Java Bytecode)
        base_args.add("-f");
        base_args.add("class");

        // Add the class path i.e. path to the JAR file
        base_args.add("-soot-class-path");
        base_args.add("Testcases/" + project + "/" + project + ".jar:PoP_Replay/build");

        // The Main class for the application
        base_args.add("-main-class");
        base_args.add(testcase + ".Main");

        // Class to analyze
        base_args.add(testcase + ".Main");

        base_args.add("-output-dir");
        base_args.add("./PoP_Replay/sootBin");
            
                
        Scene.v().addBasicClass("pop_replay.PoP_Replay_Util");
        PackManager.v().getPack("wjtp").add(new Transform("wjtp.PoP_Replay", new PoP_Replay_Instrumentor()));

        soot.Main.main(base_args.toArray(new String[base_args.size()]));

    }
}
