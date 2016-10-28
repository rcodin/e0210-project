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

import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;

import soot.PackManager;
import soot.Transform;

public class TraceMaker {

	public static void main(String[] args) throws IOException {

		String project = args[0];
		String testcase = args[1];

		// Input args that were given to the testcase executable. 
		// These may be need during symbolic execution
		String argsFile = "Testcases/" + project + "/input/" + testcase;
		String testcaseArgs = new String(Files.readAllBytes(Paths.get(argsFile)));

        // The raw output from instrumented code. You'll use this to construct the tuple for each method call
		String inPath = "Testcases/" + project + "/output/" + testcase;

        // The output files for global trace and tuples. You'll output the results to these files
		String globalTraceOutPath = "Testcases/" + project + "/processed-output/" + testcase + "-global-trace";
		String tupleOutPath = "Testcases/" + project + "/processed-output/" + testcase + "-tuples";

		System.out.println("Processing " + testcase + " of " + project);

		// Read the contents of the output file into a string
		String in = new String(Files.readAllBytes(Paths.get(inPath)));

		/*
		//  * 
		//  * Write your algorithm which does the post-processing of the output
		//  * to construct the tuple for each method call
		//  * 
		//  */

		// // Call to the symbolic execution.
		// // You can pass any data that's required for symbolic execution
		// // Example: the tuples for each method call
		sootMainSymbolicExecution(project, testcase);

        
  //           You should have the intra-thread trace for each thread and the
  //           path constraints by now.
  //           Assign an order variable of the form O_i_j to the jth trace entry
  //           of the ith thread.
  //           Use the intra-thread traces to construct read-write constraints,
  //           locking constraints, program order constraints, must-happen-before
  //           constraints. These constraints will be in terms of the order 
  //           variables.
  //           Put all these constaints together into one big equation:
  //           All_constraints = (Read-write constraints) ^ (Path constraints) ^
  //               (Program order constraints) ^ (Must happen before constraints)
  //               ^ (Locking constraints)
            
        
        
  //       /* Solve the constraints using Z3 solver
  //          The solver will provide you a feasible assignment of order variables
  //          Using these values, construct your global trace 
  //          To construct the global trace, you just need to put the intra-thread
  //          trace entries in ascending order of their order variables.
  //       */

		// // Output the global trace 
		// PrintWriter globalTraceWriter = new PrintWriter(globalTraceOutPath);
		// globalTraceWriter.print();

		// globalTraceWriter.close();

		// // Output the tuples
		// PrintWriter tupleWriter = new PrintWriter(tupleOutPath);
		// tupleWriter.print();

		// tupleWriter.close();

		return;
	}

	public static void sootMainSymbolicExecution(String project, String testcase) {

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
		base_args.add("Testcases/" + project + "/" + project + ".jar");

		// The Main class for the application
		base_args.add("-main-class");
		base_args.add(testcase + ".Main");

		// Class to analyze
		base_args.add(testcase + ".Main");

		base_args.add("-output-dir");
		base_args.add("Testcases/" + project + "/sootBin/");

		SymbolicExecution obj = new SymbolicExecution(project, testcase);

		PackManager.v().getPack("wjtp").add(new Transform("wjtp.MyAnalysis", obj));

		soot.Main.main(base_args.toArray(new String[base_args.size()]));

	}

}
