package test17;

/*
 * @author Sridhar Gopinath		-		g.sridhar53@gmail.com
 * 
 * Course project,
 * Principles of Programming Course, Fall - 2016,
 * Computer Science and Automation (CSA),
 * Indian Institute of Science (IISc),
 * Bangalore
 */

/*
 * Test 17: Exception handling
 */

import java.io.FileNotFoundException;
import java.io.PrintStream;

public class Main {

	public static void main(String[] args) {

		int a = args[0].length();

		try {
			PrintStream stream = new PrintStream(args[0]);
			stream.print("hello world");
			stream.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}

		System.err.println(a);

		return;
	}

}