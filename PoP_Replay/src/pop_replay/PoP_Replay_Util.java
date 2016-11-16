package pop_replay;


import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.logging.Level;
import java.util.logging.Logger;

public class PoP_Replay_Util 
{
    static {
           
            /* The global_trace will be copied to the current directory before running the test case */
            BufferedReader br = new BufferedReader(new FileReader("global_trace"));
            
    }
    
  
    /* You can modify criticalBefore() to receive the required arguments */
    public static void criticalBefore () {
   
    }
    
    /* You can modify criticalAfter() to receive the required arguments */
    public static void criticalAfter () {
       
    }
       
}
