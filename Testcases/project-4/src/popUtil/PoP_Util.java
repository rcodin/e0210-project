package popUtil;

/* 
    Util class for auxillary methods    
*/

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Random;
import java.util.logging.Level;
import java.util.logging.Logger;

public class PoP_Util {

    private static final Object lock = new Object();
    private static final ArrayList<String> threadIDs = new ArrayList<String>();
    private static final ArrayList<Integer> forkCount = new ArrayList<Integer>();
    private static Random randGen = new Random();
    static final Integer MAX_THREADS = 100;
    private static PrintWriter pathLog = null;
    
    /* To flush the path log when the program exits */
    static class ShutDownThread extends Thread {
            @Override
            public void run() {
                pathLog.flush();
                pathLog.close();
            }
	}

    static {
        try {
            pathLog = new PrintWriter("pathLog");
            for (int i = 0; i < MAX_THREADS; i++)
            {
                threadIDs.add (null);
                forkCount.add (0);
            }
            threadIDs.set (1, "0");
            
            Runtime.getRuntime().addShutdownHook(new ShutDownThread());
        } catch (FileNotFoundException ex) {
            Logger.getLogger(PoP_Util.class.getName()).log(Level.SEVERE, null, ex);
            writeToLog("Error: Fatal");
            System.exit(-1);
        }
    }
 
    /* Write the given string to log */
    private static void writeToLog (String str) {
    
        pathLog.println(str);
        pathLog.flush();
    }
    
    /* Register the fork performed by current thread 
        Assign Tid the new thread  */
    public static void registerFork (Thread newThread) {
        
        synchronized (lock) {
        
            Long tid = Thread.currentThread().getId();
            assert (threadIDs.get(tid.intValue()) != null);
            String aTid = threadIDs.get(tid.intValue());
            Long newTid = newThread.getId();
            assert (newTid < MAX_THREADS);
            threadIDs.set (newTid.intValue(), aTid + "." + forkCount.get(tid.intValue()));
            forkCount.set (tid.intValue(), forkCount.get(tid.intValue()) + 1);
        }
    }
    
    /* Register event performed by current thread to path log */
    public static void registerEvent (Integer eventId) {
    
        synchronized (lock) {
        
            Long tid = Thread.currentThread().getId();
            assert (threadIDs.get(tid.intValue()) != null);
            String aTid = threadIDs.get(tid.intValue());
            writeToLog ("Thread "+aTid+" registered event "+eventId);
        }
    }
    
    
    /* Delay the calling thread for a random amount of time */
    public static void randomDelay(){
        randomDelay(100);
    }
    
    public static void randomDelay(int maxDelay) {

            try {
                    int delay = randGen.nextInt(maxDelay);
                    Thread.sleep(delay);
            } catch (Exception e) {
                    System.err.println("Exception in PoP_Util class. Please contact the TA");
            }
    }

}

