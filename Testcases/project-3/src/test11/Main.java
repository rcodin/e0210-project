package test11;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 11:
    Threads competing to enter into an 'if' block
    Includes lock, fork, join
    Includes symbolic writes
    Command-line arguments
*/
public class Main {

    static Lock lock = new ReentrantLock();
    static Integer shared_int_a = 1, shared_int_b = 2;
    static class MyThread extends Thread
    {

        @Override
        public void run() 
        {
            while (true)
            {
                System.err.println(Thread.currentThread().getName()+" in new iteration");
                PoP_Util.registerEvent (1);
                PoP_Util.randomDelay();
            
                lock.lock(); 
                if(shared_int_a <= shared_int_b)
                { 
                    PoP_Util.registerEvent (2);
                    System.err.println(Thread.currentThread().getName()+" Incremented shared_int_a");
                    shared_int_a += 1; /* Need a symbolic write here */
                    lock.unlock(); 
                }
                else
                {
                    PoP_Util.registerEvent (3);
                    System.err.println(Thread.currentThread().getName()+" Couldn't increment shared_int_a");
                    lock.unlock(); 
                    break;
                }
                
            }
        }
    }

	public static void main(String[] args) throws InterruptedException {

		MyThread t1 = new MyThread();
        MyThread t2 = new MyThread();
        MyThread t3 = new MyThread();
        
        System.err.println("Command line args are "+args[0]+" "+args[1]);
        
        shared_int_a = Integer.parseInt (args[0]);
        shared_int_b = Integer.parseInt (args[1]) + shared_int_a;
        
        PoP_Util.registerFork(t1);
		t1.start();
		
		PoP_Util.registerFork(t2);
		t2.start();
		
		PoP_Util.registerFork(t3);
		t3.start();

        t1.join();
        t2.join();
        t3.join();
        
		return;
	}

}
