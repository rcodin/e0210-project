package test9;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 9:
    Threads competing to enter into an 'if' block
    Includes lock, fork
    Symbolic writes
    
    Multiple methods
    
*/
public class Main {

    static Lock lock = new ReentrantLock();
    static Integer shared_int_a = 1;
    static void incrementShared ()
    {
        PoP_Util.randomDelay();
        
        lock.lock(); 
        if(shared_int_a <= 2)
        /* Only two threads will be able to enter this */
        { 
            PoP_Util.registerEvent (1);
            System.err.println(Thread.currentThread().getName()+" Wrote shared_int_a");
            shared_int_a ++;
        }
        else
        {
            PoP_Util.registerEvent (2);
            System.err.println(Thread.currentThread().getName()+" Couldn't write shared_int_a");
        }
        lock.unlock(); 
    }
    static class MyThread extends Thread
    {
        
        @Override
        public void run() 
        {
            incrementShared();
        }
    }

	public static void main(String[] args) throws InterruptedException {

		MyThread t1 = new MyThread();
        MyThread t2 = new MyThread();
        MyThread t3 = new MyThread();

        PoP_Util.registerFork(t1);
		t1.start();
		
		PoP_Util.registerFork(t2);
		t2.start();
		
		PoP_Util.registerFork(t3);
		t3.start();
		
        incrementShared();
        
		return;
	}

}
