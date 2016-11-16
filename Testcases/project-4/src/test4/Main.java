package test4;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 4:
    Threads competing to enter into an 'if' block
    Includes lock, fork, join
    Includes symbolic writes
*/
public class Main {

    static Lock lock = new ReentrantLock();
    static Integer shared_int_a = 1;
    static class MyThread extends Thread
    {

        @Override
        public void run() 
        {
            PoP_Util.randomDelay();
            
            lock.lock(); 
            if(shared_int_a <= 2)
            /* Only two threads will be able to enter this */
            { 
                PoP_Util.registerEvent (1);
                System.err.println(Thread.currentThread().getName()+" Incremented shared_int_a");
                shared_int_a += 1; /* Need a symbolic write here */
            }
            else
            {
                PoP_Util.registerEvent (2);
                System.err.println(Thread.currentThread().getName()+" Couldn't increment shared_int_a");
            }
            lock.unlock(); 
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

        t1.join();
        t2.join();
        t3.join();
        
		return;
	}

}
