package test13;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 13:
    Threads competing to enter into an 'if' block
    Includes lock, fork, join
    Includes symbolic writes
    Multiple locks
    Recursion
*/
public class Main {

    static Lock lock1 = new ReentrantLock(), lock2 = new ReentrantLock();
    static Integer shared_int_a = 1, shared_int_b = 6;
    
    static class MyThread extends Thread
    {

        private void recurUpdate ()
        {   
            System.err.println(Thread.currentThread().getName()+" in recurUpdate()");
            PoP_Util.randomDelay();
            PoP_Util.registerEvent (2);
               
            int maxValAllowed = 0;
            lock2.lock();
            maxValAllowed = shared_int_b;
            lock2.unlock();
            
            int curVal = 0;
            lock1.lock();
            curVal = shared_int_a;
            lock1.unlock();
            
            
            PoP_Util.randomDelay();
            
            if (curVal <= maxValAllowed)
            {
                PoP_Util.registerEvent (3);
                
                lock1.lock();
                shared_int_a += 1;
                lock1.unlock();
                System.err.println(Thread.currentThread().getName()+" Incremented shared_int_a");
                
                recurUpdate();
            }
            else
            {
                System.err.println(Thread.currentThread().getName()+" couldn't incremented shared_int_a");
                PoP_Util.registerEvent (4);
            }
            
        }
        @Override
        public void run() 
        {
            recurUpdate();
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
