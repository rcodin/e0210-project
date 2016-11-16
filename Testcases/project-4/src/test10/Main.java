package test10;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 10:
    Threads competing to enter an 'if' block
    Includes lock, fork, join
    Symbolic writes
    
    Multiple methods
    A method also take arguments and return a value
    Lock and unlock in different methods
    
*/
public class Main {

    static Lock lock = new ReentrantLock();
    static Integer shared_int_a = 1;
    static Integer shared_int_b = 2;
    static void incrementShared (int incrementCount)
    {
        
        if(shared_int_a <= 2)
        /* Only two threads will be able to enter this */
        { 
            PoP_Util.registerEvent (1);
            System.err.println(Thread.currentThread().getName()+" Wrote shared_int_a and shared_int_b");
            shared_int_a += 1;
            shared_int_b += incrementCount;
        }
        else
        {
            PoP_Util.registerEvent (2);
            System.err.println(Thread.currentThread().getName()+" Couldn't write shared_int_a");
        }
        lock.unlock(); 
    }
    static Integer getIncrementCount (int a)
    {
        return a*2 + 10;
    }
    static class MyThread extends Thread
    {
        
        @Override
        public void run() 
        {
            PoP_Util.randomDelay();
            
            lock.lock(); 
            int local_int_a = shared_int_b + 4;
            incrementShared(getIncrementCount(local_int_a));
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

        t2.join();
        PoP_Util.randomDelay();
        lock.lock();
        incrementShared(getIncrementCount(5));
        
		return;
	}

}
