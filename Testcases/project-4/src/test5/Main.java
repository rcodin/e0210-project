package test5;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 5:
    Threads competing to enter into an 'if' block
    Includes fork, join
    symbolic writes 
    Without lock, so multiple threads can enter the 'if' block
*/
public class Main {

    static Integer shared_int_a = 1;
    static Integer shared_int_b = 10;
    static class MyThread extends Thread
    {
        @Override
        public void run() 
        {
            PoP_Util.randomDelay(10);
            if(shared_int_a == 1)
            /* Only one thread should be able to enter this, but as there are no locks, potentially all thread can */
            { 
                PoP_Util.registerEvent (1);
                System.err.println(Thread.currentThread().getName()+" Incremented shared_int_a");
                int local_int_a = shared_int_a*5 + shared_int_b;
                shared_int_a+=local_int_a;
            }
            else
            {
                PoP_Util.registerEvent (2);
                System.err.println(Thread.currentThread().getName()+" Coudldn't increment shared_int_a");
            }
            
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
        
        PoP_Util.randomDelay(5);
        
        if (shared_int_a == 1)
        {
            PoP_Util.registerEvent (3);
            System.err.println(Thread.currentThread().getName()+" didn't see any updates to shared_int_a");
        }
        else
        {
            PoP_Util.registerEvent (4);
            System.err.println(Thread.currentThread().getName()+" saw updates to shared_int_a");
        }
        t1.join();
        t2.join();
        t3.join();
        if(shared_int_a > 2)
        {
            PoP_Util.registerEvent (5);
            System.err.println(Thread.currentThread().getName()+" Multiple threads incremented the shared_int_a");
        }
        else
        {
            PoP_Util.registerEvent (6);
            System.err.println(Thread.currentThread().getName()+" Only single thread incremented the shared_int_a");
        }
        
		return;
	}

}
