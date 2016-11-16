package test7;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 7:
    Threads modifying a variable in a loop without locks
    Includes fork, join
    Symbolic writes
*/
public class Main {

    static Integer shared_int_a = 1;
    static class MyThread extends Thread
    {
        @Override
        public void run() 
        {
            for (int i = 0; i < 3; i++)
            {
                PoP_Util.randomDelay();
                
                if (shared_int_a%3 == 1)
                {
                    PoP_Util.registerEvent (1 + 3*i);
                    System.err.println(Thread.currentThread().getName()+" Increment shared_int_a by 1");
                    shared_int_a += 1;
                }
                else
                {
                    PoP_Util.registerEvent (2 + 3*i);
                    System.err.println(Thread.currentThread().getName()+" Increment shared_int_a by 2");
                    shared_int_a += 2;
                }
            }
        }
    }

	public static void main(String[] args) throws InterruptedException {

		MyThread t1 = new MyThread();
        MyThread t2 = new MyThread();

        PoP_Util.registerFork(t1);
		t1.start();
		
		PoP_Util.registerFork(t2);
		t2.start();
		

        t1.join();
        t2.join();
        
		return;
	}

}
