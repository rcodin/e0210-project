package test15;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 15:
    Single path code
    Includes lock, fork
    No symbolic writes
*/
public class Main {

    static Integer shared_int_a = 1;
    static class MyThread extends Thread
    {

        @Override
        public void run() 
        {
            PoP_Util.registerEvent (1);
            shared_int_a = 1;
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

		return;
	}

}
