package test2;

import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;
import java.lang.Thread;

/* Test - 2:
    Threads competing to enter into an 'if' block
    Includes lock, fork, join
    No symbolic writes
    Includes local variables and arithmetic operations
*/
public class Main {

	static Lock lock = new ReentrantLock();
	static Integer shared_int_a = 1;

	static class MyThread extends Thread {
		@Override
		public void run() {
			PoP_Util.randomDelay();

			lock.lock();
			int local_1 = shared_int_a + 5;
			int local_2 = local_1 * 5;
			int local_3 = local_2 % 10;
			if (local_3 == 0)
			/* Only one thread will be able to enter this */
			{
			    PoP_Util.registerEvent (1);
				shared_int_a = 2;
				System.err.println(Thread.currentThread().getName()+" Wrote shared_int_a");
			} else {
			    PoP_Util.registerEvent (2);
				System.err.println(Thread.currentThread().getName()+" Couldn't write shared_int_a");
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
