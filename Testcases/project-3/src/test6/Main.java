package test6;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 6:
    Thread Fork Recursion
*/
public class Main {

    static Lock lock = new ReentrantLock();
    static Integer shared_int_a = 5; /* Total 5 forks are possible.  */
    static class MyThread extends Thread
    {
        @Override
        public void run() 
        {
            PoP_Util.randomDelay();
            
            Boolean forkNew = true;
            lock.lock(); 
            
            shared_int_a--;
            if(shared_int_a <= 0)
            { 
                PoP_Util.registerEvent (1);
                forkNew = false;    
            }
            lock.unlock(); 
            if (forkNew)
            {
                PoP_Util.registerEvent (2);
                MyThread t3 = new MyThread();
                System.err.println(Thread.currentThread().getName()+" Forked new thread");
                
                PoP_Util.registerFork(t3);
                t3.start();
                
            }
            else
            {
                PoP_Util.registerEvent (3);
                System.err.println(Thread.currentThread().getName()+" shared_int_a exhausted");
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
