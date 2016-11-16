package test14;
import java.util.concurrent.locks.ReentrantLock;

import popUtil.PoP_Util;

import java.util.concurrent.locks.Lock;

/* Test - 14:
    Threads competing to enter into an 'if' block
    Includes lock, fork, join
    Includes symbolic writes
    Dynamic binding
*/
public class Main {

    static Lock lock = new ReentrantLock();
    static Integer shared_int_a = 1, shared_int_b = 1;
    
    static class ClassOne
    {
        public void fun()
        {
            PoP_Util.registerEvent (1);
            lock.lock();
            shared_int_a++;
            shared_int_b++;
            System.err.println(Thread.currentThread().getName()+" incremented shared_int_a and shared_int_b");
            lock.unlock();    
        }
    }
    
    static class ClassTwo extends ClassOne
    {
        @Override
        public void fun()
        {
            PoP_Util.registerEvent (2);
            lock.lock();
            if (shared_int_b % 2 == 0)
            {
                PoP_Util.registerEvent (3);
                shared_int_a *= 2;
                System.err.println(Thread.currentThread().getName()+" multiplied shared_int_a");
            }
            else
            {
                
                PoP_Util.registerEvent (4);
                shared_int_a ++;
                System.err.println(Thread.currentThread().getName()+" incremented shared_int_a");
            }
            lock.unlock();
        }
    }
    
    static class ClassThree extends ClassTwo
    {
        @Override
        public void fun()
        {
            PoP_Util.registerEvent (5);
            lock.lock();
            if (shared_int_b % 2 == 0)
            {
                PoP_Util.registerEvent (6);
                shared_int_a *= 2;
                System.err.println(Thread.currentThread().getName()+" multiplied shared_int_a");
            }
            else
            {
                
                PoP_Util.registerEvent (7);
                shared_int_a ++;
                System.err.println(Thread.currentThread().getName()+" incremented shared_int_a");
            }
            lock.unlock();
            
            
            lock.lock();
            if (shared_int_a % 2 == 0)
            {
                PoP_Util.registerEvent (8);
                shared_int_a *= 2;
                System.err.println(Thread.currentThread().getName()+" multiplied shared_int_a");
            }
            else
            {
                
                PoP_Util.registerEvent (9);
                shared_int_a ++;
                System.err.println(Thread.currentThread().getName()+" incremented shared_int_a");
            }
            lock.unlock();
        }
    }
    
    static class MyThread extends Thread
    {

        @Override
        public void run() 
        {
            ClassOne obj1 = new ClassOne();
            ClassOne obj2 = new ClassTwo();
            ClassOne obj3 = new ClassThree();
            
            PoP_Util.randomDelay();
            obj3.fun();
            PoP_Util.randomDelay();
            obj2.fun();
            PoP_Util.randomDelay();
            obj1.fun();
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
