 = new MyThread();
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
