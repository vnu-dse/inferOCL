/*
 * Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */

package fr.inria.atlanmod.inferocl.main;

import fr.inria.atlanmod.inferocl.gui.MainWindow;

/**
 * The main application window of InferOCL. 
 * @author duc-hanh.dang 
 */

public class Main{
	public void attachShutDownHook(final MainWindow win){
		  Runtime.getRuntime().addShutdownHook(
				  new Thread() {
					  @Override
					  public void run() {
						  win.getControlPanel().disposeEngineProcess();
					  }
				  });
	}
	public static void main(String[] arg){
		Main main = new Main();
		final MainWindow win = new MainWindow();
		win.pack();
	    win.setVisible(true);	
	    main.attachShutDownHook(win);
	}

}