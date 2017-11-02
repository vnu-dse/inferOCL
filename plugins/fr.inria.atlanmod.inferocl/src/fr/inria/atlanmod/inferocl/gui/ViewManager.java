/*
 * Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */

package fr.inria.atlanmod.inferocl.gui;

import java.awt.BorderLayout;
import java.util.ArrayList;
import java.util.List;

import javax.swing.DefaultDesktopManager;
import javax.swing.JComponent;
import javax.swing.JDesktopPane;
import javax.swing.JInternalFrame;

import fr.inria.atlanmod.inferocl.data.Invariant;
import fr.inria.atlanmod.inferocl.gui.views.ExampleView;
import fr.inria.atlanmod.inferocl.gui.views.SnapshotView;

/* 
 * A DesktopManager that knows about ViewFrames.
 * 
 * @author duc-hanh.dang
 */

public class ViewManager extends DefaultDesktopManager {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private MainWindow fMainWindow;
    private List<SnapshotView> validSnapshots;
    private List<SnapshotView> invalidSnapshots;
    private ExampleView fExampleSnapshot;
    private int id4ValidSnapshot;
    private int id4InvalidSnapshot;
    private int fViewFrameX = 0;
    private int fViewFrameY = 0;
	private ViewFrame fExampleViewFrame;
    
	
    public ViewManager(MainWindow mainWindow) {		
    	fMainWindow = mainWindow;
    	validSnapshots = new ArrayList<SnapshotView>();
    	invalidSnapshots = new ArrayList<SnapshotView>();
    	id4ValidSnapshot = 0;
    	id4InvalidSnapshot = 0;
	}
    /**
     * Adds a new view (internal frame) to the desktop.
     */
	public void addNewViewFrame(ViewFrame f) {
        f.setBounds(fViewFrameX, fViewFrameY, 320, 200);
        getDesk().add(f, JDesktopPane.DEFAULT_LAYER);
        getDesk().moveToFront(f);
        // position for next frame
        if (fViewFrameX < 200) {
            fViewFrameX += 20;
            fViewFrameY += 20;
        } else {
            fViewFrameX = 0;
            fViewFrameY = 0;
        }

        f.setVisible(true);
    }
	/**
     * Closes the frame and notifies the view about it.
     */
    public void closeFrame(JInternalFrame f) {
        super.closeFrame(f);        
        ((ViewFrame) f).close();        
    }            
    /**
     * create a new valid snapshot 
     */
	public void createValidSnapshot(String snapshotStr) {
		id4ValidSnapshot++;
		String title = "Valid snapshot " + id4ValidSnapshot;
		SnapshotView snapshot = new SnapshotView(this, true, title, snapshotStr);		
		validSnapshots.add(snapshot);		
    	ViewFrame f = new ViewFrame(title, snapshot, "ObjectDiagram.gif");
        JComponent c = (JComponent) f.getContentPane();
        c.setLayout(new BorderLayout());
        c.add(snapshot, BorderLayout.CENTER);
        addNewViewFrame(f);
	}
	/**
     * create a new invalid snapshot 
     */
	public void createInvalidSnapshot(String snapshotStr) {
		id4InvalidSnapshot++;
		String title = "Invalid snapshot " + id4InvalidSnapshot;
		SnapshotView snapshot = new SnapshotView(this, false, title, snapshotStr);		
		invalidSnapshots.add(snapshot);		
    	ViewFrame f = new ViewFrame(title, snapshot, "ObjectDiagram.gif");
        JComponent c = (JComponent) f.getContentPane();
        c.setLayout(new BorderLayout());
        c.add(snapshot, BorderLayout.CENTER);
        addNewViewFrame(f);		
	}
	/**
     * create a generated snapshot 
     */
	public void createExampleSnapshot(String snapshotStr) {		
		String title = "Assuming this is a valid snapshot!";
		fExampleSnapshot = new ExampleView(this, snapshotStr);				
    	fExampleViewFrame = new ViewFrame(title, fExampleSnapshot, "ObjectDiagram.gif");
        JComponent c = (JComponent) fExampleViewFrame.getContentPane();
        c.setLayout(new BorderLayout());
        c.add(fExampleSnapshot, BorderLayout.CENTER);
        addNewViewFrame(fExampleViewFrame);
	}
	public void removeSnapshot(SnapshotView snapshot) {	
		if(snapshot.isValidSnapshot()){
			validSnapshots.remove(snapshot);
		}else{
			invalidSnapshots.remove(snapshot);
		}
	}
	public void removeExampleView() {
		fExampleSnapshot = null;		
	}
    /**
     * Closes all views.
     */
    void closeAllViews() {
        // How many frames do we have?
        JInternalFrame[] allframes = getDesk().getAllFrames();
        int count = allframes.length;
        //System.out.println("No frames = " + count);
        for (int i = 0; i < count; i++) {        	
            ViewFrame f = (ViewFrame) allframes[i];            
            getDesk().getDesktopManager().closeFrame(f);            
        }
        // reset start position for new frames
        fViewFrameX = 0;
        fViewFrameY = 0;        
    }
    private JDesktopPane getDesk(){
    	return this.fMainWindow.getDesk();
    }
    public MainWindow getMainWindow(){
    	return fMainWindow;
    }	
	public String getSnapshotInput() {
		StringBuilder ret = new StringBuilder();		
		ret.append("SOK = [");		
		StringBuilder tmp = new StringBuilder();
		for(SnapshotView s: this.validSnapshots){
			if(s.getText() != ""){
				tmp.append( "," + s.getText());	
			}			
		}
		if(this.validSnapshots.size() != 0){
			ret.append( tmp.toString().substring(1) );
		}
		ret.append("], SNOK = [");
		tmp = new StringBuilder();
		for(SnapshotView s: this.invalidSnapshots){
			if(s.getText() != ""){
				tmp.append( "," + s.getText());	
			}
		}		
		if(this.invalidSnapshots.size() != 0){
			ret.append( tmp.toString().substring(1) );
		}
		ret.append("]");
		return ret.toString();
	}
	public void hideExampleView() {		
		//fExampleViewFrame.setVisible(false);
		this.closeFrame(fExampleViewFrame);
	}	
}
