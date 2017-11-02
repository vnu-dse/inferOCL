/* Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */
package fr.inria.atlanmod.inferocl.gui.views;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

import fr.inria.atlanmod.inferocl.data.Snapshot;
import fr.inria.atlanmod.inferocl.gui.MainWindow;
import fr.inria.atlanmod.inferocl.gui.View;
import fr.inria.atlanmod.inferocl.gui.ViewManager;

/** 
 * A view for a snapshot
 * 
 * @author duc-hanh.dang
 */
@SuppressWarnings("serial")
public class SnapshotView extends JPanel implements View {    

	private ViewManager fViewManager; 
	private Snapshot fSnapshot;
	String title;
    
    JTextArea fInstances;
    
    JScrollPane fScrollInstances;    

    public SnapshotView(ViewManager parent, boolean isValidSnapshot, String title, String snapshotStr){
        super(new BorderLayout());
        fViewManager = parent;
        fSnapshot = new Snapshot(isValidSnapshot,snapshotStr);       
        //this.isValidSnapshot = fSnapshot.isValidSnapshot();
        this.title = title;
        // textbox to enter instances
        fInstances = new JTextArea();
        fInstances.setText(snapshotStr);
        fInstances.setEditable(true);
        fInstances.setLineWrap(true);
        fInstances.setWrapStyleWord(true);
        fInstances.setRows(7);
        fScrollInstances = new JScrollPane(fInstances);       
        
    
        // layout panel
        add(fScrollInstances, BorderLayout.NORTH);
        setSize(new Dimension(300, 300));        
    }
    
    public void setText(String st){
    	this.fInstances.setText(st);
    }
    
    public String getText(){
    	if(fInstances.getText() == null) return "";    	
    	return this.fInstances.getText().trim();
    }
    
    public boolean isValidSnapshot(){
    	return fSnapshot.isValidSnapshot();
    }
    
	@Override
	public void detachModel() {
		fViewManager.removeSnapshot(this);		
		fViewManager.getMainWindow().getLogPanel().setText("The " + title + " has been removed!");
	}    

}