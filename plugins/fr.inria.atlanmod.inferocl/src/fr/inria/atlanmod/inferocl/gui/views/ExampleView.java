/* Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */
package fr.inria.atlanmod.inferocl.gui.views;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.List;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

import fr.inria.atlanmod.inferocl.data.Invariant;
import fr.inria.atlanmod.inferocl.gui.ControlPanel;
import fr.inria.atlanmod.inferocl.gui.View;
import fr.inria.atlanmod.inferocl.gui.ViewManager;

/** 
 * A view for a generated snapshot
 * 
 * @author duc-hanh.dang
 */
@SuppressWarnings("serial")
public class ExampleView extends JPanel implements View {    

	private ViewManager fViewManager;		
    
    JTextArea fSnapshot;
    
    JScrollPane fScrollSnapshot;    

    public ExampleView(ViewManager parent, String snapshotStr){
        super(new BorderLayout());
        fViewManager = parent;                
        fSnapshot = new JTextArea();
        fSnapshot.setText(snapshotStr);
        fSnapshot.setEditable(false);
        fSnapshot.setLineWrap(true);
        fSnapshot.setWrapStyleWord(true);
        fSnapshot.setRows(7);
        fScrollSnapshot = new JScrollPane(fSnapshot);              
        
        JButton fRelevance = new JButton("Relevance");
        fRelevance.setMnemonic('R');
        fRelevance.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				getRelevance();				
			}
		});
        JButton fIrrelevance = new JButton("Irrelevance");
        fIrrelevance.setMnemonic('I');
        fIrrelevance.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				getIrrelevance();				
			}
		});
		// layout the buttons centered from left to right
		JPanel buttonPane = new JPanel();
		buttonPane.setLayout(new BoxLayout(buttonPane, BoxLayout.X_AXIS));
		buttonPane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));        
		buttonPane.add(Box.createRigidArea(new Dimension(0, 10)));
		buttonPane.add(fRelevance);
		buttonPane.add(Box.createHorizontalGlue());
		buttonPane.add(fIrrelevance);
		   
        // layout panel
        add(fScrollSnapshot, BorderLayout.NORTH);
        add(buttonPane, BorderLayout.SOUTH);
        setSize(new Dimension(300, 300));        
    }
    
	public void setText(String st){
    	this.fSnapshot.setText(st);
    }
    
    public String getText(){
    	return this.fSnapshot.getText();
    }
    
    public void getRelevance() {
    	this.fViewManager.hideExampleView();    	
    	this.fViewManager.createValidSnapshot(fSnapshot.getText());    	
    	this.fViewManager.getMainWindow().getControlPanel().getRelevance();
	}

	public void getIrrelevance() {		
		this.fViewManager.hideExampleView();		
		this.fViewManager.getMainWindow().getControlPanel().getIrrelevance();
	}
    
	@Override
	public void detachModel() {
		fViewManager.removeExampleView();
		fViewManager.getMainWindow().getLogPanel().setText("The generated snapshot has been removed!");
	}    
}