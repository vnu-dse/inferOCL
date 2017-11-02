/*
 * Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */

package fr.inria.atlanmod.inferocl.gui;

import java.awt.*;
import javax.swing.*;
import javax.swing.border.Border;

/** 
 * A Result panel with a text area.
 * 
 * @author duc-hanh.dang
 */
@SuppressWarnings("serial")
class ResultPanel extends JPanel {
    private JTextArea fTextResult;
    private JLabel fConfidence;
    private JLabel fGainedPoint;
    private int confidence; 
    private int gainedPoint;
   
    public ResultPanel() {
        setLayout(new BorderLayout());
        fTextResult = new JTextArea(7,5);
        fTextResult.setEditable(false);
        fTextResult.setLineWrap(true);
        fConfidence = new JLabel("Candidate: ");        
        fGainedPoint = new JLabel("Gained Point: ");  
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));        
        setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));        
        JPanel confidencePan = new JPanel(new FlowLayout(FlowLayout.LEFT));
        JPanel gainPan = new JPanel(new FlowLayout(FlowLayout.LEFT));
        JPanel resultPan = new JPanel(new FlowLayout(FlowLayout.LEFT));
        confidencePan.add(fConfidence);
        gainPan.add(fGainedPoint);
        resultPan.add(new JLabel("Result: "));
        add(resultPan);
        add(new JScrollPane(fTextResult));
        add(confidencePan);
        add(gainPan);
    }
    /**
     * Sets the text
     */
    public void setText(String s) {    	
    	fTextResult.setText(s);
    }
    /**
     * Sets the result
     */
    public void setResult(String content, int confidence, int gainedPoint) {
    	//JLabel label = (JLabel) this.getComponent(0);
    	//label.setText(title);
    	fTextResult.setText(content);    	
    	this.setConfidence(confidence);
    	this.setGainedPoint(gainedPoint);
    }
    
    /**
     * Sets the result
     */
    public void setResult(String content, String candidateStr, int gainedPoint) {
    	//JLabel label = (JLabel) this.getComponent(0);
    	//label.setText(title);
    	fTextResult.setText(content);    	
    	fConfidence.setText("Candidate: " + candidateStr);
    	this.setGainedPoint(gainedPoint);
    }
    
    public void setConfidence(int confidence){
    	this.confidence = confidence;
    	fConfidence.setText("Confidence: " + confidence + "%" );
    }
    
    public int getConfidence(){
    	return confidence;
    }
    
    public void setGainedPoint(int gainedPoint){
    	this.gainedPoint = gainedPoint;
    	fGainedPoint.setText("Gained Point: " + gainedPoint);
    }    
    
    public int getGainedPoint(){
    	return gainedPoint;
    }
    
    /**
     * Clears the text
     */
    public void clear() {
    	fTextResult.setText(null);
    }
}