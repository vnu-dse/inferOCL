/* Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */
package fr.inria.atlanmod.inferocl.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JPanel;

import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.uml2.uml.Association;
//import org.eclipse.uml2.uml.At;
import org.eclipse.uml2.uml.Class;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Package;
import org.eclipse.uml2.uml.Property;
import org.eclipse.uml2.uml.resource.UMLResource;

import fr.inria.atlanmod.emftocsp.IModelReader;
import fr.inria.atlanmod.emftocsp.IModelToCspSolver;
import fr.inria.atlanmod.emftocsp.ProcessingException;
import fr.inria.atlanmod.inferocl.csp.EclipseSolver;
import fr.inria.atlanmod.inferocl.data.Invariant;
import fr.inria.atlanmod.inferocl.data.Snapshot;
import fr.inria.atlanmod.inferocl.gui.gensnapshot.FindExampleCspCode;
import fr.inria.atlanmod.inferocl.gui.gensnapshot.FindExampleWizard;
import fr.inria.atlanmod.inferocl.gui.views.SnapshotView;

/** 
 * A view for the controller
 * 
 * @author duc-hanh.dang
 */
@SuppressWarnings("serial")
public class ControlPanel extends JPanel{

	private ViewManager fViewManager;
	private MainWindow fMainWindow;
	private ResultPanel fResult;
	private EclipseSolver fEclipseSolver = null;
	private IModelToCspSolver<?> fModelSolver;	
	private List<Snapshot>	fSOK;
	private List<Snapshot>	fSNOK;
	private List<List<Invariant>> allINVList;
	private int allInferredRet;
	private int confidence;
	private int gainedPoint;
	//private int validINVidx;
	private int negINVidx;
	private int negInvIdx;
	private List<Invariant> consequentInvList;
	private List<List<Invariant>> equivalentINVList;
	private String exampleSnapshotStr;
	private boolean isFinding;

	//private JButton fBtnAddNewSok;
	//private JButton fBtnAddNewSnok;
	//private JButton fBtnGenPosSnapshot;
	private JButton fBtnNextFinding;
	private JButton fBtnGetFeedback;
	private JButton fBtnMoreExample;
	private JButton fBtnInfer;		


	public ControlPanel(ViewManager viewManager){
		super(new BorderLayout());
		fViewManager = viewManager;
		fMainWindow = viewManager.getMainWindow();
		this.fResult = fMainWindow.getResultPanel();
		this.fEclipseSolver = null;		
		negINVidx = 1;
		negInvIdx = 0;
		this.confidence = 0;		
		gainedPoint = 0;
		this.fSOK = new ArrayList<Snapshot>();
		this.fSNOK = new ArrayList<Snapshot>();
		allINVList = new ArrayList<List<Invariant>>();	
		consequentInvList = new ArrayList<Invariant>();
		equivalentINVList = new ArrayList<List<Invariant>>();
		this.isFinding = false;
		//--------------------------------------------------
		fBtnNextFinding = new JButton("NextFinding ");
		fBtnNextFinding.setMnemonic('N');
		fBtnNextFinding.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				nextFinding();								
			}
		});
		//--------------------------------------------------
		fBtnGetFeedback = new JButton("FindExample");
		fBtnGetFeedback.setMnemonic('F');
		fBtnGetFeedback.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				getFeedback();								
			}
		});
		fBtnMoreExample = new JButton("More ...        ");
		fBtnMoreExample.setMnemonic('M');
		fBtnMoreExample.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				moreExample();								
			}
		});
		fBtnInfer = new JButton("InferOCL       ");
		fBtnInfer.setMnemonic('I');
		fBtnInfer.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				inferOCL();
			}
		});
		// layout the buttons centered from top to bottom
		JPanel buttonPane = new JPanel();
		buttonPane.setLayout(new BoxLayout(buttonPane, BoxLayout.Y_AXIS));
		buttonPane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));        
		buttonPane.add(Box.createRigidArea(new Dimension(0, 10)));		
		buttonPane.add(fBtnGetFeedback);
		buttonPane.add(fBtnMoreExample);
		buttonPane.add(fBtnNextFinding);
		buttonPane.add(fBtnInfer);
		// layout panel
		add(buttonPane, BorderLayout.SOUTH);   
		this.fBtnGetFeedback.setEnabled(false);
		this.fBtnMoreExample.setEnabled(false);
		this.fBtnNextFinding.setEnabled(false);
		this.fBtnInfer.setEnabled(false);
		//setSize(new Dimension(300, 300));        
	}

	/**
	 * to infer OCL invs 
	 */
	public void inferOCL() {
		if (fEclipseSolver == null){        	
			MessageBox dlg = new MessageBox(fMainWindow,"Please load a model first!");
			dlg.setVisible(true);
			return;
		}        

		String snapshotInput = this.getSnapshotInput();
		//validINVidx = 0;
		negINVidx = 1;
		negInvIdx = 0;
		this.confidence = 0;		
		gainedPoint = 0;
		allINVList = new ArrayList<List<Invariant>>();	
		consequentInvList = new ArrayList<Invariant>();		
		equivalentINVList = new ArrayList<List<Invariant>>();
		this.isFinding = false;
		
		long startTime = System.currentTimeMillis();
		boolean ret = fEclipseSolver.inferOCL(snapshotInput);
		long stopTime = System.currentTimeMillis();
		long elapsedTime = stopTime - startTime;
		System.out.println("The inference takes " + elapsedTime + " ms");
		
		if (!ret){
			fResult.setResult("No OCL invariant could be inferred! Please update snapshots!",0,0);
			fMainWindow.getLogPanel().setText("Querying: " + fEclipseSolver.getQueryStr());
			this.fBtnGetFeedback.setEnabled(false);
			return;
		}else{
			this.allINVList = Invariant.getInvLists(fEclipseSolver.getInvFile());
			if(allINVList == null || allINVList.size() == 0){
				fResult.setResult("No OCL invariant could be inferred! Please update snapshots!",0,0);
				fMainWindow.getLogPanel().setText("Querying: " + fEclipseSolver.getQueryStr());
				this.fBtnGetFeedback.setEnabled(false);
				return;
			}			
			this.fBtnGetFeedback.setEnabled(true);
			this.allInferredRet = allINVList.size();
			computeConfidence();
			this.gainedPoint = 0;
			writeInv();
			fMainWindow.getLogPanel().setText("Querying: " + fEclipseSolver.getQueryStr() + "\nDone!");
		}    
	}

	public void getFeedback(){
		List<Invariant> validINV, invalidINV;
		Invariant inv;
		if(allINVList == null || allINVList.size() == 0){
			MessageBox dlg = new MessageBox(fMainWindow,"There is no OCL invariant inferred!");
			dlg.setVisible(true);			
			this.writeInv();
		}else{
			if( this.negINVidx >= allINVList.size() ){				
				negInvIdx = -1;
			}else if(this.negInvIdx >= 0 ){
				invalidINV = allINVList.get(this.negINVidx);
				if( this.negInvIdx >= invalidINV.size()){
					negInvIdx = 0;
					this.negINVidx ++;
					if( this.negINVidx >= allINVList.size()){
						negInvIdx = -1;					
					}
				}
				if( this.negInvIdx >= 0){
					inv = invalidINV.get(this.negInvIdx);
					validINV = allINVList.get(0);			
					while( validINV.contains(inv) || this.consequentInvList.contains(inv) ){
						this.negInvIdx++;
						if( negInvIdx >= invalidINV.size() ){
							negInvIdx = 0;
							this.negINVidx ++;
							if( this.negINVidx >= allINVList.size()){
								negInvIdx = -1;
								break;
							}
							invalidINV = allINVList.get(this.negINVidx);
						}				
						inv = invalidINV.get(this.negInvIdx);
					}
				}
			}
			if(negInvIdx == -1){
				this.isFinding = true;
				this.nextFinding();
			}else{
				this.findExampleWizard();
			}
		}
	}
	
	public void moreExample(){
		MessageBox dlg = new MessageBox(fMainWindow,"Under Construction!");
		dlg.setVisible(true);		
		return;
	}
	
	public void nextFinding(){
		List<Invariant> validINV, invalidINV, tmpINV;
		Invariant inv;
		if(this.isFinding == false){
			MessageBox dlg = new MessageBox(fMainWindow,"Let try to find examples first!");
			dlg.setVisible(true);
			this.writeInv();
			return;
		}
		this.isFinding = false;
		if(allINVList == null || allINVList.size() == 0){
			MessageBox dlg = new MessageBox(fMainWindow,"There is no OCL invariant inferred!");
			dlg.setVisible(true);
			this.writeInv();
			return;
		}		
		
		if( this.equivalentINVList.size() >= this.allINVList.size()){
			tmpINV = this.allINVList.get(0);
			this.allINVList.remove(0);
			this.allINVList.add(tmpINV);
			this.findExampleWizard();
			System.out.println("Working with only equivalent invariant sets");
			return;
		}
		
		if (negInvIdx == -1 || negINVidx >= allINVList.size()){
			tmpINV = this.allINVList.get(0);
			this.equivalentINVList.add(tmpINV);
			this.allINVList.remove(0);
			this.allINVList.add(tmpINV);
			this.consequentInvList = new ArrayList<Invariant>();
			this.negINVidx = 1;
			negInvIdx = 0;
			
			if( this.equivalentINVList.size() >= this.allINVList.size()){
				this.findExampleWizard();
				System.out.println("Working with only equivalent invariant sets");
				return;
			}
		}else{			
			invalidINV = allINVList.get(this.negINVidx);	
			this.consequentInvList.add(invalidINV.get(this.negInvIdx) );			
			this.negInvIdx++;
			if( this.negInvIdx >= invalidINV.size()){
				this.negINVidx ++;
				this.negInvIdx = 0;
				if( this.negINVidx >= allINVList.size()){				
					tmpINV = this.allINVList.get(0);
					this.equivalentINVList.add(tmpINV);
					this.allINVList.remove(0);
					this.allINVList.add(tmpINV);
					this.consequentInvList = new ArrayList<Invariant>();
					negINVidx = 1;
					
					if( this.equivalentINVList.size() >= this.allINVList.size()){
						this.findExampleWizard();
						System.out.println("Working with only equivalent invariant sets");
						return;
					}
					
				}								
			}	
		}
		
		invalidINV = allINVList.get(this.negINVidx);
		inv = invalidINV.get(this.negInvIdx);
		validINV = allINVList.get(0);
		
		while( validINV.contains(inv) || this.consequentInvList.contains(inv) ){
			this.negInvIdx++;
			if( negInvIdx >= invalidINV.size() ){
				this.negINVidx ++;
				negInvIdx = 0;
				
				if( this.negINVidx >= allINVList.size()){
					tmpINV = this.allINVList.get(0);
					this.equivalentINVList.add(tmpINV);
					this.allINVList.remove(0);
					this.allINVList.add(tmpINV);					
					validINV = this.allINVList.get(0);
					this.consequentInvList = new ArrayList<Invariant>();					
					negINVidx = 1;
					
					if( this.equivalentINVList.size() >= this.allINVList.size()){
						this.findExampleWizard();
						System.out.println("Working with only equivalent invariant sets");
						return;
					}
				}
				invalidINV = allINVList.get(this.negINVidx);				
			}				
			inv = invalidINV.get(this.negInvIdx);
		}
		
		//System.out.println("negInv:" + inv.getOclInv());
		//for(Invariant inv1:validINV){
		//	System.out.println("Inv:" + inv1.getOclInv());
		//}
		
		
		this.findExampleWizard();
	}
	/**
	 * to show a wizard in order find a new valid snapshot 
	 */
	public void findExampleWizard() {		
		if( fMainWindow.getModelSolver() == null){
			MessageBox dlg = new MessageBox(fMainWindow,"Please load a model or update snapshots!");
			dlg.setVisible(true);
			return;
		}
		Shell shell = new Shell(Display.getCurrent(), SWT.NONE);
		FindExampleWizard wizard = new FindExampleWizard(fMainWindow);
		WizardDialog dialog = new WizardDialog(shell, wizard);
		dialog.open();
	}

	public boolean findExample() {
		if(allINVList == null || allINVList.size() == 0){
			MessageBox dlg = new MessageBox(fMainWindow,"There is no OCL invariant inferred!");
			dlg.setVisible(true);
			return false;
		}	
		List<Invariant> validINV = allINVList.get(0),invalidINV;
		Invariant invalidInv;
		if(this.equivalentINVList.size() >= allINVList.size()){
			this.negInvIdx = -1;
		}
		if(this.negInvIdx >=0 && this.negINVidx < allINVList.size()){
			invalidINV = allINVList.get(this.negINVidx);
			if(negInvIdx > invalidINV.size()){
				invalidInv = null;
			}else{
				invalidInv = invalidINV.get(this.negInvIdx);
			}
		}else{
			invalidInv = null;
		}
		
		try {
			IModelReader<UMLResource, Package, Class, Association, Property, Operation> modelReader = (IModelReader<UMLResource, Package, Class, Association, Property, Operation>)fModelSolver.getModelReader();
			Map<String, String> modelElementsDomain = fModelSolver.getModelElementsDomain();
			boolean result = false;				
			FindExampleCspCode genCspCode = new FindExampleCspCode(modelReader, modelElementsDomain, validINV, invalidInv);
			long startTime = System.currentTimeMillis();
			result = fEclipseSolver.findExample(genCspCode.getCspCode());
			long stopTime = System.currentTimeMillis();
			long elapsedTime = stopTime - startTime;
			System.out.println("Finding the example takes " + elapsedTime + " ms");
			if(result){
				File exampleFile = fEclipseSolver.getExampleFile();
				BufferedReader readbuffer = new BufferedReader(new FileReader(exampleFile));
				this.exampleSnapshotStr = readbuffer.readLine().toLowerCase();			
				readbuffer.close();
				this.fBtnNextFinding.setEnabled(false);
				this.fViewManager.createExampleSnapshot(exampleSnapshotStr);
				if( this.equivalentINVList.size() >= this.allINVList.size()){
					this.fBtnMoreExample.setEnabled(true);
					if(this.allINVList.size() > 1){
						this.fBtnNextFinding.setEnabled(true);
					}
				}
			}else{
				MessageBox dlg = new MessageBox(fMainWindow,"No counterexample is found! Let update domain restrictions and regenerate it! Only if still not found in every case, let switch to NextFinding!");				
				dlg.setVisible(true);
				this.fBtnMoreExample.setEnabled(false);
				this.fBtnNextFinding.setEnabled(true);
			}
			this.isFinding = true;
			return result;
		} catch (IOException e) {
			this.fBtnMoreExample.setEnabled(false);
			System.out.println(e.toString());
			return false;
		}
	}

	public String getSnapshotInput() {
		StringBuilder ret = new StringBuilder();		
		ret.append("SOK = [");		
		StringBuilder tmp = new StringBuilder();
		for(Snapshot s: this.fSOK){
			if(s.toString() != ""){
				tmp.append( "," + s.toString());	
			}			
		}
		if(this.fSOK.size() != 0){
			ret.append( tmp.toString().substring(1) );
		}
		ret.append("], SNOK = [");
		tmp = new StringBuilder();
		for(Snapshot s: this.fSNOK){
			if(s.toString() != ""){
				tmp.append( "," + s.toString());	
			}
		}		
		if(this.fSNOK.size() != 0){
			ret.append( tmp.toString().substring(1) );
		}
		ret.append("]");
		return ret.toString();
	}

	public void addNewSnapshot(Boolean isValidSnapshot, String tmpStr) {
		Snapshot sp = new Snapshot(isValidSnapshot, tmpStr);
		if(isValidSnapshot){
			fSOK.add(sp);
		}else{
			fSNOK.add(sp);
		}		
	}

	public void addGainedPoint() {
		gainedPoint++;
		fResult.setGainedPoint(gainedPoint);		
	}


	public void computeConfidence() {
		int numInv = allINVList.size();
		if( numInv > 1){
			confidence = 100 / numInv;  
		}else if (numInv == 1){
			confidence = 80;
		}else{
			confidence = 0;
		}
	}

	public void writeInv() {
		if(allINVList.size() == 0){
			fResult.setResult("No candidate found!\nPerhaps, the knowledge (OCL patterns) need to be updated!","0 / " + this.allInferredRet, 0);
			return;
		}
		List<Invariant> bestINV = allINVList.get(0);
		String str = "";
		for(Invariant inv: bestINV){
			if(str != ""){
				str = str + "\n-------------\n";
			}
			str = str + inv.getOclInv();
		}		
		fResult.setResult(str, "" + allINVList.size() + " / " + this.allInferredRet , this.gainedPoint);
	}

	public IModelToCspSolver<?> getModelSolver() {
		return this.fModelSolver;

	}

	public void setModelSolver(IModelToCspSolver<UMLResource> modelSolver) {
		this.fModelSolver = modelSolver;

	}

	public EclipseSolver getEclipseSolver() {
		return fEclipseSolver;
	}

	public void setEclipseSolver(EclipseSolver solver){
		this.fEclipseSolver = solver;
	}


	public void disposeEngineProcess() {
		if(fEclipseSolver == null) return;
		this.fEclipseSolver.disposeEngineProcess();
	}
	
	public void reset(){
		fResult.setResult("", "", 0);		
		this.fViewManager.closeAllViews();		
		this.resetSnapshot();
		this.fBtnGetFeedback.setEnabled(false);
		this.fBtnInfer.setEnabled(false);		
		this.fBtnMoreExample.setEnabled(false);		
		this.fBtnNextFinding.setEnabled(false);		
	}

	public void resetSnapshot() {
		fSOK.clear();
		fSNOK.clear();
	}

	public void getRelevance() {
		int idx = 0;
		List<Invariant> tmpINV;
		this.addGainedPoint();
		if(negINVidx < allINVList.size() && negInvIdx >= 0){
			tmpINV = allINVList.get(this.negINVidx);
			if(negInvIdx > tmpINV.size()){
				return;
			}
			String invalidInv = tmpINV.get(this.negInvIdx).getOclInv();
			this.allINVList.remove(negINVidx);
			this.equivalentINVList.remove(tmpINV);
			while(idx < allINVList.size()){
				tmpINV = allINVList.get(idx);
				for(Invariant inv:tmpINV){
					if(inv.getOclInv().equals(invalidInv)){
						this.allINVList.remove(idx);
						idx--;
						this.equivalentINVList.remove(tmpINV);
						break;
					}
				}
				idx++;
			}			
			idx  = 0;
			while(idx < allINVList.size()){
				tmpINV = allINVList.get(idx);
				if( !this.getEclipseSolver().isValidSnapshot(this.exampleSnapshotStr,tmpINV) ){
					this.allINVList.remove(idx);
					idx--;
					this.equivalentINVList.remove(tmpINV);
				}
				idx++;
			}
			this.negInvIdx = 0;
		}
		this.computeConfidence();
		writeInv();
		MessageBox dlg = new MessageBox(fMainWindow,"The result was updated!");
		dlg.setVisible(true);
	}

	public void getIrrelevance() {
		if(0 < allINVList.size()){			
			this.equivalentINVList.remove(this.allINVList.get(0));
			this.allINVList.remove(0);
			this.gainedPoint = 0;
			int idx = 0;
			while(idx < allINVList.size()){
				List<Invariant> tmpINV = allINVList.get(idx);
				if( this.getEclipseSolver().isValidSnapshot(this.exampleSnapshotStr,tmpINV) ){
					this.allINVList.remove(idx);
					idx--;
					this.equivalentINVList.remove(tmpINV);;
				}
				idx++;
			}			
		}
		this.negINVidx = 1;
		this.consequentInvList = new ArrayList<Invariant>();
		this.negInvIdx = 0;
		this.computeConfidence();
		writeInv();
		this.fBtnMoreExample.setEnabled(false);
		MessageBox dlg = new MessageBox(fMainWindow,"The result was updated!");
		dlg.setVisible(true);
	}

	public void readyInferOCL() {
		this.fBtnInfer.setEnabled(true);		
	}
}
