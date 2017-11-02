/*******************************************************************************
 * Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     INRIA Rennes Bretagne-Atlantique - initial API and implementation
 *******************************************************************************/
package fr.inria.atlanmod.inferocl.csp;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

import fr.inria.atlanmod.emftocsp.ProcessingException;
import fr.inria.atlanmod.inferocl.data.Invariant;
import fr.inria.atlanmod.inferocl.gui.LogPanel;
import fr.inria.atlanmod.inferocl.main.Options;

import com.parctechnologies.eclipse.CompoundTerm;
import com.parctechnologies.eclipse.EclipseEngine;
import com.parctechnologies.eclipse.EclipseEngineOptions;
import com.parctechnologies.eclipse.EclipseException;
import com.parctechnologies.eclipse.Fail;
import com.parctechnologies.eclipse.OutOfProcessEclipse;
import com.parctechnologies.eclipse.Throw;

/**
 * @author duc-hanh.dang
 */

public class EclipseSolver {

	private EclipseEngineOptions engineOptions = null;
	private EclipseEngine engine = null;
	String queryStr = null;
	LogPanel fLogPanel;
	private String filePath = null;

	public EclipseSolver(String eclipsePath, LogPanel fLogPanel) {
		this.fLogPanel = fLogPanel; 
		engineOptions = new EclipseEngineOptions(new File(eclipsePath));
		engineOptions.setUseQueues(false);    
		try {
			engine = new OutOfProcessEclipse(engineOptions);
		} 
		catch (IOException e) {
			e.printStackTrace();
		} 
		catch (EclipseException e) {
			e.printStackTrace();
		}
	}

	public boolean inferOCL(String snapshotInput) {
		if(filePath == null) return false;
		try { 
			StringBuilder query = new StringBuilder();
			query.append(snapshotInput);
			query.append(", getPatterns(PATTERN), ");
			query.append("findall(INV, apply_all(SOK, SNOK, PATTERN, INV), INVList),");
			query.append("writeINV(\""); //$NON-NLS-1$
			query.append(filePath.replaceAll("\\\\", "\\\\\\\\")); //$NON-NLS-1$ //$NON-NLS-2$
			query.append(".inv\", INVList)");
			queryStr = query.toString();
			engine.rpc(queryStr);			
			//fLogPanel.setText("Querying:\n" + query.toString() + "\n... Done!");
			return true;		
		} catch (EclipseException | IOException e) {
			//disposeEngineProcess(); 
			System.out.println("Unexpected problem with the query: " + queryStr);
			System.out.println("Please consult the executed generated CLP code (.ecl file)" + e);
			return false;
		}
	}

	public boolean findExample(String cspCode){
		if(cspCode == null || engine == null) return false;				
		try {			
			File exampleFile = new File(filePath + ".snapshot.ecl");			
			BufferedWriter writer = new BufferedWriter(new FileWriter(exampleFile) );		
		    writer.append(cspCode);
		    writer.flush();
			writer.close();
			engine.compile(exampleFile);
			
			StringBuilder query = new StringBuilder();	
			query.append("findExample(Instances),txt_write_object_diagram(\"");
			query.append(filePath.replaceAll("\\\\", "\\\\\\\\")); //$NON-NLS-1$ //$NON-NLS-2$
			query.append(".snapshot\", Instances)");
			queryStr = query.toString();
			System.out.println(queryStr);
			engine.rpc(queryStr);
		} catch (EclipseException | IOException e) {
			//throw new ProcessingException("Unexpected problem. Please consult the executed generated CLP code (.ecl file)",e);
			System.out.println("Unexpected problem with the query: " + queryStr);
			System.out.println("Please consult the executed generated CLP code (.ecl file)" + e);
			return false;
		}		
		return true;
	}
	
	public boolean isValidSnapshot(String exampleSnapshotStr,Invariant inv) {
		String patId = inv.getPatternId();
		String patName = inv.getPatternName();
		String paraStr = inv.getMatchingPara();
		try {
			StringBuilder query = new StringBuilder();	
			query.append("Sok=" + exampleSnapshotStr);			
			query.append(", Para = " + paraStr);
			query.append(", getLocalPara(" + patId + ", Para, LocalPara),");
			query.append(patName + "(Sok,LocalPara,1)");
			queryStr = query.toString();
			//System.out.println(queryStr);
			engine.rpc(queryStr);
		} catch (EclipseException | IOException e) {
			//throw new ProcessingException("Unexpected problem. Please consult the executed generated CLP code (.ecl file)",e);
			System.out.println("Unexpected problem with the query: " + queryStr);
			System.out.println("Please consult the executed generated CLP code (.ecl file)" + e);
			return false;
		}		
		return true;
	}
	
	public boolean isValidSnapshot(String exampleSnapshotStr,List<Invariant> oclINV) {		
		for(Invariant inv: oclINV){
			if(!this.isValidSnapshot(exampleSnapshotStr, inv)){
				return false;
			}
		}		
		return true;
	}

	/*
	 * To generate an invalid snapshot
	 */

	/*public String genInvalidSnapshot(List<Invariant> list, String snapshotInput){
	  if(list.size() == 0) return null;	  
	  //Currently, the generated snapshot is only rejected by the first invariant of the list
	  Invariant inv;
	  for(int i = 0; i < list.size(); i++){
		  inv = list.get(i);
		  StringBuilder query = new StringBuilder();	  
		  query.append(snapshotInput);
		  query.append(", Para = " + inv.getMatchingPara() );
		  query.append(", Pat = " + inv.getPatternId());
		  query.append(", genSnok(SOK, SNOK, Pat, Para, Result)");
		  try {
			  CompoundTerm result = engine.rpc(query.toString());
			  CompoundTerm retGoal1 = (CompoundTerm) result.arg(2);		  
			  CompoundTerm retGoal2 = (CompoundTerm) retGoal1.arg(2);
			  CompoundTerm retGoal3 = (CompoundTerm) retGoal2.arg(2);
			  CompoundTerm retGoal = (CompoundTerm) retGoal3.arg(2);		  
			  String ret = (String) retGoal.arg(5);
			  //System.out.println("Querying: " + query.toString());
			  //System.out.println("Result: " + ret + "HanhEnd");
			  if( ret != ""){
				  return ret;
			  }
		  } catch (EclipseException | IOException e) {
			  e.printStackTrace();
			  System.out.print(e.toString());
			  return null;
		  }
	  }
	  return "";
  }*/

	public void compile(File srcFile, List<File> libs) throws EclipseException, IOException {
		if(engine == null) return;
		engine.compile(srcFile);
		if (libs != null){
			for (File importFile : libs){
				engine.compile(importFile);
			}
		}
	}

	public void disposeEngineProcess() {
		try {
			((OutOfProcessEclipse)engine).destroy();
		} 
		catch (Exception e) {
			e.printStackTrace();
		} 
		finally {
			engine = null;
		}
	} 
	public String getQueryStr(){
		return queryStr;
	}

	public void setFilePath(String path) {
		this.filePath = path;		
	}
	public File getInvFile(){		
		return new File(this.filePath + ".inv");
	}
	public File getExampleFile(){
		return new File(this.filePath + ".snapshot");
	}	
}