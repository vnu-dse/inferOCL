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
package fr.inria.atlanmod.inferocl.gui.gensnapshot;


import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.jface.wizard.Wizard;

import fr.inria.atlanmod.inferocl.gui.ControlPanel;
import fr.inria.atlanmod.inferocl.gui.MainWindow;
import fr.inria.atlanmod.inferocl.main.Options;


/**
 * @author duc-hanh.dang
 *
 */
public class FindExampleWizard extends Wizard {
	private IWizardPage[] wizardNavigation;
	private ControlPanel fControlPanel;	
	//private IModelToCspSolver<?> modelSolver;
	//String logFileName;
	
	public FindExampleWizard(MainWindow mainWindow) {
		fControlPanel = mainWindow.getControlPanel();
		wizardNavigation = new IWizardPage[1];
		wizardNavigation[0] = new DomainRestrictionPage(Options.ModelWizardNavigation_0, fControlPanel.getModelSolver());		
	    //wizardPages[1] = new ResultLocationSelectionPage("Validation results", Messages.ModelWizardNavigation_3, null, new ArrayList<String>(Arrays.asList("Folder")), modelSolver); //$NON-NLS-3$ //$NON-NLS-1$		
	}

	@Override
	public void addPages() {	  
	  for (int i = 0; i < wizardNavigation.length; i++)
	    addPage(wizardNavigation[i]);
	}
	
	@Override
	public boolean performCancel() {	  
	  return true;
	}
	
	@Override
	public boolean performFinish() {		
		return fControlPanel.findExample();
		//msgTitle = Messages.ValidationWizard_2;
		//message = Messages.ValidationWizard_3;	      
		//MessageBox messageBox = new MessageBox(this.getShell(), SWT.ICON_WARNING | SWT.OK);
		//messageBox.setText(msgTitle);
		//messageBox.setMessage(message);
		//messageBox.open();		
	}
	
	@Override
	public boolean canFinish() {
	  return true;	  
	}
}
