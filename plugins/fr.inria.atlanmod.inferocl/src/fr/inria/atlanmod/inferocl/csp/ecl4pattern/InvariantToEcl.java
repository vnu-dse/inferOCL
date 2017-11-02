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
package fr.inria.atlanmod.inferocl.csp.ecl4pattern;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Stack;

import org.eclipse.core.resources.IFile;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.ocl.Environment;
import org.eclipse.ocl.OCLInput;
import org.eclipse.ocl.ParserException;
import org.eclipse.ocl.ecore.EcoreFactory;
import org.eclipse.ocl.ecore.EcorePackage;
import org.eclipse.ocl.expressions.BooleanLiteralExp;
import org.eclipse.ocl.expressions.CollectionItem;
import org.eclipse.ocl.expressions.CollectionLiteralExp;
import org.eclipse.ocl.expressions.IntegerLiteralExp;
import org.eclipse.ocl.expressions.IteratorExp;
import org.eclipse.ocl.expressions.OCLExpression;
import org.eclipse.ocl.expressions.OperationCallExp;
import org.eclipse.ocl.expressions.PropertyCallExp;
import org.eclipse.ocl.expressions.RealLiteralExp;
import org.eclipse.ocl.expressions.StringLiteralExp;
import org.eclipse.ocl.expressions.TypeExp;
import org.eclipse.ocl.expressions.Variable;
import org.eclipse.ocl.expressions.VariableExp;
import org.eclipse.ocl.helper.OCLHelper;
import org.eclipse.ocl.types.SetType;
import org.eclipse.ocl.uml.OCL;
import org.eclipse.ocl.uml.UMLEnvironmentFactory;
import org.eclipse.ocl.uml.UMLFactory;
import org.eclipse.ocl.uml.UMLPackage;
import org.eclipse.ocl.util.TypeUtil;
import org.eclipse.ocl.utilities.AbstractVisitor;
import org.eclipse.ocl.utilities.ExpressionInOCL;
import org.eclipse.ocl.utilities.PredefinedType;
import org.eclipse.ocl.utilities.TypedElement;
import org.eclipse.ocl.utilities.UMLReflection;
import org.eclipse.uml2.uml.Association;
import org.eclipse.uml2.uml.CallOperationAction;
import org.eclipse.uml2.uml.Class;
import org.eclipse.uml2.uml.Classifier;
import org.eclipse.uml2.uml.Constraint;
import org.eclipse.uml2.uml.EnumerationLiteral;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Package;
import org.eclipse.uml2.uml.Parameter;
import org.eclipse.uml2.uml.Property;
import org.eclipse.uml2.uml.SendSignalAction;
import org.eclipse.uml2.uml.State;
import org.eclipse.uml2.uml.internal.resource.UMLResourceFactoryImpl;
import org.eclipse.uml2.uml.resource.UMLResource;
import org.eclipse.uml2.uml.validation.IEValidatorProvider.UML;
/* 
 * To generate ecl codes from pattern specifications
 * 
 * @author duc-hanh.dang
 */

public class InvariantToEcl{  
	public static void main(String[] args){
		//*************************************************************
		//APSEC2013 paper
		//*************************************************************
		//String folderPath="/home/duc-hanh.dang/acquireOCL/genEcl4inv/";
		//String umlFile = "p11_nonSelfInclusion.uml";
		//String oclFile = "p11_isInvalid_nonSelfInclusion.ocl";
		//String eclFile = "p11_isInvalid_nonSelfInclusion.ecl";
		//String umlFile = "p00_interval.uml";
		//String oclFile = "p00_isValid_interval.ocl";
		//String eclFile = "p00_isValid_interval.ecl";
		//String umlFile = "PersonCar.uml";
		//String oclFile = "PersonCar_Valid.ocl";
		//String eclFile = "PersonCar_Valid.ecl";
		//String umlFile = "p10_multiplicityConstraint.uml";
		//String oclFile = "p10_multiplicityConstraint.ocl";
		//String eclFile = "p10_multiplicityConstraint.ecl";
		//String umlFile = "p03_uniqueAttr.uml";
		//String oclFile = "p03_uniqueAttr.ocl";
		//String eclFile = "p03_uniqueAttr.ecl";
		//String umlFile = "p12_attrRel.uml";
		//String oclFile = "p12_attrRel.ocl";
		//String eclFile = "p12_attrRel.ecl";		
		//String oclFilePath =  folderPath + oclFile;
		//String cspCodeFilePath = folderPath + eclFile;	    
		//String modelFilePath = folderPath + umlFile;
		//*************************************************************
		//*************************************************************
		//String folderPath="/home/duc-hanh.dang/Dropbox/workspace/oclpatterns/";
		String folderPath="/home/hanhdd/Dropbox/workspace/oclpatterns/";
		String patternName = "countObject1";		
		//String patternName = "attrRel2";
		//String patternName = "oneReferee";
		//String patternName = "maxCard";
		//String patternName = "requiredInclusion";
		//String patternName = "restrictedAssoc";
		//String patternName = "cycleFree";		
		
		String oclFilePath =  folderPath + patternName + ".ocl";
		String cspCodeFilePath = folderPath + patternName + ".ecl";
		String modelFilePath = folderPath + patternName + ".uml";
		File cspCodeFile = new File(cspCodeFilePath);

		FileInputStream in = null;
		try {
			in = new FileInputStream(oclFilePath);
		}catch (FileNotFoundException e) {
			System.out.print(e.toString());
		}    
		URI modelFileURI = URI.createFileURI(modelFilePath); 
		ResourceSet rSet = new ResourceSetImpl();    
		rSet.getResourceFactoryRegistry().getExtensionToFactoryMap().put("uml", new UMLResourceFactoryImpl());
		OCL.initialize(rSet);    
		UMLResource modelResource = (UMLResource)rSet.getResource(modelFileURI, true);
		UMLEnvironmentFactory umlEnv = new UMLEnvironmentFactory(modelResource.getResourceSet());    
		OCLInput oclDocument = new OCLInput(in);    
		OCL oclParser = OCL.newInstance(umlEnv);    
		Environment.Registry.INSTANCE.registerEnvironment(umlEnv.createEnvironment());
		List<Constraint> constraints = new ArrayList<Constraint>();
		try {
			constraints = oclParser.parse(oclDocument);
		}catch (Exception e) {
			e.printStackTrace();
			System.out.println(e.getMessage());
		}
		StringBuilder cspCode = new StringBuilder();
		HashMap<String, String> ctfpMap = new HashMap<String, String>();
		OclTemplateToEcl oclVisitor = OclTemplateToEcl.getInstance(null);
		OCLHelper<Classifier, Operation, Property, Constraint> helper = oclParser.createOCLHelper();
		for (Constraint c : constraints) {
			List<String> keywords = c.getKeywords();
			if (keywords != null)
				for (String keyword : keywords)
					if (!keyword.equalsIgnoreCase("precondition") && !keyword.equalsIgnoreCase("postcondition")) {
						ExpressionInOCL<Classifier, Parameter> oclExpression = (ExpressionInOCL<Classifier, Parameter>) c.getSpecification();
						Class contextCls = (Class) c.getConstrainedElements().get(0);
						//insertQuantificationForSelf(helper, contextCls, oclExpression);
						try {     	  
							/* TODO: This method inserts the quantification for "self" only if this variable
							 *       occurs. This is working and practical. 
							 *       However, the precise semantics of OCL would require that self is always quantified.
							 *       In the long term, a switch for EMFtoCSP should be added.
							 */
							OCLExpression bodyExp = oclExpression.getBodyExpression();
							LookupSelfVariableVisitor lookupVisitor = new LookupSelfVariableVisitor();
							bodyExp.accept(lookupVisitor);
							Variable<Classifier, Parameter> selfDecl = lookupVisitor.getResult();
							if (selfDecl != null) {
								//System.err.println("Adding required self variable quantification");
								UMLPackage oclPackage =  (UMLPackage) oclExpression.eClass().getEPackage();
								UMLFactory oclFactory = (UMLFactory) oclPackage.getUMLFactory();
								IteratorExp forAllExp = oclFactory.createIteratorExp();
								forAllExp.setName("forAll");
								forAllExp.setType((Classifier) bodyExp.getType());
								selfDecl.setName("self");
								selfDecl.setType(contextCls);
								forAllExp.getIterator().add(selfDecl);
								forAllExp.setBody(bodyExp);

								helper.setContext(contextCls);
								OCLExpression<Classifier> allInstancesExp = helper.createQuery(contextCls.getName() + ".allInstances()");
								forAllExp.setSource(allInstancesExp);

								oclExpression.setBodyExpression(forAllExp);
							}
						} catch (ParserException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						cspCode.append(oclExpression.accept(oclVisitor));
						ctfpMap.put(c.getName(), oclVisitor.getConstraintFirstPredicate());
						cspCode.append("\n");                      
					}
		}   
		try {
			PrintWriter out = new PrintWriter(cspCodeFile);
			out.println(cspCode);
			out.flush();
		} catch (IOException e) {
			//throw new ProcessingException(e);
		}
	}  
}