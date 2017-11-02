/*******************************************************************************
 * Copyright (c) 2011 INRIA Rennes Bretagne-Atlantique.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     INRIA Rennes Bretagne-Atlantique - initial API and implementation
 *******************************************************************************/
package fr.inria.atlanmod.emftocsp.umltoecl;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EParameter;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.ocl.ParserException;
import org.eclipse.ocl.ecore.EcoreFactory;
import org.eclipse.ocl.ecore.EcorePackage;
import org.eclipse.ocl.ecore.OCL;
import org.eclipse.ocl.expressions.IteratorExp;
import org.eclipse.ocl.expressions.OCLExpression;
import org.eclipse.ocl.expressions.Variable;
import org.eclipse.ocl.helper.OCLHelper;
import org.eclipse.ocl.uml.UMLFactory;
import org.eclipse.ocl.uml.UMLPackage;
import org.eclipse.ocl.utilities.ExpressionInOCL;
import org.eclipse.uml2.uml.Association;
import org.eclipse.uml2.uml.Class;
import org.eclipse.uml2.uml.Classifier;
import org.eclipse.uml2.uml.Constraint;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Package;
import org.eclipse.uml2.uml.Parameter;
import org.eclipse.uml2.uml.Property;
import org.eclipse.uml2.uml.resource.UMLResource;

import fr.inria.atlanmod.emftocsp.IModelProperty;
import fr.inria.atlanmod.emftocsp.IModelReader;
import fr.inria.atlanmod.emftocsp.IModelToCspSolver;
import fr.inria.atlanmod.emftocsp.IOclParser;
import fr.inria.atlanmod.emftocsp.impl.LackOfConstraintsRedundanciesModelProperty;
import fr.inria.atlanmod.emftocsp.impl.LackOfConstraintsSubsumptionsModelProperty;
import fr.inria.atlanmod.emftocsp.uml.impl.UmlCspCodeGenerator;

/**
 * @author <a href="mailto:carlos.gonzalez@inria.fr">Carlos A. Gonz�lez</a>
 *
 */
public class UmlToEclCodeGenerator extends UmlCspCodeGenerator {
  IModelToCspSolver<UMLResource> modelSolver;

  public UmlToEclCodeGenerator(IModelToCspSolver<UMLResource> modelSolver) {
    this.modelSolver = modelSolver;
  }
  
  @SuppressWarnings("unchecked")
  @Override
  public String getCspCode() {
    setModel(modelSolver.getModel());
    setOclDocument(modelSolver.getConstraintsDocument());
    setModelElementsDomains(modelSolver.getModelElementsDomain());
    setProperties(modelSolver.getModelProperties());
    setModelReader((IModelReader<UMLResource, Package, Class, Association, Property, Operation>)modelSolver.getModelReader());
    setOclParser((IOclParser<Constraint, UMLResource>)modelSolver.getOclParser());
    
    StringBuilder s = new StringBuilder();
    s.append(translateUmlModel(GetModelReader(), getModelElementsDomain(), GetProperties()));
    s.append(translateOclConstraints(GetOclParser(), GetProperties(), GetModel(), getOclDocument()));
    return s.toString();
  }
  
  private String translateUmlModel(IModelReader<UMLResource, Package, Class, Association, Property, Operation> umlModelReader, Map<String, String> modelElementsDomain, List<IModelProperty> properties) {
    StringBuilder s = new StringBuilder();
    try {
      List<String> constraintsNames = GetOclParser().getModelConstraintsNames(GetModel(), getOclDocument());
      ModelToEcl umlTranslator = new ModelToEcl(umlModelReader, modelElementsDomain, properties, constraintsNames, modelSolver.getLogger());
      
      s.append(umlTranslator.genLibsSection());
      s.append("\n");
      s.append("%:-use_module(\"libs/allPatterns.ecl\").\n");
      s.append("\n");
      s.append(umlTranslator.genStructSection());
      s.append("\n");
      s.append(umlTranslator.genHeaderSection());
      s.append("\n");
      s.append(umlTranslator.genCardinalityDefinitionsSection());
      s.append("\n");
      s.append(umlTranslator.genCardinalityConstraintsSection());
      s.append("\n");
      s.append(umlTranslator.genCardinalityInstantiationSection());
      s.append("\n");
      s.append(umlTranslator.genInstancesSection1());
      s.append("\n");
      s.append(umlTranslator.genSnapshotSection());
      s.append("\n");
      s.append(umlTranslator.genObjectsCreationSection());
      s.append("\n");
      s.append(umlTranslator.genLinksCreationSection());
      s.append("\n");
      s.append(umlTranslator.genInstancesSection2());
      s.append("\n");
      s.append(umlTranslator.genOclRootSection());
      s.append("\n");
      s.append(umlTranslator.genAllAttributesSection());
      s.append("\n");
      s.append(umlTranslator.genGeneralizationSection());
      s.append("\n");
      s.append(umlTranslator.genIndexesSection());
      s.append("\n");
      s.append(umlTranslator.genAssociationRolesSection());
      s.append("\n");
      s.append(umlTranslator.genAssociationIsUniqueSection());
      s.append("\n");
      s.append(umlTranslator.genClassGeneralization());
      s.append("\n");
      s.append(umlTranslator.genModelPropertiesSection());
      s.append("\n");
      s.append(umlTranslator.genConstraintBinAssocMultiSection());
      s.append("\n");
      s.append(umlTranslator.genClassCreationSection());
      s.append("\n");
      s.append(umlTranslator.genAssociationCreationSection());
      s.append("\n");
    }
    catch (Exception e) {
      e.printStackTrace();
      System.out.println(e.getMessage());
    }
    return s.toString();
  }
  
  @SuppressWarnings("rawtypes")
  private String translateOclConstraints(IOclParser<Constraint, UMLResource> oclParser, List<IModelProperty> properties, UMLResource modelResource, IFile oclDocument) {
    StringBuilder s = new StringBuilder();
    HashMap<String, String> ctfpMap = new HashMap<String, String>();
    try {
      org.eclipse.ocl.uml.OCL ocl = org.eclipse.ocl.uml.OCL.newInstance();
      OCLHelper<Classifier, Operation, Property, Constraint> helper = ocl.createOCLHelper();	
      OclToEcl oclVisitor = OclToEcl.getInstance(modelSolver.getLogger());                
      List<Constraint> cList = oclParser.parseModelConstraints(modelResource, oclDocument);
      for (Constraint c : cList) {
        List<String> keywords = c.getKeywords();
        if (keywords != null)
          for (String keyword : keywords)
            if (!keyword.equalsIgnoreCase("precondition") && !keyword.equalsIgnoreCase("postcondition")) {
              ExpressionInOCL oclExpression = (ExpressionInOCL) c.getSpecification();
              
              insertQuantificationForSelf(helper, (Class)c.getConstrainedElements().get(0), oclExpression);
              
              s.append(oclExpression.accept(oclVisitor));
              ctfpMap.put(c.getName(), oclVisitor.getConstraintFirstPredicate());
              s.append("\n");                      
            }
      }
      LackOfConstraintsSubsumptionsModelProperty cSub = null;
      LackOfConstraintsRedundanciesModelProperty cRed = null;
      for(IModelProperty prop : properties) {
        if (prop instanceof LackOfConstraintsSubsumptionsModelProperty)
          cSub = (LackOfConstraintsSubsumptionsModelProperty) prop;
        if (prop instanceof LackOfConstraintsRedundanciesModelProperty)
          cRed = (LackOfConstraintsRedundanciesModelProperty) prop;
      }   
      if (cSub != null)
        for(String cNames : cSub.getTargetModelElementsNames()) {
          String[] nameList = cNames.split(",");
          s.append("noSubsumption");
          s.append(cNames.replace(",", ""));
          s.append("(Instances):- ");
          s.append("noConstraintSubsumption(Instances, "); 
          s.append(ctfpMap.get(nameList[0]));
          s.append(",");
          s.append(ctfpMap.get(nameList[1]));
          s.append(").\n");
        }
      if (cRed != null)
        for(String cNames : cRed.getTargetModelElementsNames()) {
          String[] nameList = cNames.split(",");
          s.append("noRedundancy");
          s.append(cNames.replace(",", ""));
          s.append("(Instances):- ");
          s.append("noConstraintRedundancy(Instances, "); 
          s.append(ctfpMap.get(nameList[0]));
          s.append(",");
          s.append(ctfpMap.get(nameList[1]));
          s.append(").\n");
        }
    }
    catch (Exception e) {
      e.printStackTrace();
      System.out.println(e.getMessage());
    }
    return s.toString();
  }

  @Override
  public String getCspCodeFileExtension() {
    return "ecl";
  }
  
  /**
   * Add quantification for self variable if required.
   * @param helper 
   * @param contextCls The context of this expression (i.e., the type of "self")
   * @param oclExpression The OCL expression to be extended
   * @throws ParserException
   */
  @SuppressWarnings("rawtypes")
  private void insertQuantificationForSelf(OCLHelper<Classifier, Operation, Property, Constraint> helper,
		Class contextCls, ExpressionInOCL oclExpression) throws ParserException {
	
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
  	}   

}