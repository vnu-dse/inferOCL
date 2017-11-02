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
package fr.inria.atlanmod.emftocsp.uml.impl;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.uml2.uml.Association;
import org.eclipse.uml2.uml.AssociationClass;
import org.eclipse.uml2.uml.Class;
import org.eclipse.uml2.uml.Generalization;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Package;
import org.eclipse.uml2.uml.PackageableElement;
import org.eclipse.uml2.uml.Property;
import org.eclipse.uml2.uml.UMLPackage;
import org.eclipse.uml2.uml.resource.UMLResource;



import fr.inria.atlanmod.emftocsp.IModelReader;

/**
 * @author <a href="mailto:carlos.gonzalez@inria.fr">Carlos A. Gonz�lez</a>
 *
 */
public class UmlModelReader implements IModelReader<UMLResource, Package, Class, Association, Property, Operation> {
	UMLResource r;

	public UmlModelReader(UMLResource r) {
		this.r = r;
	}

	@Override
	public UMLResource getModelResource() {
		return r;
	}

	@Override
	public List<Package> getPackages() {		
		ArrayList<Package> pList = new ArrayList<Package>();
		if (r.getContents() != null)
			for (EObject obj : r.getContents()) 
				if (obj instanceof Package) {
					pList.add((Package)obj);
				}
		return pList;
	}

	private List<Class> getClassesFromPackage(Package p) {
		ArrayList<Class> cList = new ArrayList<Class>();
		if (p.getPackagedElements() != null)
			for (PackageableElement pkgElement : p.getPackagedElements())
				if (pkgElement instanceof Class){
					cList.add((Class)pkgElement);          
				}
		return cList;
	}

	@Override
	public List<Class> getClasses() {
		List<Package> pList = getPackages();
		ArrayList<Class> cList = new ArrayList<Class>();          
		for(Package p : pList) 
			cList.addAll(getClassesFromPackage(p));
		return cList;
	}

	@Override
	public List<String> getClassesNames() {
		List<Class> cList = getClasses();
		ArrayList<String> names = new ArrayList<String>();
		for(Class c : cList)
			names.add(c.getName());	  
		return names;
	}	

	@Override
	public List<Property> getClassAttributes(Class c) {
		//hanhdd
		List<Property> ret;
		if( c instanceof AssociationClass){
			List<Property> assocEnds = this.getOwnedEnds((Association) c);
			ret = new ArrayList<Property>();
			for(Property p:c.getAllAttributes()){
				if(!assocEnds.contains(p)){
					ret.add(p);
				}
			}			
			/*List<Property> assocEnds = ( (AssociationClass)c).getOwnedEnds();
			if(assocEnds.size() == ( (AssociationClass)c).getAllAttributes().size()){
				ret = assocEnds;
				ret.addAll(c.getAttributes());				
			}
			else{			  
				//ret = new ArrayList<Property>();			  
				//ret.addAll(this.getOwnedEnds((Association) c));
				//ret.addAll(c.getAttributes());
				ret = c.getAttributes();
			}*/
		}else{
			ret = c.getAttributes();
		}	  
		return ret;
	}



	@Override
	public List<Operation> getClassOperations(Class c) {
		return c.getOperations();
	}

	@Override
	public List<Class> getClassSubtypes(List<Class> classList, Class c) {
		ArrayList<Class> subTypesList = new ArrayList<Class>();          
		if (classList != null) {
			for (Class cl : classList) {
				for (Generalization g : cl.getGeneralizations()) {
					if ((Class)g.getGeneral() == c)
						subTypesList.add(cl);
				}
			}
		}
		return subTypesList.size() > 0 ? subTypesList : null;
	}

	@Override
	public Class getBaseClass(Class c) {
		if (c.getGeneralizations() == null || (c.getGeneralizations() != null && c.getGeneralizations().size() == 0))
			return c;
		if (c.getGeneralizations().size() > 1)
			return null;
		return (Class)c.getGeneralizations().get(0).getGeneral();
	} 

	@Override
	public List<Association> getAssociations() {
		List<Package> pList = getPackages();
		ArrayList<Association> asList = new ArrayList<Association>();
		for(Package p : pList) 
			asList.addAll(getAssociationListFromPackage(p));
		return asList;
	}

	@Override
	public List<String> getAssociationsNames() {
		List<Association> aList = getAssociations();
		ArrayList<String> names = new ArrayList<String>();
		for(Association as : aList)
			names.add(getAssociationName(as));   
		return names;
	}

	@Override  
	public String getAssociationName(Association as) {
		String ret; 
		if (as.getName() != "" && as.getName() != null){ //$NON-NLS-1$
			ret = as.getName();
		}else{
			String asName = ""; //$NON-NLS-1$
			for(Property asEnd : as.getOwnedEnds())
				asName += getAssociationEndName(asEnd) + "_"; //$NON-NLS-1$
			ret = asName.substring(0, asName.length() - 1);
		}
		//hanhdd
		if(as instanceof AssociationClass){
			ret = "AssocCls_" + ret;
		}
		return ret;
	}  

	@Override
	public String getAssociationEndName(Property asEnd) {
		if (asEnd.getName() != "" && asEnd.getName() != null) //$NON-NLS-1$
			return asEnd.getName();
		if (asEnd.getType().getName() != null && asEnd.getType().getName() != "") //$NON-NLS-1$
			return asEnd.getType().getName();    
		return "unamedAssociationEnd"; //$NON-NLS-1$
	}

	public List<Property> getOwnedEnds(Association assoc){
		//hanhdd
		//FIXME: in case as is an association class, only two first attributes are taken! 
		//(since currently, Association::getOwnedEnds() is incorrect

		if(assoc instanceof AssociationClass){
			List<Property> assocEnds = ( (AssociationClass)assoc).getOwnedEnds();
			if(assocEnds.size() == ( (AssociationClass)assoc).getAllAttributes().size()){			  
				return assocEnds.subList(0, 2);
			}
			/*else{			  
				List<Property> ret = new ArrayList<Property>();
				for( Property p: ( (AssociationClass)assoc).getAllAttributes() ){
					if(!assocEnds.contains(p)){
						ret.add(p);
					}
				}
				return ret;
			}*/
			return assocEnds;
		}else{
			return assoc.getOwnedEnds();
		}
	}

	private ArrayList<Association> getAssociationListFromPackage(Package p) {
		ArrayList<Association> asList = new ArrayList<Association>();
		for (PackageableElement pkgElement : p.getPackagedElements())      	
			if ( (pkgElement instanceof Association) ) //&& ! (pkgElement instanceof Class) ) 
				asList.add((Association)pkgElement);
		return asList;
	}

	public static  void main(String[] args){
		//System.out.println(UMLResource.FILE_EXTENSION);
		String fileName ="PersonCar.uml";
		String path = "/home/duc-hanh.dang/Dropbox/workspace/inferOCL/example/PersonDepartment.uml";
		URI modelFileURI = URI.createFileURI(path); 
		ResourceSet rSet = new ResourceSetImpl();	  
		rSet.getResourceFactoryRegistry().getExtensionToFactoryMap().put("uml", UMLResource.Factory.INSTANCE);

		rSet.getPackageRegistry().put(UMLPackage.eNS_URI, UMLPackage.eINSTANCE);

		UMLResource r = (UMLResource)rSet.getResource(modelFileURI, true);

		for (EObject obj : r.getContents()){    	  
			System.out.println(obj);
			if (obj instanceof org.eclipse.uml2.uml.Package) {
				System.out.println(obj.toString());
			}else{
				System.out.println("Ko phai package");
			}
		}

		// UmlModelReader umlReader = new UmlModelReader(r);

		/*
       ICspSolver solver = new EclipseSolver(Options.eclipsePath, Options.graphvizPath);
       IModelToCspSolverFactory<UMLResource> modelSolverFactory = new UmlModelToCspSolverFactory();     
      IModelToCspSolver<UMLResource> modelSolver = modelSolverFactory.getModelToCspSolver(); 
      modelSolver.setModelFileName(fileName);
      modelSolver.setModel(r);
      modelSolver.setSolver(solver);
      modelSolver.setCspCodeGenerator(new UmlToEclCodeGenerator(modelSolver));
      try {
			System.out.println( modelSolver.getCspCodeGenerator().getCspCode() );
		} catch (ProcessingException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		 */

	}
}
