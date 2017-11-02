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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.uml2.uml.Association;
import org.eclipse.uml2.uml.AssociationClass;
import org.eclipse.uml2.uml.Class;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Package;
import org.eclipse.uml2.uml.Property;
import org.eclipse.uml2.uml.resource.UMLResource;

import fr.inria.atlanmod.emftocsp.IModelReader;
import fr.inria.atlanmod.inferocl.data.Invariant;

/**
 * @author duc-hanh.dang
 *
 */
public class FindExampleCspCode {	
	private IModelReader<UMLResource, Package, Class, Association, Property, Operation> modelReader;	 
	private List<Class> cList; 
	private List<String> cListNames; 
	private List<Association> asList;
	private List<String> asListNames;
	private List<Invariant> validINV;	 
	private Invariant invalidInv;
	private List<String> allLabeling; 
	private Map<String, String> elementsDomain;

	public FindExampleCspCode(IModelReader<UMLResource, Package, Class, Association, Property, Operation> modelReader, Map<String, String> elementsDomain, List<Invariant> validINV, Invariant invalidInv) {
		this.modelReader = modelReader;
		cList = modelReader.getClasses();
		asList = modelReader.getAssociations();
		cListNames = modelReader.getClassesNames();
		asListNames = modelReader.getAssociationsNames();		
		this.elementsDomain = elementsDomain;
		this.validINV = validINV;	
		this.invalidInv = invalidInv;
	}

	public String getCspCode() {   
		StringBuilder s = new StringBuilder();    
		try {
			//List<String> constraintsNames = GetOclParser().getModelConstraintsNames(GetModel(), getOclDocument());

			s.append(this.genHeaderSection());
			s.append("\n");
			s.append(this.genCardinalityDefinitionsSection());
			s.append("\n");
			s.append(this.genCardinalityConstraintsSection());
			s.append("\n");			
			s.append(this.genInstancesSection1());
			s.append("\n");
			s.append(this.genOclInvAndLabelingSection());
			s.append("\n");
			s.append(this.genCardinalityInstantiationSection());
			s.append("\n");			
			s.append(this.genObjectsCreationSection());
			s.append("\n");
			s.append(this.genLinksCreationSection());			
			s.append("\n\t");
			s.append(this.genInstancesSection2());						
			s.append("\n\t");
			s.append(this.genAllAttributesSection());							
			s.append("\n");      
			s.append(this.genClassCreationSection());
			s.append("\n");
			s.append(this.genAssociationCreationSection());
			s.append("\n");
		}
		catch (Exception e) {
			e.printStackTrace();
			System.out.println(e.getMessage());
		}
		return s.toString();
	}

	protected String genHeaderSection() {
		return "findExample(Instances):-\n";   
	}  

	protected String genCardinalityDefinitionsSection() {  
		StringBuilder s = new StringBuilder();
		String nameList = "";
		s.append("\t%Cardinality definitions\n\t");
		for (Class c : cList) {
			s.append("S");
			s.append(c.getName());
			nameList += "S" + c.getName() + ",";
			s.append("::");
			s.append(elementsDomain.get(c.getPackage().getName() + "." + c.getName()));
			s.append(", ");
		}
		s.append("\n\t");

		for (String asName : asListNames) {			
			if(asName.startsWith("AssocCls_")){    	  
				nameList += "S" + asName.substring(9) + ",";
				continue;
			}else{
				nameList += "S" + asName + ",";  
			}      
			s.append("S");
			s.append(asName);
			s.append("::");
			s.append(elementsDomain.get(asName));
			s.append(", ");
		}
		s.append("\n\t");
		s.append("CardVariables=[");
		s.append(nameList.substring(0, nameList.length() - 1));
		s.append("],\n\t");		
		return s.toString();
	}

	protected String genCardinalityConstraintsSection() {  
		StringBuilder s = new StringBuilder();
		s.append("\t%Cardinality constraints\n\t");
		for (Class c : cList) {
			List<Class> subTypes = modelReader.getClassSubtypes(cList, c);
			StringBuilder subTypeNames = new StringBuilder();
			if (subTypes != null) {
				for(Class subType : subTypes) { 
					subTypeNames.append(",");
					subTypeNames.append(subType.getName());
				}
				s.append("constraintsGen");
				s.append(c.getName());
				s.append(subTypeNames.toString().replace(",","")); 
				s.append("(S");
				s.append(c.getName());
				s.append(subTypeNames.toString().replace(",",", S"));  
				s.append("),\n\t");
			}
		}
		s.append("\n\t");
		for (String asName : asListNames) {
			s.append("constraints");
			s.append(asName);
			s.append("Card(CardVariables),\n\t");
		}
		return s.toString();    
	}

	protected String genCardinalityInstantiationSection() { 
		StringBuilder s = new StringBuilder();
		String labelCls, cardVars="";
		boolean ok = false;
		for(String cName:this.cListNames){
			if(cName.startsWith("AssocCls_")){
				labelCls = "S" + cName.substring(9);
			}else{
				labelCls = "S" + cName;
			}
			if(!this.allLabeling.contains(labelCls)){
				ok = true;
				cardVars = cardVars + "," + labelCls; 
			}
		}
		if(ok){			
			s.append("\t%Instantiation of remaining cardinality variables\n\t");			
			s.append("labeling([" + cardVars.substring(1) + "]),\n\t");
			return s.toString();
		}else{
			return "";
		}
		
	}

	protected String genObjectsCreationSection() {
		StringBuilder s = new StringBuilder();
		String cName,labelCls;
		s.append("\t%Object creation\n\t");    

		for (Class c : cList) {
			cName = c.getName();
			if(cName.startsWith("AssocCls_")){
				labelCls = "S" + cName.substring(9);
			}else{
				labelCls = "S" + cName;
			}
			if(!this.allLabeling.contains(labelCls)){				
				s.append(this.genObjectCreation(c));
			}
		}	    
    
		return s.toString();
	}

	protected String genLinksCreationSection() {
		StringBuilder s = new StringBuilder();		
		s.append("\t%Links creation\n\t");    

		for (Association as : asList) {
			if(!this.allLabeling.contains("P" + as.getName())){
				s.append(this.genLinkCreation(as));
			}
		}

		return s.toString(); 
	}

	protected String genInstancesSection1() {
		StringBuilder s = new StringBuilder();

		s.append("\tInstances = [");
		for (String cName : cListNames) {
			s.append("O");
			s.append(cName);
			s.append(", ");
		}
		for (String asName : asListNames) {
			s.append("L");
			s.append(asName);
			s.append(", ");
		}   
		s.deleteCharAt(s.length() - 2);
		s.append("],\n\t");
		return s.toString();
	}

	protected String genInstancesSection2() {
		StringBuilder s = new StringBuilder();
		for (String asName : asListNames) {
			s.append("cardinalityLinks");
			s.append(asName);
			s.append("(Instances),\n\t");
		} 
		return s.toString(); 
	}

	protected String genOclInvAndLabelingSection() {
		StringBuilder s = new StringBuilder();	
		
		int idx = 0;
		allLabeling = new ArrayList<String>();
		List<String> labelCls,labelLink,labelAttr;
		String tmpStr;
		s.append("%--OCL constraints-----\n\t");
		for(Invariant inv : validINV) {
			idx++;
			String patIdStr = inv.getPatternId();
			String patName = inv.getPatternName();
			String paraStr = inv.getMatchingPara();
			String firstChar = patName.substring(0, 1); 
			String firstCharLower = firstChar.toLowerCase();			
			labelCls = inv.getLabelCls();
			labelLink = inv.getLabelLink();
			labelAttr = inv.getLabelAttr();
			for(String cStr:labelCls){				
				if(cStr.startsWith("AssocCls_")){
					tmpStr = "S" + cStr.substring(9);
				}else{
					tmpStr = "S" + cStr;
				}
				if(!allLabeling.contains(tmpStr)){
					allLabeling.add(tmpStr);
					s.append("labeling([" + tmpStr + "]),\n\t");
					s.append(this.genObjectCreation(this.getClass(tmpStr.substring(1))));
				}				
			}
			for(String lStr:labelLink){
				if(allLabeling.contains("P" + lStr))
					continue;
				allLabeling.add("P" + lStr);
				if(lStr.startsWith("AssocCls_")){
					tmpStr = lStr.substring(9);
					if(!allLabeling.contains("S" + tmpStr)){
						allLabeling.add("S" + tmpStr);
						s.append("labeling([S" + tmpStr + "]),\n\t");
						s.append(this.genObjectCreation(this.getClass(tmpStr)));
					}
				}else{
					tmpStr = "S" + lStr;
					if(!allLabeling.contains(tmpStr)){
						allLabeling.add(tmpStr);
						s.append("labeling([" + tmpStr + "]),\n\t");						
					}
					s.append(this.genLinkCreation(this.getAssoc(lStr)));
				}													
				s.append("labeling(P" + lStr + "),\n\t");
			}
			for(String aStr:labelAttr){
				if(!allLabeling.contains("At" + aStr)){
					allLabeling.add("At" + aStr);
					s.append("labeling(At" + aStr + "),\n\t");
				}
			}
			s.append("Pat" + idx + "=" + patIdStr + ",\n\t");
			s.append("Para" + idx + "=" + paraStr + ",\n\t");
			s.append("getLocalPara(Pat" + idx + ",Para" + idx + ",LocalPara" + idx + "),\n\t");
			s.append(patName.replaceFirst(firstChar, firstCharLower));
			s.append("(Instances, LocalPara" + idx + ", 1),\n\n\t");				
		}
		if(invalidInv != null){
			String patIdStr = invalidInv.getPatternId();
			String patName = invalidInv.getPatternName();
			String paraStr = invalidInv.getMatchingPara();
			String firstChar = patName.substring(0, 1); 
			String firstCharLower = firstChar.toLowerCase();
			labelCls = invalidInv.getLabelCls();
			labelLink = invalidInv.getLabelLink();
			labelAttr = invalidInv.getLabelAttr();
			for(String cStr:labelCls){
				if(cStr.startsWith("AssocCls_")){
					tmpStr = "S" + cStr.substring(9);
				}else{
					tmpStr = "S" + cStr;
				}
				if(!allLabeling.contains(tmpStr)){
					allLabeling.add(tmpStr);
					s.append("labeling([" + tmpStr + "]),\n\t");
					s.append(this.genObjectCreation(this.getClass(tmpStr.substring(1))));
				}	
			}
			for(String lStr:labelLink){
				if(allLabeling.contains("P" + lStr))
					continue;
				allLabeling.add("P" + lStr);
				if(lStr.startsWith("AssocCls_")){
					tmpStr = lStr.substring(9);
					if(!allLabeling.contains("S" + tmpStr)){
						allLabeling.add("S" + tmpStr);
						s.append("labeling([S" + tmpStr + "]),\n\t");
						s.append(this.genObjectCreation(this.getClass(tmpStr)));
					}
				}else{
					tmpStr = "S" + lStr;
					if(!allLabeling.contains(tmpStr)){
						allLabeling.add(tmpStr);
						s.append("labeling([" + tmpStr + "]),\n\t");						
					}
					s.append(this.genLinkCreation(this.getAssoc(lStr)));
				}								
				s.append("labeling(P" + lStr + "),\n\t");				
			}
			for(String aStr:labelAttr){
				if(!allLabeling.contains(aStr)){
					allLabeling.add(aStr);
					s.append("labeling(At" + aStr + "),\n\t");
				}
			}
			s.append("Pat=" + patIdStr + ",\n\t");
			s.append("Para=" + paraStr + ",\n\t");
			s.append("getLocalPara(Pat,Para,LocalPara),\n\t");
			s.append(patName.replaceFirst(firstChar, firstCharLower));
			s.append("(Instances, LocalPara, 0),\n\n\t");		
		}		
		return s.toString();
	}
	
	private Class getClass(String clsName){
		for(Class c: this.cList){
			if(c.getName().equals(clsName))
				return c;
		}
		System.out.println("there is something wrong with choosing class name:" + clsName);
		return null;
	}
	
	private String genObjectCreation(Class c){
		if(c == null){			
			return "";
		}
		StringBuilder s = new StringBuilder();
		String cName = c.getName();
		
		if(c instanceof AssociationClass){			
			s.append("creationAssocCls_");
			s.append(cName);
			s.append("(O");
			s.append(c.getName());
			s.append(", LAssocCls_");
			s.append(cName);		
			s.append(", S");		
			s.append(cName);
			s.append(", S");
			s.append(modelReader.getBaseClass(c).getName());
			s.append(", PAssocCls_");
			s.append(cName);
			for(Property p : modelReader.getOwnedEnds((Association)c)) {
				s.append(", S");
				s.append(modelReader.getBaseClass((Class)p.getType()).getName());
			}		
			s.append(", At");
			s.append(cName);
			s.append("),\n\t");
		}else{
			s.append("creation");
			s.append(cName);
			s.append("(O");
			s.append(cName);
			s.append(", S");
			s.append(cName);
			s.append(", S");
			s.append(modelReader.getBaseClass(c).getName());
			s.append(", At");
			s.append(cName);
			s.append("),\n\t");
		}
		
		s.append("differentOids");
		s.append(cName);
		s.append("(O");
		s.append(cName);
		s.append("),\n\t");
		
		s.append("orderedInstances");
		s.append(cName);
		s.append("(O");
		s.append(cName);
		s.append("),\n\t");
		
		List<Class> subTypes = modelReader.getClassSubtypes(cList, c);
		if (subTypes != null) 
			for(Class subType : subTypes) { 
				s.append("existingOids");
				s.append(subType.getName());
				s.append("In");  
				s.append(c.getName());
				s.append("(O");
				s.append(subType.getName());
				s.append(", O");
				s.append(c.getName());
				s.append("),\n\t");
			}
		
		StringBuilder subTypeNames = new StringBuilder();
		if (subTypes != null && subTypes.size() > 0) {
			for(Class subType : subTypes) { 
				subTypeNames.append(", O");
				subTypeNames.append(subType.getName());
			}
			s.append("disjointInstances");
			s.append(subTypeNames.toString().replace(", O", ""));
			s.append("(");
			s.append(subTypeNames.toString().substring(2));
			s.append("),\n\t");
		}
	
		
		return s.toString();
	}
	
	private Association getAssoc(String assocName){
		for(Association assoc: this.asList){
			if(assoc.getName().equals(assocName))
				return assoc;
		}
		System.out.println("there is something wrong with get assoc: " + assocName);
		return null;
	}
	
	private String genLinkCreation(Association as){
		if(as == null){			
			return "";
		}
		StringBuilder s = new StringBuilder();
		String asName = modelReader.getAssociationName(as);
		
		if(!(as instanceof AssociationClass) ){
			s.append("creation");
			s.append(asName);
			s.append("(L");
			s.append(asName);
			s.append(", S");
			s.append(asName);
			s.append(", P");
			s.append(asName);
			for(Property p : modelReader.getOwnedEnds(as)) {
				s.append(", S");
				s.append(modelReader.getBaseClass((Class)p.getType()).getName());
			}
			s.append("),\n\t");
		}
		
		s.append("differentLinks");
		s.append("(L");
		s.append(asName);
		s.append("),\n\t");		    
		
		return s.toString();
	}

	protected String genAllAttributesSection() {
		StringBuilder s = new StringBuilder();

		s.append("AllAttributes = [");
		for (String asName : asListNames) {
			if(!this.allLabeling.contains("P" + asName)){
				s.append("P");
				s.append(asName);
				s.append(", ");
			}
		}     
		for (String cName : cListNames) {
			if(!this.allLabeling.contains("At" + cName)){
				s.append("At");
				s.append(cName);
				s.append(", ");
			}
		}    
		s.deleteCharAt(s.length() - 2);
		s.append("],\n\t");
		s.append("flatten(AllAttributes, Attributes),\n\t");
		s.append("labeling(Attributes).\n");

		return s.toString();    
	}

	protected String genClassCreationSection() {
		StringBuilder s = new StringBuilder();

		for (Class c : cList) {
			//hanhdd
			if(c instanceof AssociationClass){
				s.append( this.genAssocClassCreation( (AssociationClass)c ));
				continue;
			}
			s.append("creation");
			s.append(c.getName());
			if (c.getGeneralizations() != null && c.getGeneralizations().size() > 0) 
				s.append("(Instances, Size, MaxId, Attributes):-\n\t");
			else 
				s.append("(Instances, Size, _, Attributes):-\n\t");
			s.append("length(Instances, Size),\n\t");
			if (c.getGeneralizations() != null && c.getGeneralizations().size() > 0) {
				s.append("(foreach(Xi, Instances), fromto([],AtIn,AtOut,Attributes), param(MaxId) do\n\t\t");
				s.append("Xi=");
				s.append(c.getName().toLowerCase());
				s.append("{oid:Integer1");
			}
			else {
				s.append("(foreach(Xi, Instances), fromto([],AtIn,AtOut,Attributes), for(N, 1, Size) do\n\t\t");
				s.append("Xi=");
				s.append(c.getName().toLowerCase());
				s.append("{oid:N");
			}

			List<Property> pList = modelReader.getClassAttributes(c);
			int i = 1;
			for (Property p : pList) { 
				s.append(",");
				s.append(p.getName());
				s.append(":");
				s.append(p.getType().getName());
				s.append(++i);
			}
			if (c.getGeneralizations() != null && c.getGeneralizations().size() > 0)
				s.append("}, Integer1::1..MaxId, ");
			else
				s.append("}, ");
			i = 1;
			for (Property p : c.getAttributes()) { 
				s.append(p.getType().getName());
				s.append(++i);
				s.append("::");
				s.append(elementsDomain.get(c.getName() + "." + p.getName()));
				s.append(", ");
			}
			s.append("\n\t\t");

			if (c.getGeneralizations() != null && c.getGeneralizations().size() > 0)
				s.append("append([Integer1");
			else
				s.append("append([N");
			i = 1;
			for (Property p : c.getAttributes()) { 
				s.append(",");
				s.append(p.getType().getName());
				s.append(++i);
			}
			s.append("],AtIn, AtOut)).\n");
		}
		return s.toString();
	}	

	protected String genAssocClassCreation(AssociationClass cls) {
		//creationAssocCls_MutuallyExclusive(OInstances, LInstances, Size, _, Participants, SUser, SRole, Attributes):-
		StringBuilder ret = new StringBuilder();
		String clsName = cls.getName();
		ret.append("creationAssocCls_");		
		ret.append(clsName);
		ret.append("(OInstances,LInstances,Size,");

		if (cls.getGeneralizations() != null && cls.getGeneralizations().size() > 0) 
			ret.append("MaxId,Participants");
		else 
			ret.append("_,Participants");
		for(Property p : modelReader.getOwnedEnds(cls)) {
			ret.append(", S");
			ret.append(p.getType().getName());
		}
		ret.append(",Attributes):-\n\t");
		ret.append("length(OInstances, Size),\n\t");
		ret.append("length(LInstances, Size),\n\t");
		ret.append("(foreach(Xi,OInstances),foreach(Li,LInstances),fromto([],AtIn,AtOut,Attributes),");
		ret.append("fromto([],PIn,POut,Participants),");
		for(Property p : modelReader.getOwnedEnds(cls)) {
			ret.append("param(S");
			ret.append(p.getType().getName());
			ret.append("),");
		}		
		if (cls.getGeneralizations() != null && cls.getGeneralizations().size() > 0) {
			ret.append("param(MaxId) do\n\t\tLi=");			
		}else {
			ret.append("for(N, 1, Size) do\n\t\tLi=assoccls_");			
		}
		ret.append(clsName.toLowerCase());
		ret.append("{");
		StringBuilder vPart = new StringBuilder();
		int i = 1;
		for(Property p : modelReader.getOwnedEnds(cls)) {
			vPart.append(",");
			vPart.append(modelReader.getAssociationEndName(p));
			vPart.append(":ValuePart");
			vPart.append(i++);
		}      
		ret.append(vPart.toString().substring(1));
		ret.append("}");		
		i = 1;
		for(Property p : modelReader.getOwnedEnds(cls)) {
			ret.append(", ValuePart");
			ret.append(i);
			ret.append("#>0, ValuePart");
			ret.append(i);
			ret.append("#=<S");
			ret.append(p.getType().getName());
			i++;
		}      
		ret.append(",\n\t\tappend([ValuePart1,ValuePart2],PIn, POut),\n\t\tXi=");		
		ret.append(clsName.toLowerCase());

		if (cls.getGeneralizations() != null && cls.getGeneralizations().size() > 0) {
			ret.append("{oid:Integer1,");
		}else {
			ret.append("{oid:N,");
		}		
		ret.append(vPart.toString().substring(1));			
		List<Property> attrList = modelReader.getClassAttributes(cls);	
		i = 1;			
		for (Property p : attrList) {	
			ret.append(",");
			ret.append(p.getName());
			ret.append(":");
			ret.append(p.getType().getName());
			ret.append(++i);
		}
		if (cls.getGeneralizations() != null && cls.getGeneralizations().size() > 0)
			ret.append("}, Integer1::1..MaxId, ");
		else
			ret.append("}, ");
		i = 1;
		for (Property p : attrList) { 
			ret.append(p.getType().getName());
			ret.append(++i);
			ret.append("::");
			ret.append(elementsDomain.get(clsName + "." + p.getName()));
			ret.append(", ");
		}		
		ret.append("\n\t\t");

		if (cls.getGeneralizations() != null && cls.getGeneralizations().size() > 0)
			ret.append("append([Integer1,ValuePart1,ValuePart2");
		else
			ret.append("append([N,ValuePart1,ValuePart2");
		i = 1;
		for (Property p : attrList) {
			ret.append(",");
			ret.append(p.getType().getName());
			ret.append(++i);
		}
		ret.append("],AtIn, AtOut)).\n");

		return ret.toString();
	}

	protected String genAssociationCreationSection() {
		StringBuilder s = new StringBuilder();

		for (Association as : asList) {
			if(as instanceof AssociationClass)
				continue;
			String asName = modelReader.getAssociationName(as);
			s.append("creation");
			s.append(asName);
			s.append("(Instances, Size, Participants");
			for(Property p : modelReader.getOwnedEnds(as)) {
				s.append(", S");
				s.append(p.getType().getName());
			}
			s.append("):-\n\tlength(Instances, Size),\n\t(foreach(Xi, Instances), fromto([],AtIn,AtOut,Participants)");
			for(Property p : modelReader.getOwnedEnds(as)) {
				s.append(", param(S");
				s.append(p.getType().getName());
				s.append(")");
			}
			s.append(" do\n\t\tXi=");
			s.append(asName.toLowerCase());
			s.append("{");
			int i = 1;
			StringBuilder vPart = new StringBuilder();
			for(Property p : modelReader.getOwnedEnds(as)) {
				vPart.append(",");
				vPart.append(modelReader.getAssociationEndName(p));
				vPart.append(":ValuePart");
				vPart.append(i++);
			}
			s.append(vPart.toString().substring(1));
			s.append("}");
			i = 1;
			for(Property p : modelReader.getOwnedEnds(as)) {
				s.append(", ValuePart");
				s.append(i);
				s.append("#>0, ValuePart");
				s.append(i);
				s.append("#=<S");
				s.append(p.getType().getName());
				i++;
			}      
			s.append(",\n\t\tappend([");       // Check this
			for(i = 1; i <= modelReader.getOwnedEnds(as).size(); i++) {
				s.append("ValuePart");
				s.append(i);
				if (i != modelReader.getOwnedEnds(as).size())
					s.append(",");
			} 
			s.append("],AtIn, AtOut)).\n");
		} 
		return s.toString();
	}     
}