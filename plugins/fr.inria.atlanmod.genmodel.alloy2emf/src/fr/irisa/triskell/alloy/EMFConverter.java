package fr.irisa.triskell.alloy;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

import org.eclipse.emf.ecore.EAttribute;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EEnumLiteral;
import org.eclipse.emf.ecore.EFactory;
import org.eclipse.emf.ecore.ENamedElement;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.emf.ecore.EStructuralFeature;
import org.eclipse.emf.ecore.EcoreFactory;



public class EMFConverter {
	
	private static final boolean EAttribute = false;
	private  Hashtable<String,EObject> elements;
	private Hashtable<EObject,EObject> instances;
	private Hashtable<EObject,Hashtable<String,EObject>> featElements;
	private EPackage main;
	private EObject mainInstance;
	private String mainType;
	
	public EMFConverter(EPackage packages,String mainTypeName){
		this.elements=new Hashtable<String, EObject>();
		this.featElements= new  Hashtable<EObject, Hashtable<String,EObject>>();
		this.instances=new Hashtable<EObject, EObject>();
		this.indexPackage(packages);
		this.main=packages;
		this.mainType=mainTypeName;
	}
	
	public EObject createTypeElement(String meta,String element){
		
		
		EFactory gfactory=main.getEFactoryInstance();
		//System.out.println("meta="+meta);
		if(this.elements.containsKey(meta)){
			Object p=this.elements.get(meta);
			EObject object=null;
			if(p instanceof EClass){
				EClass identifier=(EClass) p;
				object=gfactory.create(identifier);
				this.instances.put(object, identifier);
			}
			else if(p instanceof EEnum){
				EEnum identifier=(EEnum) p;
				object=(EObject) gfactory.createFromString(identifier, element);
				this.instances.put(object, identifier);
			}

			if(this.mainType.equals(meta)){
				this.mainInstance=object;
			}
			return object;
		}	
		return null;
	}
	
	public EObject getMainOnstance(){
		return this.mainInstance;
	}
	public void createAttrElement(String meta,EObject metainstance,Object value){
		
		Object t=this.instances.get(metainstance);
		Object s=this.featElements.get(this.instances.get(metainstance));
		Object d=this.featElements.get(this.instances.get(metainstance)).get(meta);
		
		//System.out.println("meta estructure="+metainstance.eClass().getEStructuralFeature(meta).getName());
		
		if (metainstance.eClass().getEStructuralFeature(meta)!=null)
		{
		if( metainstance.eClass().getEStructuralFeature(meta).getUpperBound()==1){

			if(d instanceof EAttribute )
			{
				String className=((EAttribute)d).getEType().getInstanceClassName();
				if(className!=null){
					if(!value.getClass().getName().equals(className)&&className.equals("java.lang.String")&&value.getClass().getName().equals("java.lang.Integer")){
						value=EMFHelper.converAlloyInteToString((Integer) value);
					}
				}
			}
			//metainstance.eSet(this.featElements.get(this.instances.get(metainstance)).get(meta), value);
			metainstance.eSet((EStructuralFeature) this.featElements.get(this.instances.get(metainstance)).get(meta), value);
		}
		else{
			if(d instanceof EAttribute ){
				String className=((EAttribute)d).getEType().getInstanceClassName();
				//System.out.println("Class name="+className);
			}
			//((List)metainstance.eGet(this.featElements.get(this.instances.get(metainstance)).get(meta))).add(value);
			((List)metainstance.eGet((EStructuralFeature) this.featElements.get(this.instances.get(metainstance)).get(meta))).add(value);
		}
		}
	}
	
	private void indexPackage(EPackage packages){
		for(EClassifier clasi:packages.getEClassifiers()){
			boolean add=true;
			if(clasi instanceof EClass){
				if(((EClass)clasi).isAbstract()){
					add=false;
				}
				
			}
			if(add){
				this.elements.put(clasi.getName(), clasi);
			}
			this.indexClass(clasi);
		}
		for(EPackage pack:packages.getESubpackages()){
			this.elements.put(pack.getName(), pack);
		}
	}
	private void indexClass(EClassifier classi){
		
		Hashtable<String, EObject> tmpals=new Hashtable<String, EObject>();
		this.featElements.put(classi, tmpals);
			for(EObject t:	classi.eContents()){
				if(t instanceof EStructuralFeature){
					tmpals.put(((EStructuralFeature)t).getName(),(EStructuralFeature) t);
				}
				//System.out.println("class context: "+t.toString());
			}
			if(classi instanceof EClass){
				EClass classe=(EClass)classi;
				for(EClass supert:classe.getEAllSuperTypes()){
					for(EObject t:	supert.eContents()){
						if(t instanceof EStructuralFeature){
							tmpals.put(((EStructuralFeature)t).getName(),(EStructuralFeature) t);
						}
						//System.out.println("class context: "+t.toString());
					}
				}
			}
			else if(classi instanceof EEnum){
				EEnum tempEnum = EcoreFactory.eINSTANCE.createEEnum();
				tempEnum.setName(((EEnum) classi).getName());
				Object d=	((EEnum) classi).getDefaultValue();
				for(EEnumLiteral lit:((EEnum) classi).getELiterals()){
					EEnumLiteral lt=EcoreFactory.eINSTANCE.createEEnumLiteral();
					lt.setValue(lit.getValue());
					lt.setName(lit.getName());
					lt.setLiteral(lit.getLiteral());
					lt.setInstance(lit.getInstance());
					tempEnum.getELiterals().add(lt);
				}
				
				tmpals.put((tempEnum).getName(),classi);
			}
			else{
				//System.out.println("");
			}
	}
}
