package fr.irisa.triskell.alloy;

import java.util.Hashtable;
import java.util.List;
import java.util.Set;

import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EEnum;
import org.eclipse.emf.ecore.EEnumLiteral;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.impl.DynamicEObjectImpl;

import edu.mit.csail.sdg.alloy4viz.AlloyAtom;
import edu.mit.csail.sdg.alloy4viz.AlloyInstance;
import edu.mit.csail.sdg.alloy4viz.AlloyModel;
import edu.mit.csail.sdg.alloy4viz.AlloyRelation;
import edu.mit.csail.sdg.alloy4viz.AlloyTuple;
import edu.mit.csail.sdg.alloy4viz.AlloyType;

public class AlloyToEMF {

	private EMFConverter converter;
	private AlloyInstance instance;
	private  Hashtable<String,EObject> elements;

	public AlloyToEMF(EMFConverter converter,AlloyInstance instance){
		this.converter=converter;
		this.instance=instance;
		this.elements=new Hashtable<String, EObject>();
	}
	
	public void convert(){
		AlloyModel model = this.instance.model;
		Set<AlloyType> types = model.getTypes();
		
		for(AlloyType t:types){
			List<AlloyAtom> atoms =  this.instance.type2atoms(t);
			
			
			
			if(t.getName().contains("VisibilityKind")){
				System.out.println("");
			}
			for(AlloyAtom atom:atoms){
				EObject type=converter.createTypeElement(t.getName(),atom.toString());
				if(type!=null){
					this.elements.put(atom.toString(), type);
					//System.out.println(" type: "+type.toString());
					//System.out.println("  |-> Atom: "+atom.toString());
				}
			}
			

			
			//System.out.println(" holi: "+t.toString());
		}
		for(AlloyRelation r:model.getRelations()){
				Set<AlloyTuple> tuples =  this.instance.relation2tuples(r);
				//System.out.println(" relation: "+r.getName());
				
				for(AlloyTuple tuple:tuples){
					AlloyAtom start=tuple.getStart();
					AlloyAtom end=tuple.getEnd();
					System.err.println(end.getType().toString());
					if(this.elements.containsKey(end.toString())){
						Object p=this.elements.get(end.getType().toString());
			/*			if(p instanceof DynamicEObjectImpl){
							Object f=((DynamicEObjectImpl)p).eClass();
							System.out.println("");
						}*/
						if(this.elements.get(end.getType().toString()) instanceof DynamicEObjectImpl){
							this.converter.createAttrElement(r.getName(), this.elements.get(start.toString()), this.elements.get(end.toString()));
						}
						else {
							if(r.getName().equals("next")||r.getName().equals("prev")){
								
							}
							else{
								String name=r.getName();
								String sstart=start.toString();
								String send=end.toString();
								System.err.println("ENV: "+name+" I :"+sstart+" E :"+send);
								this.converter.createAttrElement(r.getName(), this.elements.get(start.toString()), this.elements.get(end.toString()));
							}
							
						}
					}
					else{
						System.err.println(" tupe: "+tuple.toString());
							this.converter.createAttrElement(r.getName(), this.elements.get(start.toString()),AlloyTypesHelper.alloyToEcoreType(end));
					}
					//System.out.println(" tupe: "+tuple.toString());
				}
		}
	}
}
