package fr.irisa.triskell.alloy;

import com.sun.org.apache.bcel.internal.generic.NEW;

import edu.mit.csail.sdg.alloy4viz.AlloyAtom;

public class AlloyTypesHelper{
	
	public static String alloyBoolTRUE="Bool/True";
	public static String alloyBoolFalse="Bool/False";
	public static String alloyInt="Int";
	public static String alloySeqInt="seq/Int";
	public static String alloyString="String/";
	public static String alloySecondString="fun/String";
	public static Object alloyToEcoreType(AlloyAtom atom){
		if(atom.getType().getName().equals(AlloyTypesHelper.alloyBoolTRUE)){
			return new Boolean(true);
		}
		else if(atom.getType().getName().equals(AlloyTypesHelper.alloyBoolFalse)){
			return new Boolean(false);
		}
		else if(atom.getType().getName().equals(AlloyTypesHelper.alloyInt)||atom.getType().getName().equals(AlloyTypesHelper.alloySeqInt)){
			String inte=atom.toString();
			return new Integer(Integer.valueOf(inte));
		}
		else if(atom.getType().getName().startsWith(AlloyTypesHelper.alloyString)){
			return new String();
		}
		else if(atom.getType().getName().startsWith(AlloyTypesHelper.alloySecondString)){
			return new String();
		}
		else{
			//System.out.println("?");
		}
		return null;
	}
}
