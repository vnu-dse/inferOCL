package fr.irisa.triskell.alloy;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.LinkedList;

import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EPackage;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4viz.AlloyInstance;
import edu.mit.csail.sdg.alloy4viz.StaticInstanceReader;

public class LaunchAlloyInstance2XMI {
	public static void main(String[] args) {
		LinkedList<String> files=new LinkedList<String>();
		String root = new String("/Users/sagarsen/Desktop/CartierDemo/demoSpace/Cartier");
		System.out.println("Transforming Alloy XML to XMI...");
		File dir = new File(root+"/Temp/alloySolutions");
	    
	    String[] children = dir.list();
	    
	 // It is also possible to filter the list of returned files.
	    // This example does not return any files that start with `.'.
	    FilenameFilter filter = new FilenameFilter() {
	        public boolean accept(File dir, String name) {
	            return !name.startsWith(".");
	        }
	    };
	    children = dir.list(filter);
	    
	    if (children == null) {
	        // Either dir does not exist or is not a directory
	    } else {
	        for (int i=0; i<children.length; i++) {
	            // Get filename of file or directory
	            String filename = children[i];
	            files.add(root+"/Temp/alloySolutions/"+filename);
	        }
	    }
	    
	   
		String strdest=root+"/Temp/xmiSolutions";
		int j=0;
		for(String file:files){
			File xmlFile=new File(file);
			XMLNode xml;
			AlloyInstance result;
			try {
				EPackage obj=(EPackage) EMFHelper.loadModel(root+"/Temp/currentMetaModel/current.ecore");
				/*for(EClassifier clasi:obj.getEClassifiers()){
					System.out.println("eclass: "+clasi.toString());
				}*/
				//Set the root package
				EMFConverter converter=new EMFConverter(obj,"ClassModel");
				if (args.length==0)
				{
				System.out.println("Top-level class not specified in argument.");
				
				}
				if (args.length==1)
				{
				System.out.println("Top-level class specified. Value ="+args[1]);
				converter=new EMFConverter(obj,"ClassModel");
				}
				result = StaticInstanceReader.parseInstance(xmlFile);

				AlloyToEMF alloy2emf=new AlloyToEMF(converter,result);

				alloy2emf.convert();
				EObject t=converter.getMainOnstance();
				String outputFileName = new String(file.split("/")[file.split("/").length-1].toString());
				outputFileName=outputFileName.substring(0,outputFileName.length()-4);
				System.out.println(outputFileName);
				EMFHelper.save(t, strdest+"/"+outputFileName+".xmi");
				System.out.println("Finish");
				j++;
			} catch (Err e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
	}
}
