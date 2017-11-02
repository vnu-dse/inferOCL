package fr.irisa.triskell.alloy;

import java.io.IOException;
import java.util.Collections;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.xmi.impl.EcoreResourceFactoryImpl;

public class EMFHelper {

	public static EObject loadModel(String path) throws IOException{
		URI fileURI = URI.createFileURI(path);
		ResourceSet resourceSet = new ResourceSetImpl();
		resourceSet.getResourceFactoryRegistry().getExtensionToFactoryMap().put(
				    Resource.Factory.Registry.DEFAULT_EXTENSION, new EcoreResourceFactoryImpl());
		Resource resource = resourceSet.getResource(fileURI,true);
		resource.getContents().get(0);
		return resource.getContents().get(0);
	}
	
	public static String converAlloyInteToString(Integer inte){
		return inte.toString();
	}

	public static void save(EObject object,String path) throws IOException{
		URI fileURI = URI.createFileURI(path);
		System.out.println("saving to: "+fileURI);
		ResourceSet resourceSet=new ResourceSetImpl();
		resourceSet.getResourceFactoryRegistry().getExtensionToFactoryMap().put(
			    Resource.Factory.Registry.DEFAULT_EXTENSION, new EcoreResourceFactoryImpl());
		Resource resource = resourceSet.createResource(fileURI);
		resource.getContents().add(object);
		resource.save(Collections.EMPTY_MAP);
	}
}
