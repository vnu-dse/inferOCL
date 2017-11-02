package fr.inria.atlanmod.inferocl.main;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.ocl.uml.OCL;
import org.eclipse.uml2.uml.Association;
import org.eclipse.uml2.uml.Class;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Package;
import org.eclipse.uml2.uml.Property;
import org.eclipse.uml2.uml.UMLPackage;
import org.eclipse.uml2.uml.internal.resource.UMLResourceFactoryImpl;
import org.eclipse.uml2.uml.resource.UMLResource;

import com.parctechnologies.eclipse.EclipseException;

import fr.inria.atlanmod.emftocsp.IModelProperty;
import fr.inria.atlanmod.emftocsp.IModelReader;
import fr.inria.atlanmod.emftocsp.IModelToCspSolver;
import fr.inria.atlanmod.emftocsp.IModelToCspSolverFactory;
import fr.inria.atlanmod.emftocsp.ProcessingException;
import fr.inria.atlanmod.emftocsp.uml.impl.UmlModelToCspSolverFactory;
import fr.inria.atlanmod.emftocsp.umltoecl.UmlToEclCodeGenerator;
import fr.inria.atlanmod.inferocl.csp.EclipseSolver;
import fr.inria.atlanmod.inferocl.data.Invariant;
import fr.inria.atlanmod.inferocl.gui.MainWindow;

public class Emf2Csp {

	public static void main(String[] args) {
		String workingPath = "/home/duc-hanh.dang/Dropbox/hanhdd/Inria/2014_reasoningConstraintPatterns/implementation/";
		String umlFileName = "course.uml";
		String umlFilePath = workingPath + umlFileName;
		String oclFilePath = workingPath + "test.ocl";
		//String oclFilePath = workingPath + "course_emf2csp.ocl";
		//String oclFilePath = workingPath + "course.ocl";		
		String domainSpecFilePath = workingPath + "domainSpec.txt";

		Options.setOclFilePath(oclFilePath);

		EclipseSolver eclipseSolver = new EclipseSolver(Options.eclipsePath, null);

		IModelToCspSolver<UMLResource> modelSolver;
		ResourceSet rSet;

		rSet = new ResourceSetImpl();
		rSet.getResourceFactoryRegistry().getExtensionToFactoryMap().put("uml", new UMLResourceFactoryImpl());
		rSet.getPackageRegistry().put(UMLPackage.eNS_URI, UMLPackage.eINSTANCE);
		Map uriMap = rSet.getURIConverter().getURIMap();
		URI uri = URI.createURI("jar:file:" + Options.homeDir + "/libs/org.eclipse.uml2.uml.resources_4.0.2.v20130114-0902.jar!/");
		uriMap.put(URI.createURI(UMLResource.LIBRARIES_PATHMAP), uri.appendSegment("libraries").appendSegment(""));
		uriMap.put(URI.createURI(UMLResource.METAMODELS_PATHMAP), uri.appendSegment("metamodels").appendSegment(""));
		uriMap.put(URI.createURI(UMLResource.PROFILES_PATHMAP), uri.appendSegment("profiles").appendSegment(""));

		OCL.initialize(rSet); 

		URI modelFileURI = URI.createFileURI(umlFilePath);

		UMLResource r = (UMLResource) rSet.getResource(modelFileURI, true);

		IModelToCspSolverFactory<UMLResource> modelSolverFactory = new UmlModelToCspSolverFactory();

		modelSolver = modelSolverFactory.getModelToCspSolver();        
		modelSolver.setModelFileName(umlFileName);
		modelSolver.setModel(r);                    
		modelSolver.setModelProperties(new ArrayList<IModelProperty>());
		modelSolver.setCspCodeGenerator(new UmlToEclCodeGenerator(modelSolver));

		File domainSpecFile = new File( domainSpecFilePath );
		PrintWriter domainWriter;
		try {
			//***domainWriter = new PrintWriter(domainSpecFile);			
			BufferedReader domainReader = new BufferedReader(new FileReader(domainSpecFile) );
			String readLine;
			String[] fieldsOnALine;
			Map<String, String> modelElementsDomain = new HashMap<String, String>();
			IModelReader<UMLResource, Package, Class, Association, Property, Operation> modelReader = (IModelReader<UMLResource, Package, Class, Association, Property, Operation>)modelSolver.getModelReader();   
			List<Class> cList = (List<Class>) modelReader.getClasses();
			for (Class c : cList) {
				//***modelElementsDomain.put(c.getPackage().getName() + "." + c.getName(), "0..10"); //$NON-NLS-1$ //$NON-NLS-2$
				//***domainWriter.println(c.getPackage().getName() + "." + c.getName() + ":\t0..10" );
				readLine = domainReader.readLine().trim();
				while("".equals(readLine)){
					readLine = domainReader.readLine().trim();
				}
				fieldsOnALine = readLine.split("\\t+");
				modelElementsDomain.put(c.getPackage().getName() + "." + c.getName(), fieldsOnALine[1]); //$NON-NLS-1$ //$NON-NLS-2$

				List<Property> atList = modelReader.getClassAttributes(c);
				for (Property at : atList) 
					if (at.getType() != null && "Boolean".equals(at.getType().getName())){ //$NON-NLS-1$
						//***modelElementsDomain.put(at.getClass_().getName() + "." + at.getName(), "0..1"); //$NON-NLS-1$ //$NON-NLS-2$
						//***domainWriter.println(at.getClass_().getName() + "." + at.getName() + ":\t0..1");
						readLine = domainReader.readLine().trim();
						while("".equals(readLine)){
							readLine = domainReader.readLine().trim();
						}
						fieldsOnALine = readLine.split("\\t+");
						modelElementsDomain.put(at.getClass_().getName() + "." + at.getName(), fieldsOnALine[1]); //$NON-NLS-1$ //$NON-NLS-2$

					}else if (at.getType() != null && "String".equals(at.getType().getName())){ //$NON-NLS-1$
						//***modelElementsDomain.put(at.getClass_().getName() + "." + at.getName(), "[\"a\",\"b\",\"c\",\"d\",\"e\"]"); //$NON-NLS-1$ //$NON-NLS-2$
						//***domainWriter.println(at.getClass_().getName() + "." + at.getName() + ":\t[\"a\",\"b\",\"c\",\"d\",\"e\"]");
						readLine = domainReader.readLine().trim();
						while("".equals(readLine)){
							readLine = domainReader.readLine().trim();
						}
						fieldsOnALine = readLine.split("\\t+");
						modelElementsDomain.put(at.getClass_().getName() + "." + at.getName() + ".length", fieldsOnALine[1]); //$NON-NLS-1$ //$NON-NLS-2$
						if(fieldsOnALine.length > 2){
							modelElementsDomain.put(at.getClass_().getName() + "." + at.getName() + ".domain", fieldsOnALine[2]); //$NON-NLS-1$ //$NON-NLS-2$
						}else{
							modelElementsDomain.put(at.getClass_().getName() + "." + at.getName() + ".domain", "");
						}
					}else{
						//***modelElementsDomain.put(at.getClass_().getName() + "." + at.getName(), "1..10"); //$NON-NLS-1$ //$NON-NLS-2$
						//***domainWriter.println(at.getClass_().getName() + "." + at.getName() + ":\t1..10");
						readLine = domainReader.readLine().trim();
						while("".equals(readLine)){
							readLine = domainReader.readLine().trim();
						}
						fieldsOnALine = readLine.split("\\t+");
						modelElementsDomain.put(at.getClass_().getName() + "." + at.getName(), fieldsOnALine[1]); //$NON-NLS-1$ //$NON-NLS-2$
					}
			}
			List<String> asNames = modelReader.getAssociationsNames();
			for (String asName : asNames){ 
				//***modelElementsDomain.put(asName, "0..10"); //$NON-NLS-1$
				//***domainWriter.println(asName + ":\t0..10");
				readLine = domainReader.readLine().trim();
				while("".equals(readLine)){
					readLine = domainReader.readLine().trim();
				}
				fieldsOnALine = readLine.split("\\t+");
				modelElementsDomain.put(asName, fieldsOnALine[1]); //$NON-NLS-1$
			}

			modelSolver.setModelElementsDomain(modelElementsDomain);
			//***domainWriter.flush();
			//***domainWriter.close();
			domainReader.close();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		File importsFolder = new File(Options.libDir);    	
		File[] libs = importsFolder.listFiles(
				new FilenameFilter() {
					public boolean accept(File dir, String name) {    
						return name.matches(".*\\.ecl$");  //$NON-NLS-1$
					}
				}
				);
		ArrayList<File> libList = new ArrayList<File>();        
		for(File lib: libs){
			libList.add(lib);
		}

		String cspCodeFileName = modelSolver.getModelFileName() + ".ecl";        
		File cspCodeFile = new File( workingPath + cspCodeFileName);		
		String cspCode;
		try {
			cspCode = modelSolver.getCspCodeGenerator().getCspCode();
			PrintWriter out = new PrintWriter(cspCodeFile);
			out.println(cspCode);
			out.flush();
			out.close();
			eclipseSolver.compile(cspCodeFile, libList);
		} catch (IOException | ProcessingException | EclipseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

}