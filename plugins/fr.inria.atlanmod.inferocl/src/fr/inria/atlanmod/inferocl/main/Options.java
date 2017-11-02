/*
 * Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */

package fr.inria.atlanmod.inferocl.main;

import java.awt.Dimension;

/**
 * Global options for all packages.
 * @author duc-hanh.dang
 */
public class Options {

    // the release version
    public static final String RELEASE_VERSION = "0.0.9";

    // the copyright:
    public static final String COPYRIGHT = "Copyright (C) 2013-2015 Atlanmod/INRIA";
    /**
     * Encoding for xml-files.
     */
    public static final String ENCODING = "ISO-8859-1";
    
	private static String lastDirectory = System.getProperty("user.dir");
    
	public static String LINE_SEPARATOR = System.getProperty("line.separator");
    public static String FILE_SEPARATOR = System.getProperty("file.separator");

    //public static String eclipsePath = "/home/duc-hanh.dang/hanhdd/setup/eclipsepl";
    public static String eclipsePath = "/home/hanhdd/hanhdd/Setup/eclipsepl";    
    
	//public static String homeDir = "/home/duc-hanh.dang/hanhdd/workspace/workspace.inferOCL/inferOCL";
    public static String homeDir = "/home/hanhdd/hanhdd/workspace/workspace.inferOCL/inferOCL";
	
    public static String iconDir = homeDir + FILE_SEPARATOR + "images" + FILE_SEPARATOR;
    
    public static String libDir = homeDir + "/plugins/fr.inria.atlanmod.inferocl/libs";
    
    public static String resultDir = homeDir + "/tmp";
    //public static String resultDir = homeDir + "/serviceProvider";
    //public static String resultDir = homeDir + "/personExample";
    //public static String resultDir = homeDir + "/paperResearch";
    
    public static String oclFilePath = null;
    
    public static String graphvizPath = "";
    
	public static String URL_PREFIX = "file:" + FILE_SEPARATOR + FILE_SEPARATOR
			+ FILE_SEPARATOR;   
	
	//Messages
	
	public static String ModelWizardNavigation_0 = "Set the attributes domain and the cardinalities of the classes and associations";
	/**
     * Size of the diagram panel. 
     */
    public static Dimension fDiagramDimension = new Dimension( 400, 400 );   
      
    /** no instances */
	private Options() {}     
    	
    private static void setDimension( String width, String height ) {
        int dWidth = fDiagramDimension.width;
        int dHeight = fDiagramDimension.height;
                
        dWidth = Integer.parseInt( width );
        dHeight = Integer.parseInt( height );
        
        fDiagramDimension.setSize( dWidth, dHeight );
    }
    
    /**
	 * We always use the last directory for file choose operations
	 * @param string
	 */
	public static void setLastDirectory(String string) {
		lastDirectory = string;
	}
	
	/**
	 * We always use the last directory for file choose operations
	 */
	public static String getLastDirectory() {
		return lastDirectory;
	}
	
	public static void setResultDirectory(String path) {		
		resultDir = path;
	}
	
	public static void setOclFilePath(String path) {		
		oclFilePath = path;
	}

	public static String getOclFilePath() {		
		return oclFilePath;
	}
	
}