/*
 * Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */

package fr.inria.atlanmod.inferocl.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.Event;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.BufferedReader;
import java.io.BufferedWriter;
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

import javax.swing.AbstractAction;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JDesktopPane;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JSplitPane;
import javax.swing.JToolBar;
import javax.swing.KeyStroke;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
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
import fr.inria.atlanmod.inferocl.main.Options;
import fr.inria.atlanmod.inferocl.util.ExtFileFilter;

/**
 * The main application window of InferOCL. 
 * @author duc-hanh.dang 
 */
@SuppressWarnings("serial")
public class MainWindow extends JFrame{      
    
	private LogPanel fLogPanel;

    private JDesktopPane fDesk;
    
    private ControlPanel fControl;    
    
    private ResultPanel fResult;

    private JSplitPane fLeftSplitPane;
    
    private JSplitPane fTopSplitPane;
    
	private JToolBar fToolBar;
	
	private JMenuBar fMenuBar;
	        	
    private static MainWindow fInstance; // global instance of main window
    
    private ActionFileOpenXmi fActionFileOpenXmi = new ActionFileOpenXmi();
    
    private ActionFileOpenSnapshot fActionFileOpenSnapshot = new ActionFileOpenSnapshot();
    
    private ActionHelpAbout fActionHelpAbout = new ActionHelpAbout();

	private IModelToCspSolver<UMLResource> modelSolver;    
	
	private ResourceSet rSet;

    private JButton addToToolBar(JToolBar toolBar, AbstractAction action,
            String toolTip) {
        JButton tb = toolBar.add(action);
        tb.setToolTipText(toolTip);
        tb.setText("");
        return tb;
    }
	
	public MainWindow() {
        super("Inference of Business Rules in OCL");        
        modelSolver = null;
		
        // create the menubar
		fMenuBar = new JMenuBar();
		getRootPane().setJMenuBar(fMenuBar);

        // `File' submenu
        JMenuItem mi;
        JMenu menu = new JMenu("File");
        menu.setMnemonic('F');
		fMenuBar.add(menu);
		mi = menu.add(fActionFileOpenXmi);
        mi.setAccelerator(KeyStroke
                .getKeyStroke(KeyEvent.VK_O, Event.CTRL_MASK));
        mi.setMnemonic('O');
        
        
        mi = menu.add(this.fActionFileOpenSnapshot);
        mi.setAccelerator(KeyStroke
                .getKeyStroke(KeyEvent.VK_H, Event.CTRL_MASK));
        mi.setMnemonic('H');
        
        // create the desktop
        fDesk = new JDesktopPane();
        fDesk.setDesktopManager(new ViewManager(this));
        
        // create the log panel
        fLogPanel = new LogPanel();
        
        // create the result panel
        fResult = new ResultPanel();
        
        // create the browser panel
		fControl = new ControlPanel((ViewManager) this.fDesk.getDesktopManager());
		
		// create toolbar
		fToolBar = new JToolBar();
		addToToolBar(fToolBar, fActionFileOpenXmi,  "Open model specification");
		addToToolBar(fToolBar, fActionFileOpenSnapshot,  "Open snapshot specification");
		//fToolBar.addSeparator();

        // put the three panels into split panes
        JSplitPane sp = new JSplitPane(JSplitPane.VERTICAL_SPLIT, fResult, fControl);
        sp.setDividerLocation(280);
        fLeftSplitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, sp, fDesk);
        fLeftSplitPane.setDividerLocation(250);
        fLeftSplitPane.setOneTouchExpandable(true);
        
        fTopSplitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT, fLeftSplitPane, fLogPanel);
        fTopSplitPane.setDividerLocation(460);
        fTopSplitPane.setOneTouchExpandable(true);
        // Layout and set the content pane
        JPanel contentPane = new JPanel();
        contentPane.setLayout(new BorderLayout());
        contentPane.setPreferredSize(new Dimension(800, 550));
        contentPane.add(fToolBar, BorderLayout.NORTH);
        contentPane.add(fTopSplitPane, BorderLayout.CENTER);        
        setContentPane(contentPane);

        addWindowListener(new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                close();
            }
        });

        setBounds(10, 20, 900, 700);		

		// `Help' submenu
		menu = new JMenu("Help");
		menu.setMnemonic('H');
		fMenuBar.add(menu);		
		mi = menu.add(fActionHelpAbout);
		mi.setMnemonic('A');
		
		this.rSet = new ResourceSetImpl();
        rSet.getResourceFactoryRegistry().getExtensionToFactoryMap().put("uml", new UMLResourceFactoryImpl());
        rSet.getPackageRegistry().put(UMLPackage.eNS_URI, UMLPackage.eINSTANCE);
        Map uriMap = rSet.getURIConverter().getURIMap();
        URI uri = URI.createURI("jar:file:" + Options.homeDir + "/libs/org.eclipse.uml2.uml.resources_4.0.2.v20130114-0902.jar!/");
        uriMap.put(URI.createURI(UMLResource.LIBRARIES_PATHMAP), uri.appendSegment("libraries").appendSegment(""));
        uriMap.put(URI.createURI(UMLResource.METAMODELS_PATHMAP), uri.appendSegment("metamodels").appendSegment(""));
        uriMap.put(URI.createURI(UMLResource.PROFILES_PATHMAP), uri.appendSegment("profiles").appendSegment(""));
    }

    /**
     * Returns the selected view of all internal views. If none is selected null
     * is returned.
     */
    public View getSelectedView() {
        if (fDesk.getSelectedFrame() != null) {
            return ((ViewFrame) fDesk.getSelectedFrame()).getView();
        }
        return null;
    }    
       
    private void close() {
        setVisible(false);
        dispose();	
    }

    /**
     * Returns the instance of MainWindow.
     */
    public static MainWindow instance() {
        return fInstance;
    }
    
    /**
     * Opens and compiles a specification file.
     */
    private class ActionFileOpenXmi extends AbstractAction {
        private JFileChooser fChooser;

        ActionFileOpenXmi() {
            super("Open xmi specification...", new ImageIcon(Options.iconDir
                    + "Open.gif"));
        }

        public void actionPerformed(ActionEvent e) {
            String path;
            // reuse chooser if possible
            if (fChooser == null) {
                path = Options.getLastDirectory();
                fChooser = new JFileChooser(path);
                ExtFileFilter filter = new ExtFileFilter("uml",
                        "Model specifications");
                fChooser.addChoosableFileFilter(filter);
                fChooser.setDialogTitle("Open specification");
            }
            int returnVal = fChooser.showOpenDialog(MainWindow.this);
            if (returnVal != JFileChooser.APPROVE_OPTION)
                return;

            path = fChooser.getCurrentDirectory().toString();
            Options.setLastDirectory(path);
            Options.setResultDirectory(path);
            File f = new File(path, fChooser.getSelectedFile().getName());
            URI modelFileURI = URI.createFileURI(f.getPath());
            
            EclipseSolver eclipseSolver = fControl.getEclipseSolver();
            
            if ( eclipseSolver == null){
            	eclipseSolver = new EclipseSolver(Options.eclipsePath, fLogPanel);
            	fControl.setEclipseSolver(eclipseSolver);
            }else{            	
            	fControl.reset();            	
            }
            
            //System.out.println(modelFileURI.toString());
            
            UMLResource r = (UMLResource) rSet.getResource(modelFileURI, true);
            
            IModelToCspSolverFactory<UMLResource> modelSolverFactory = new UmlModelToCspSolverFactory();
            
            modelSolver = modelSolverFactory.getModelToCspSolver(); 
            fControl.setModelSolver(modelSolver);
            modelSolver.setModelFileName(f.getName());
            modelSolver.setModel(r);
            initializeModelElementsDomain(modelSolver);            
            modelSolver.setModelProperties(new ArrayList<IModelProperty>());
            modelSolver.setCspCodeGenerator(new UmlToEclCodeGenerator(modelSolver));            
            try {            	
            	eclipseSolver.compile(getModelCspCode(), getImportLibs());
    		} catch (EclipseException | IOException | ProcessingException e1) {			
    			e1.printStackTrace();
    		}            
            fControl.resetSnapshot();
            fLogPanel.setText("Loading the Model ... Done!");
        }

    }  
    /**
     * Opens and compiles a snapshot specification file.
     */
    private class ActionFileOpenSnapshot extends AbstractAction {
        private JFileChooser fChooser;

        ActionFileOpenSnapshot() {
            super("Open snapshot specification...", new ImageIcon(Options.iconDir
                    + "Snapshot.gif"));
        }

        public void actionPerformed(ActionEvent e) {
            String path;
            if(modelSolver == null){
            	MessageBox dlg = new MessageBox(MainWindow.instance(),"Please load a model first!");
    			dlg.setVisible(true);
    			return;
            }
            // reuse chooser if possible
            if (fChooser == null) {
                path = Options.getLastDirectory();
                fChooser = new JFileChooser(path);
                ExtFileFilter filter = new ExtFileFilter("sna",
                        "Snapshot specifications");
                fChooser.addChoosableFileFilter(filter);
                fChooser.setDialogTitle("Open snapshot specification");
            }
            int returnVal = fChooser.showOpenDialog(MainWindow.this);
            if (returnVal != JFileChooser.APPROVE_OPTION)
                return;

            path = fChooser.getCurrentDirectory().toString();
            Options.setLastDirectory(path);
            File f = new File(path, fChooser.getSelectedFile().getName());
            BufferedReader readbuffer;
			try {
				StringBuilder str = new StringBuilder();
				String tmpStr;
				Boolean isValidSnapshot = true;
				readbuffer = new BufferedReader(new FileReader(f) );				 
				String strRead;				
				fControl.resetSnapshot();
				strRead = readbuffer.readLine();
				while(strRead != null){					
					strRead = strRead.trim();
					if(strRead != null && strRead.startsWith("[[") ){
						tmpStr = str.toString();
						if(!tmpStr.isEmpty() && tmpStr.charAt(tmpStr.length() - 1) == ','){
							tmpStr = tmpStr.substring(0, tmpStr.length() - 1);
						}
						if(! tmpStr.isEmpty()){
							fControl.addNewSnapshot(isValidSnapshot, tmpStr);
						}						
					}
					if(strRead != null & strRead.endsWith("{")){
						str = new StringBuilder();						
					}else if( strRead != null && !strRead.endsWith("}") & !strRead.isEmpty()){
						str.append(strRead);
					}else if(strRead != null && strRead.startsWith("}")){
						tmpStr = str.toString();
						fControl.addNewSnapshot(isValidSnapshot, tmpStr);
						if(isValidSnapshot){							
							isValidSnapshot = false;
						}
					}						
					strRead = readbuffer.readLine();
				}
				fControl.readyInferOCL();
			} catch (IOException e1) {
				fControl.readyInferOCL();				
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}			
        }
    }
    /**
     * to get the csp model file 
     * @throws ProcessingException 
     */
    public File getModelCspCode() throws ProcessingException{    
    	String cspCodeFileExtension = modelSolver.getCspCodeGenerator().getCspCodeFileExtension();
        String cspCodeFileName = modelSolver.getModelFileName() + "." + cspCodeFileExtension; //$NON-NLS-1$
        String path = Options.resultDir + Options.FILE_SEPARATOR;
        File cspCodeFile = new File( path + cspCodeFileName);
		fControl.getEclipseSolver().setFilePath(path + modelSolver.getModelFileName());
        String cspCode = modelSolver.getCspCodeGenerator().getCspCode();
        try {
    	    PrintWriter out = new PrintWriter(cspCodeFile);
    	    out.println(cspCode);
    	    out.flush();
    	    out.close();
    	    return cspCodeFile;
        } catch (IOException e) {
        	throw new ProcessingException(e);
        }
    }
    
    /**
     * to get list of imported ECL libs 
     */ 
    public List<File> getImportLibs(){ 
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
    	return libList;
    }        
    /**
     * Help about.
     */
    private class ActionHelpAbout extends AbstractAction {
        ActionHelpAbout() {
            super("About...");
        }

        public void actionPerformed(ActionEvent e) {
            AboutDialog dlg = new AboutDialog(MainWindow.this);
            dlg.setVisible(true);
        }
    }  
	/**
     * initialize the modelElementsDomain attribute for modelsolver
     */
	public void initializeModelElementsDomain(IModelToCspSolver<UMLResource> modelSolver) {
    	IModelReader<UMLResource, Package, Class, Association, Property, Operation> modelReader = (IModelReader<UMLResource, Package, Class, Association, Property, Operation>)modelSolver.getModelReader();   
    	List<Class> cList = (List<Class>) modelReader.getClasses();
    	Map<String, String> modelElementsDomain = new HashMap<String, String>();    	
		for (Class c : cList) {
    		modelElementsDomain.put(c.getPackage().getName() + "." + c.getName(), "0..10"); //$NON-NLS-1$ //$NON-NLS-2$
    		List<Property> atList = modelReader.getClassAttributes(c);
    		for (Property at : atList) 
    			if (at.getType() != null && "Boolean".equals(at.getType().getName())) //$NON-NLS-1$
    				modelElementsDomain.put(at.getClass_().getName() + "." + at.getName(), "0..1"); //$NON-NLS-1$ //$NON-NLS-2$
    			else if (at.getType() != null && "String".equals(at.getType().getName())){ //$NON-NLS-1$
    				modelElementsDomain.put(at.getClass_().getName() + "." + at.getName(), "[\"a\",\"b\",\"c\",\"d\",\"e\"]"); //$NON-NLS-1$ //$NON-NLS-2$
    			}
    			else
    				modelElementsDomain.put(at.getClass_().getName() + "." + at.getName(), "1..10"); //$NON-NLS-1$ //$NON-NLS-2$
    	}
    	List<String> asNames = modelReader.getAssociationsNames();
    	for (String asName : asNames) 
    		modelElementsDomain.put(asName, "0..10"); //$NON-NLS-1$

    	modelSolver.setModelElementsDomain(modelElementsDomain);    
    }
	/**
     * get the ResultPanel
     */
	//public void setResult(String text, int confidence, int gainedPoint) {
		//this.fResult.setResult(text, confidence, gainedPoint);
		
	//}
	
	public ResultPanel getResultPanel(){
		return this.fResult;
	}
	
	public JDesktopPane getDesk() {
		return fDesk;
		
	}
	public IModelToCspSolver<UMLResource> getModelSolver() {
		return this.modelSolver;		
	}
	public ControlPanel getControlPanel() {		
        return fControl;
    }
	
	public LogPanel getLogPanel() {
        return fLogPanel;
    }
	/**
     * Shows the log panel.
     */
    public void showLogPanel() {
        double loc = fTopSplitPane.getDividerLocation();
        // if divider is at bottom move it to top so that the log is visible
        if (loc / (fTopSplitPane.getHeight() - fTopSplitPane.getDividerSize()) > 0.95)
            fTopSplitPane.setDividerLocation(0.75);
    }
}