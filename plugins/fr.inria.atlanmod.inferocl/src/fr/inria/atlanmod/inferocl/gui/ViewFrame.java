/*
 * Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */

package fr.inria.atlanmod.inferocl.gui;

import java.awt.print.PageFormat;
import javax.swing.ImageIcon;
import javax.swing.JInternalFrame;

import fr.inria.atlanmod.inferocl.main.Options;

/** 
 * @author duc-hanh.dang
 */
@SuppressWarnings("serial")
public class ViewFrame extends JInternalFrame {
    private View fView;

    public ViewFrame(String title, View view, String iconFilename) {
        super(title, true, true, true, true);
        fView = view;
        setFrameIcon(new ImageIcon(Options.iconDir + iconFilename));
    }

    void close() {
        fView.detachModel();
    }
    
    /**
     * Returns the view of this ViewFrame.
     */
    public View getView() {
        return fView;
    }
}