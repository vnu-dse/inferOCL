/*
 * USE - UML based specification environment
 * Copyright (C) 1999-2004 Mark Richters, University of Bremen
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

// $Id: LogPanel.java 1050 2009-07-07 16:25:22Z lars $

package fr.inria.atlanmod.inferocl.gui;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

/** 
 * A Log panel with a scrollable text area.
 * 
 * @version     $ProjectVersion: 0.393 $
 * @author  Mark Richters
 */
@SuppressWarnings("serial")
public class LogPanel extends JPanel {
    private JTextArea fTextLog;
    private JPopupMenu fPopupMenu; // context menu on right mouse click

    public LogPanel() {
        setLayout(new BorderLayout());
        fTextLog = new JTextArea();
        fTextLog.setEditable(false);
        add(new JLabel(" Log "), BorderLayout.NORTH);
        add(new JScrollPane(fTextLog), BorderLayout.CENTER);

        // create the popup menu
        fPopupMenu = new JPopupMenu();
        JMenuItem mi = new JMenuItem("Clear");
        mi.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    clear();
                }});
        fPopupMenu.add(mi);
        fTextLog.addMouseListener(new PopupListener());
        fTextLog.setText(null);
    }

    public JTextArea getTextComponent() {
        return fTextLog;
    }
    
    public void setText(String str){
    	String tmp = fTextLog.getText();
    	if(tmp != null){
    		fTextLog.setText(tmp + "\n" + str);	
    	}else{
    		fTextLog.setText(str);
    	}
    	
    }

    /**
     * Clears the log.
     */
    public void clear() {
        fTextLog.setText(null);
    }

    class PopupListener extends MouseAdapter {
        public void mousePressed(MouseEvent e) {
            maybeShowPopup(e);
        }

        public void mouseReleased(MouseEvent e) {
            maybeShowPopup(e);
        }

        private void maybeShowPopup(MouseEvent e) {
            if (e.isPopupTrigger() ) {
                fPopupMenu.show(e.getComponent(), e.getX(), e.getY());
            }
        }
    }
}
