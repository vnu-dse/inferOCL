/*
 * Copyright (c) 2013 INRIA Rennes Bretagne-Atlantique. 
 */

package fr.inria.atlanmod.inferocl.gui;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;

import fr.inria.atlanmod.inferocl.main.Options;

/** 
 * About dialog.
 * 
 * @author duc-hanh.dang
 */
@SuppressWarnings("serial")
class AboutDialog extends JDialog {

    AboutDialog(JFrame parent) {
        super(parent, "About");

        JPanel logoBox = new JPanel();
        logoBox.setLayout(new BoxLayout(logoBox, BoxLayout.Y_AXIS));
        //logoBox.setBackground(new Color(0xe0, 0xe0, 0xff));
        //logoBox.add(new JLabel(new ImageIcon(Options.iconDir + "use1.gif")));
        logoBox.setBorder(BorderFactory.createEmptyBorder(0, 5, 0, 5));

        JPanel infoBox = new JPanel();
        infoBox.setLayout(new BoxLayout(infoBox, BoxLayout.Y_AXIS));
        //infoBox.setBackground(Color.white);
        infoBox.setBorder(BorderFactory.createEmptyBorder(0, 5, 0, 5));
        JLabel l = line("INFEROCL - Inference of Business Rules in OCL");
        l.setFont(l.getFont().deriveFont(Font.BOLD));
        infoBox.add(l);
          
        infoBox.add(line(Options.COPYRIGHT));
        //infoBox.add(line("Version " + Options.RELEASE_VERSION));
        //infoBox.add(line("For more information see:"));
        //infoBox.add(line("http://www.inria.fr"));
        infoBox.add(Box.createRigidArea(new Dimension(0,5)));
        infoBox.add(line("This program is free software; you can redistribute it and/or"));
        infoBox.add(line("modify it under the terms of the GNU General Public License as"));
        infoBox.add(line("published by the Free Software Foundation; either version 2 of the"));
        infoBox.add(line("License, or (at your option) any later version."));
        infoBox.add(Box.createRigidArea(new Dimension(0,5)));
        infoBox.add(line("This program is distributed in the hope that it will be useful, but"));
        infoBox.add(line("WITHOUT ANY WARRANTY; without even the implied warranty of"));
        infoBox.add(line("MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE."));
        infoBox.add(line("See the GNU General Public License for more details."));
        infoBox.add(Box.createRigidArea(new Dimension(0,5)));


        // add close button
        Box btnBox = Box.createHorizontalBox();
        JButton closeBtn = new JButton("Close");
        btnBox.add(Box.createGlue());
        btnBox.add(closeBtn);
        btnBox.add(Box.createGlue());
        closeBtn.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent ev) {
                    setVisible(false);
                    dispose();
                }
            });

        // Layout and set the content pane
        JPanel contentPane = new JPanel();
        contentPane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        contentPane.setLayout(new BorderLayout());
        contentPane.add(logoBox, BorderLayout.WEST);
        contentPane.add(infoBox, BorderLayout.CENTER);
        contentPane.add(btnBox, BorderLayout.SOUTH);
        setContentPane(contentPane);
        getRootPane().setDefaultButton(closeBtn);

        // allow dialog close on escape key
        //CloseOnEscapeKeyListener ekl = new CloseOnEscapeKeyListener(this);
        //addKeyListener(ekl);

        pack();
        //setSize(getSize());   // hack for layout bug with fvwm2
        setLocationRelativeTo(parent);
        closeBtn.requestFocus();
    }

    private JLabel line(String s) {
        JLabel l = new JLabel(s);
        l.setForeground(Color.black);
        return l;
    }
}