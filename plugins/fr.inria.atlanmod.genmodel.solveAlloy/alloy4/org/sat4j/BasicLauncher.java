/*******************************************************************************
* SAT4J: a SATisfiability library for Java Copyright (C) 2004-2008 Daniel Le Berre
*
* All rights reserved. This program and the accompanying materials
* are made available under the terms of the Eclipse Public License v1.0
* which accompanies this distribution, and is available at
* http://www.eclipse.org/legal/epl-v10.html
*
* Alternatively, the contents of this file may be used under the terms of
* either the GNU Lesser General Public License Version 2.1 or later (the
* "LGPL"), in which case the provisions of the LGPL are applicable instead
* of those above. If you wish to allow use of your version of this file only
* under the terms of the LGPL, and not to allow others to use your version of
* this file under the terms of the EPL, indicate your decision by deleting
* the provisions above and replace them with the notice and other provisions
* required by the LGPL. If you do not delete the provisions above, a recipient
* may use your version of this file under the terms of the EPL or the LGPL.
* 
* Based on the original MiniSat specification from:
* 
* An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
* Sixth International Conference on Theory and Applications of Satisfiability
* Testing, LNCS 2919, pp 502-518, 2003.
*
* See www.minisat.se for the original solver in C++.
* 
*******************************************************************************/
package org.sat4j;

import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.InstanceReader;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ISolver;

/**
 * Very simple launcher, to be used during the SAT competition or the SAT race 
 * for instance.
 * 
 * @author daniel
 *
 */
public class BasicLauncher extends AbstractLauncher {

    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    /**
     * Lance le prouveur sur un fichier Dimacs.
     * 
     * @param args
     *            doit contenir le nom d'un fichier Dimacs, eventuellement
     *            compress?.
     */
    public static void main(final String[] args) {
        BasicLauncher lanceur = new BasicLauncher();
        lanceur.run(args);
        System.exit(lanceur.getExitCode().value());
    }

    protected ISolver configureSolver(String[] args) {
       ISolver asolver = SolverFactory.newDefault();
       asolver.setTimeout(Integer.MAX_VALUE);
            log(asolver.toString(COMMENT_PREFIX)); //$NON-NLS-1$
            return asolver;
    }

    @Override
    protected Reader createReader(ISolver solver, String problemname) {
        return new InstanceReader(solver);
    }

    @Override
    public void usage() {
        log("java -jar sat4j-core.jar <cnffile>");
    }

    @Override
    protected String getInstanceName(String[] args) {
        assert args.length==1;
        return args[0];
    }
}
