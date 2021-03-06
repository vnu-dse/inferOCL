/*******************************************************************************
 * Copyright (c) 2011 INRIA Rennes Bretagne-Atlantique.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *     INRIA Rennes Bretagne-Atlantique - initial API and implementation
 *******************************************************************************/
package fr.inria.atlanmod.emftocsp.impl;

import java.util.List;

/**
 * @author <a href="mailto:carlos.gonzalez@inria.fr">Carlos A. Gonz�lez</a>
 *
 */
public class WeakSatisfiabilityModelProperty extends ModelPropertyImpl {

  public WeakSatisfiabilityModelProperty() {
    String name = "Weak Satisfiability"; //$NON-NLS-1$
    setName(name);
  }
  
  public WeakSatisfiabilityModelProperty(List<String> modelElementsNames) {
    String name = "Weak Satisfiability"; //$NON-NLS-1$
    setName(name);
    setTargetModelElementsNames(modelElementsNames);
  }

}
