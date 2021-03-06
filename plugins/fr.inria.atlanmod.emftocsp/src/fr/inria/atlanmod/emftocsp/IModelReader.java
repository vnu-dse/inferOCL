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
package fr.inria.atlanmod.emftocsp;

import java.util.List;

import org.eclipse.uml2.uml.Association;
import org.eclipse.uml2.uml.Property;

/**
 * @author <a href="mailto:carlos.gonzalez@inria.fr">Carlos A. Gonz�lez</a>
 *
 */
public interface IModelReader<R, P, C, AS, AT, OP> {

	public R getModelResource(); 

	public List<P> getPackages();

	public List<C> getClasses();

	public List<String> getClassesNames();

	public List<AT> getClassAttributes(C c);

	public List<OP> getClassOperations(C c);  

	public List<C> getClassSubtypes(List<C> classList, C c);

	public C getBaseClass(C c);  

	public List<AS> getAssociations();

	public List<String> getAssociationsNames();

	public String getAssociationName(AS as);

	public String getAssociationEndName(AT asEnd);
	//hanhdd
	public List<Property> getOwnedEnds(Association assoc);
}
