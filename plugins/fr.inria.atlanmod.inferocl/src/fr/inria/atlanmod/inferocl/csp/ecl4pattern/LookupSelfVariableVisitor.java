package fr.inria.atlanmod.inferocl.csp.ecl4pattern;
import org.eclipse.uml2.uml.CallOperationAction;
import org.eclipse.uml2.uml.Classifier;
import org.eclipse.uml2.uml.Constraint;
import org.eclipse.uml2.uml.EnumerationLiteral;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Parameter;
import org.eclipse.uml2.uml.Property;
import org.eclipse.uml2.uml.SendSignalAction;
import org.eclipse.uml2.uml.State;
import org.eclipse.ocl.expressions.Variable;
import org.eclipse.ocl.expressions.VariableExp;
import org.eclipse.ocl.utilities.AbstractVisitor;

public class LookupSelfVariableVisitor extends AbstractVisitor<Variable<Classifier, Parameter>, Classifier, Operation, Property, EnumerationLiteral, Parameter, State, CallOperationAction, SendSignalAction, Constraint> {
	
	public  Variable<Classifier, Parameter> visitVariableExp(VariableExp<Classifier, Parameter> v) {
		Variable<Classifier, Parameter> referredVar = v.getReferredVariable();
		if ("self".equals(referredVar.getName())) {
			result = referredVar;
		}
		return result;
	}
	
	/**
	 * If the "self" variable was referenced, this method return the declaration of the variable, 
	 * otherwise the method return null.
	 */
	public Variable<Classifier, Parameter> getResult() {
		return result;
	}
}