
import java.util.StringTokenizer;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.parser.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;


/** This class demonstrates how to access Alloy4 via the compiler methods. */


public final class runAlloy {

	public static String removeSpaces(String s) {
		StringTokenizer st = new StringTokenizer(s," ",false);
		String t="";
		while (st.hasMoreElements()) t += st.nextElement();
		return t;
	}
	/*
	 * Execute every command in every file.
	 *
	 * This method parses every file, then execute every command.
	 *
	 * If there are syntax or type errors, it may throw
	 * a ErrorSyntax or ErrorType or ErrorAPI or ErrorFatal exception.
	 * You should catch them and display them,
	 * and they may contain filename/line/column information.
	 */


	public static void main(String[] args) throws Err {

		//Change the Top-level Class Here:
		String TopLevelClass = new String("ClassModel");
		//Change the root on a different machine
		String root = new String("/Users/sagarsen/Desktop/CartierDemo/demoSpace/Cartier/");
		//Choose number of solutions desired per predicates
		Integer numberOfSolutions=new Integer(5);

		// Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
		// By default, the A4Reporter ignores all these events (but you can extend the A4Reporter to display the event for the user)
		A4Reporter rep = new A4Reporter() {
			// For example, here we choose to display each "warning" by printing it to System.out
			@Override public void warning(ErrorWarning msg) {
				System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
				System.out.flush();
			}
		};
		//Input Alloy File

		String filename = new String(root+"/Temp/currentMetaModel/current.als");


		// Parse+typecheck the model
		System.out.println("=========== Parsing+Typechecking "+filename+" =============");
		Module world = CompUtil.parseEverything_fromFile(rep, null, filename);

		// Choose some default options for how you want to execute the commands
		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.MiniSatJNI;
		Integer modelCopy=new Integer(0);

		Integer setNumber = new Integer(1);
		for (Command command: world.getAllCommands()) {

			System.out.println("============ Command "+command+": ============");

			// Now run it!

			modelCopy=1;
			for (int i=1;i<=numberOfSolutions;i++)
			{
				// String solutionFileName=command.toString().replace(" ", "_")+modelCopy.toString()+".xml";
				String solutionFileName="Set_"+setNumber.toString()+"_Model_"+modelCopy.toString()+".xml";
				A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
				// Print the outcome
				System.out.println("Answer " +modelCopy.toString()+" : ");
				//System.out.println(ans.toString());


				modelCopy=modelCopy+1;


				// If satisfiable...
				if (ans.satisfiable()) {
					// You can query "ans" to find out the values of each set or type.
					// This can be useful for debugging.
					//
					// You can also write the outcome to an XML file
					ans.writeXML(root+"/Temp/alloySolutions/"+solutionFileName);
					//
					// You can then visualize the XML file by calling this:
					//
				}    

				else
				{
					System.out.println("No Solution Found for predicate "+command.toString().replace(" ", "_"));
				}
			}
			setNumber=setNumber+1;
		}

	}
}