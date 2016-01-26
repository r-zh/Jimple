/**
 * File: src/reporter/reportOpts.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 01/06/16		hcai		created; dealing with options in the statistics reporting
 *
*/
package reporters;

import java.util.ArrayList;
import java.util.List;

public class reportOpts {
	protected boolean debugOut = false;
	protected String traceFile = null;
	// simple uniform list of source and sinks
	protected String srcsinkFile = null;
	protected String callbackFile = null;
	
	// categorized sources and sinks
	protected String catsrc = null;
	protected String catsink = null;
	
	public String[] process(String[] args) {
		List<String> argsFiltered = new ArrayList<String>();
		boolean allowPhantom = true;
		
		for (int i = 0; i < args.length; ++i) {
			String arg = args[i];

			if (arg.equals("-debug")) {
				debugOut = true;
			}
			else if (arg.equals("-trace")) {
				traceFile = args[i+1];
				i++;
			}
			else if (arg.equals("-srcsink")) {
				srcsinkFile = args[i+1];
				i++;
			}
			else if (arg.equals("-catsrc")) {
				catsrc = args[i+1];
				i++;
			}
			else if (arg.equals("-catsink")) {
				catsink = args[i+1];
				i++;
			}
			else if (arg.equals("-callback")) {
				callbackFile = args[i+1];
				i++;
			}
			else if (arg.equals("-nophantom")) {
				allowPhantom = false;
			}
			else {
				argsFiltered.add(arg);
			}
		}
		
		if (allowPhantom) {
			argsFiltered.add("-allowphantom");
		}
		
		String[] arrArgsFilt = new String[argsFiltered.size()];
		return (String[]) argsFiltered.toArray(arrArgsFilt);
	}
}

/* vim :set ts=4 tw=4 tws=4 */

