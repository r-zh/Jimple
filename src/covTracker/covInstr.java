/**
 * File: src/covTracker/covInst.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 06/18/16		hcai		created; for monitoring user code statement coverage
 * 06/19/16		hcai		reached the working version
*/
package covTracker;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Iterator;
import java.util.Set;

import profile.InstrumManager;

import dua.Extension;
import dua.Forensics;
import dua.global.ProgramFlowGraph;
import dua.method.CFG;
import dua.method.CFG.CFGNode;
import dua.util.Util;
import fault.StmtMapper;

import soot.*;
import soot.jimple.*;
import soot.tagkit.Tag;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BlockGraph;
import soot.toolkits.graph.ExceptionalBlockGraph;
import utils.*;
import soot.tagkit.LineNumberTag;

public class covInstr implements Extension {
	
	protected SootClass clsMonitor;
	
	protected SootMethod mSProbe;
	
	protected File fJimpleOrig = null;
	protected File fJimpleInsted = null;
	
	protected static Options opts = new Options();

	public static void main(String args[]){
		args = preProcessArgs(opts, args);

		covInstr icgins = new covInstr();
		// examine catch blocks
		dua.Options.ignoreCatchBlocks = false;
		dua.Options.skipDUAAnalysis = false;
		dua.Options.modelAndroidLC = false;
		dua.Options.analyzeAndroid = true;
		
		soot.options.Options.v().set_src_prec(soot.options.Options.src_prec_apk);
		
		//output as APK, too//-f J
		soot.options.Options.v().set_output_format(soot.options.Options.output_format_dex);
		soot.options.Options.v().set_force_overwrite(true);
		soot.options.Options.v().set_keep_line_number(true);
		
		Scene.v().addBasicClass("com.ironsource.mobilcore.BaseFlowBasedAdUnit",SootClass.SIGNATURES);
		Scene.v().addBasicClass("covTracker.covMonitor");
		
		
		Forensics.registerExtension(icgins);
		Forensics.main(args);
	}
	
	protected static String[] preProcessArgs(Options _opts, String[] args) {
		opts = _opts;
		args = opts.process(args);
		
		String[] argsForDuaF;
		int offset = 0;

		argsForDuaF = new String[args.length + 2 - offset];
		System.arraycopy(args, offset, argsForDuaF, 0, args.length-offset);
		argsForDuaF[args.length+1 - offset] = "-paramdefuses";
		argsForDuaF[args.length+0 - offset] = "-keeprepbrs";
		
		return argsForDuaF;
	}
	
	/**
	 * Descendants may want to use customized event monitors
	 */
	protected void init() {
		clsMonitor = Scene.v().getSootClass("covTracker.covMonitor");
		clsMonitor.setApplicationClass();
				
		mSProbe = clsMonitor.getMethodByName("sprobe");
	}
	
	public void run() {
		System.out.println("Running instrumentation for statement coverage monitoring...");
		//StmtMapper.getCreateInverseMap();

		instrument();
		
		if (opts.dumpJimple()) {
			String fnJimple = soot.options.Options.v().output_dir()+File.separator+utils.getAPKName()+"_JimpleInstrumented.out";
			fJimpleInsted = new File(fnJimple);
			utils.writeJimple(fJimpleInsted);
		}
	}
	
	public int getSLOC() {
		Set<Integer> lns = new HashSet<Integer>();
		Set<Integer> lnsLog = new HashSet<Integer>();
		/* traverse all classes */
		Iterator<SootClass> clsIt = ProgramFlowGraph.inst().getUserClasses().iterator();
		if (opts.instrall())
			clsIt = ProgramFlowGraph.inst().getAppClasses().iterator();

		// define the parameter of result
		int[] exception = new int[3];
		int num_ex = 0, size_ex = 0, num_log_ex = 0;

		while (clsIt.hasNext()) {
			SootClass sClass = (SootClass) clsIt.next();
			if (sClass.isPhantom()) {
				// skip phantom classes
				continue;
			}
			if (!sClass.isApplicationClass()) {
				// skip library classes
				continue;
			}

			/* traverse all methods of the class */
			Iterator<SootMethod> meIt = sClass.getMethods().iterator();
			while (meIt.hasNext()) {
				SootMethod sMethod = (SootMethod) meIt.next();
				if (!sMethod.isConcrete()) {
					// skip abstract methods and phantom methods, and native methods as well
					continue;
				}
				if (sMethod.toString().indexOf(": java.lang.Class class$") != -1) {
					// don't handle reflections now either
					continue;
				}

				// cannot instrument method event for a method without active body
				if (!sMethod.hasActiveBody()) {
					continue;
				}
				/*
				 * if (sMethod.isJavaLibraryMethod() || !sMethod.isDeclared() ||
				 * sMethod.isNative()) { continue; }
				 */
				// if (sMethod.isConstructor() || sMethod.isStaticInitializer()) continue;

				/*
				 * the ID of a method to be used for identifying and indexing a method in the
				 * event maps of EAS
				 */
				String meId = sMethod.getSignature();

				CFG cfg = ProgramFlowGraph.inst().getCFG(sMethod);

				if (cfg == null || !cfg.isReachableFromEntry()) {
					System.out.println("\nSkipped method unreachable from entry: " + meId + "!");
					continue;
				}

				// -- DEBUG
				if (opts.debugOut()) {
					System.out.println("\nNow instrumenting method " + meId + "...");
				}
				
				for (CFGNode n : cfg.getNodes()) {
					Stmt s = n.getStmt();
					if (n.isInCatchBlock() || n.isSpecial() || s == null)
						continue;
					if (s instanceof IdentityStmt)
						continue;
					Tag lntag = null;
					for (Tag t : s.getTags()) {
						// System.out.println("one more tag " + t);
						if (t instanceof LineNumberTag) {
							lntag = t;
							break;
						}
					}
					if (lntag == null) {
						continue;
					}

					byte[] arrln = lntag.getValue();
					int ln = ((arrln[0] & 0xff) << 8) | (arrln[1] & 0xff);
					
					lns.add(ln);

					// add log node into the list
					if (isLLOC(s)) {
						lnsLog.add(ln);
						// System.out.println(s.toString());
					}
				}
				
				// add the num to the sum
				exception = getException(sMethod);

				num_ex += exception[0];
				size_ex += exception[1];
				num_log_ex += exception[2];

			} // -- while (meIt.hasNext())
		} // -- while (clsIt.hasNext())
		System.out.println("Total Log Lines of Code in the program: " + lnsLog.size());

		// total line, log line, exception number, size_ex, log number in
		// exception size will be a problem, we don't really need it
		String result = lns.size() + "," + lnsLog.size() + "," + num_ex + "," + size_ex + "," + num_log_ex;

		// TODO echo -e "$1,\c" >> log_exception.csv
		print_toFile(result);
		return lns.size();
	}

	public boolean isLLOC(Stmt s) {
		// function invoke
		if (s instanceof InvokeStmt) {
			InvokeExpr expr = s.getInvokeExpr();
			/**
			 * log logger timber system.out system.err info warn error debug fatal trace
			 * aspect
			 */
			String log = expr.toString().toLowerCase();
			String[] logSymbol = { ".log:", " println(java.lang.String)", ".logger:", ".timber:" };
			// log statement symbols
			for (String i : logSymbol) {
				if (log.contains(i))
					return true;
			}
		}
		return false;
	}

	// when I add this condition, there is no code in the exception, so there are
	// differences between the block graph and CFG, so we just count the number
	public int[] getException(SootMethod sMethod) {
		int[] exception = { 0, 0, 0 };

		BlockGraph bg = new ExceptionalBlockGraph(sMethod.getActiveBody());

		for (Block block : bg.getBlocks()) {
			Stmt head = (Stmt) block.getHead(), curunit = head, exit = curunit;
		
			if (head.toString().contains(":= @caughtexception")) {
				exception[0]++;
				System.out.println(block.getBody());
				
				while (curunit != null) {
					exit = curunit;
					curunit = (Stmt) block.getSuccOf(curunit);
				//System.out.println("here is the exception part:>>>>>>>>>>>>>>>>"+exit);

					if(ProgramFlowGraph.inst().getNode((exit)).isInCatchBlock()){
						System.out.println("it is isInCatchBlock:>>>>>>>>>>>>>>>>"+exit);
						//continue;
					}
					if(ProgramFlowGraph.inst().getNode((exit)).isSpecial()) {
						System.out.println("it is isSpecial:>>>>>>>>>>>>>>>>"+exit);
						//continue;
					}
						
					if (exit instanceof IdentityStmt)
						continue;
					Tag lntag = null;
					for (Tag t : exit.getTags()) {
						if (t instanceof LineNumberTag) {
							lntag = t;
							break;
						}
					}
					if (lntag == null) {
						continue;
					}
					System.out.println("it is counted:>>>>>>>>>>>>>>>>"+exit);
					exception[1]++;

					if (isLLOC(exit)) {
						exception[2]++;
					}
				}//while (curunit != null
			}
		}//for (Block block : bg.getBlocks()) 
		return exception;
	}

	public void print_toFile(String result) {
		String apkName = apkDir.substring(apkDir.lastIndexOf('/') + 1, apkDir.lastIndexOf('.'));
		String apkPath = apkDir.substring(0, apkDir.lastIndexOf('/') + 1);

		result = apkName + "," + result;

		// String filename = "../log_exception.csv";
		String filename = apkPath + "log_exception.csv";
		try {
			FileOutputStream fos = new FileOutputStream(filename, true);
			fos.write(result.getBytes());
			fos.write("\n".getBytes());
			fos.close();
			System.out.println("File write successfully");
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
			System.out.println(e1);
		} catch (IOException e) {
			e.printStackTrace();
			System.out.println(e);
		}
	}
		
	public void instrument() {
		if (opts.dumpJimple()) {
			//String fnJimple = Util.getCreateBaseOutPath() + "JimpleOrig.out";
			String fnJimple = soot.options.Options.v().output_dir()+File.separator+utils.getAPKName()+"_JimpleOrg.out";
			fJimpleOrig = new File(fnJimple);
			utils.writeJimple(fJimpleOrig);
		}
		
		if (opts.dumpFunctionList()) {
			String fnFunclist = Util.getCreateBaseOutPath() + "functionList.out";
			utils.dumpFunctionList(fnFunclist);
		}
		
		init();
		
		int sloc = getSLOC();
		System.out.println("Total Source Lines of Code in the program: " + sloc);

		/* traverse all classes */
		int cnt = 0, skipped=0;
		Iterator<SootClass> clsIt = ProgramFlowGraph.inst().getUserClasses().iterator();
		if (opts.instrall()) clsIt = ProgramFlowGraph.inst().getAppClasses().iterator(); 
		while (clsIt.hasNext()) {
			SootClass sClass = (SootClass) clsIt.next();
			if ( sClass.isPhantom() ) {
				// skip phantom classes
				continue;
			}
			if ( !sClass.isApplicationClass() ) {
				// skip library classes
				continue;
			}

            //if (sClass.isInterface()) continue;
            //if (sClass.isInnerClass()) continue;
			
			
			/* traverse all methods of the class */
			Iterator<SootMethod> meIt = sClass.getMethods().iterator();
			while (meIt.hasNext()) {
				SootMethod sMethod = (SootMethod) meIt.next();
				if ( !sMethod.isConcrete() ) {
					// skip abstract methods and phantom methods, and native methods as well
					continue; 
				}
				if ( sMethod.toString().indexOf(": java.lang.Class class$") != -1 ) {
					// don't handle reflections now either
					continue;
				}
				
				// cannot instrument method event for a method without active body
				if ( !sMethod.hasActiveBody() ) {
					continue;
				}
				/*
				if (sMethod.isJavaLibraryMethod() || !sMethod.isDeclared() || sMethod.isNative()) {
					continue;
				}
				*/
				//if (sMethod.isConstructor() || sMethod.isStaticInitializer()) continue;
				
				PatchingChain<Unit> pchn = sMethod.retrieveActiveBody().getUnits();
				
				/* the ID of a method to be used for identifying and indexing a method in the event maps of EAS */
				String meId = sMethod.getSignature();
				
				/* 1. instrument method entry events and program start event */
				CFG cfg = ProgramFlowGraph.inst().getCFG(sMethod);
				
				if (cfg == null || !cfg.isReachableFromEntry()) {
					System.out.println("\nSkipped method unreachable from entry: " + meId + "!");
					continue;
				}
				
				// -- DEBUG
				if (opts.debugOut()) {
					System.out.println("\nNow instrumenting method " + meId + "...");
				}

				for (CFGNode n : cfg.getNodes()) {
					Stmt s = n.getStmt();
					if (n.isInCatchBlock() || n.isSpecial() || s==null) continue;
					if (n instanceof IdentityStmt) continue;
					Tag lntag = null;
					for (Tag t : s.getTags()) {
						if (t instanceof LineNumberTag) {
							lntag = t;
							break;
						}
					}
					if (lntag ==null) {
						//System.out.println("\nSkipped statement due to lack of linenumber tag: " + s);
						skipped ++;
						continue;
					}
					
					byte[] arrln = lntag.getValue();
					int ln = ((arrln[0] & 0xff) << 8) | (arrln[1] & 0xff);

					List<Stmt> sProbes = new ArrayList<Stmt>();
					List<IntConstant> sArgs = new ArrayList<IntConstant>();
					sArgs.add(IntConstant.v(ln));
					sArgs.add(IntConstant.v(sloc));
					Stmt sCall = Jimple.v().newInvokeStmt( Jimple.v().newStaticInvokeExpr( mSProbe.makeRef(), sArgs ));
					sProbes.add(sCall);	
					
					InstrumManager.v().insertAfter(pchn, sProbes, s);
					cnt ++;
				}
			} // -- while (meIt.hasNext()) 
		} // -- while (clsIt.hasNext())
		System.out.println("Total Jumple Lines of Code Probed: " + cnt);
		System.out.println("Total Jumple Lines of Code Skipped due to lack of source line number: " + skipped);
	} // -- void instrument
} // -- public class icgInst  

/* vim :set ts=4 tw=4 tws=4 */

