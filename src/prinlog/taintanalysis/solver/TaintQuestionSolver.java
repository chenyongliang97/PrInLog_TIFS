package prinlog.taintanalysis.solver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;
import java.util.concurrent.TimeUnit;

import prinlog.main.runTest;
import prinlog.stringvsa.forwardexec.LightICCForwardContext;
import prinlog.stringvsa.forwardexec.LightICCForwardEngine;
import prinlog.taintanalysis.base.SourcePoint;
import prinlog.taintanalysis.base.TaintQuestion;
import prinlog.taintanalysis.main.QuestionGenerator;
import prinlog.taintanalysis.utility.BlockGenerator;
import prinlog.taintanalysis.utility.ListUtility;
import prinlog.taintanalysis.utility.Logger;
import prinlog.taintanalysis.utility.TimeUtility;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.ThisRef;
import soot.toolkits.graph.Block;

public class TaintQuestionSolver {
	public static HashSet<String> staticFieldVariableSet;
	public static HashSet<String> newStaticFieldSet;
//	public static InterfaceTree tree = null;
	public static int processedInstruction = 0;
	
// 	public ArrayList<TaintQuestion> solve(TaintQuestion originTq) {
// 		staticFieldVariableSet = new HashSet<String>();
// 		newStaticFieldSet = new HashSet<String>();
		
// 		ArrayList<TaintQuestion> tqList = new ArrayList<TaintQuestion>();
		
// 		int iterTimes = 0;
// 		runTest.questionTimeout = false;
// 		Thread thread = TimeUtility.startWatcherOneQuestionBruce(3 * 60);
// 		tqList.addAll(solveOneTq(originTq, originTq.getSourcep()));
// 		while (newStaticFieldSet.size() > 0 && !runTest.questionTimeout && !runTest.timeout) {
// 			iterTimes++;
// 			if (iterTimes >= 2) {
// //				System.out.println("Shut down this question since exceeding iteration time limit");
// 				break;
// 			}
// 			staticFieldVariableSet.addAll(newStaticFieldSet);
// 			HashSet<String> tempNewSet = (HashSet<String>) newStaticFieldSet.clone();
// 			newStaticFieldSet = new HashSet<String>();
			
// 			for (SootClass sclas : Scene.v().getClasses()) {
// 				String scName = sclas.toString();
// 				for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
// 					if (!smthd.isConcrete()) continue;
	
// 					Body body = smthd.retrieveActiveBody();
// 					if (body == null) continue;
// 					List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
// 					for (Block block : bs) {
// 						for (Unit unit : block) {
// 							if (unit instanceof AssignStmt) {
// 								Value rop = ((AssignStmt) unit).getRightOp();
// 								if (rop instanceof StaticFieldRef && tempNewSet.contains(((StaticFieldRef)rop).getField().toString())) {
// 									QuestionGenerator qg = new QuestionGenerator();
// 									TaintQuestion curTq = qg.generateOneStaticFieldQuestion(smthd, block, unit, ((AssignStmt) unit).getLeftOp(), false, originTq);
// //									System.out.println("Found one source: " + unit.toString() + " in " + smthd.toString());
// 									tqList.addAll(solveOneTq(curTq, originTq.getSourcep()));
// 								}
// 							}
// 						}
// 					}
// 				}
// 			}
			
// 		}
// 		if (thread.isAlive())
// 			thread.interrupt();
// 		return tqList;
// 	}
	
	public static void solveOneTq(TaintQuestion tq){
		ArrayList<TaintQuestion> tqList = new ArrayList<TaintQuestion>();
		
		LightICCForwardContext target = null;


		while (!runTest.timeout) {
			// printState(tq);
			if (tq.hasSolved()) break;

			while (tq.getsContexts().size() > 100000){
//				System.out.println("*******Out of size remove current Context");
				tq.getsContexts().remove(tq.getsContexts().size() - 1);
			}
			
			target = null;
			for (LightICCForwardContext sContext : tq.getsContexts()) {
				if (!sContext.isTerminated()) {
					target = sContext;
					break;
				}
			}

			if (target == null) {
				tq.setHasSolved();
				break;
			}


			tq.addSContexts(LightICCForwardEngine.getInstance().oneStepForward(tq, target));
			// processOneInstruction(tq, target);
		}
		
		tqList.add(tq);
		
		
	}

	// public void processOneInstruction(TaintQuestion tq, SimulationContext sContext) {

	// 	List<SimulationContext> diversed = SimulationEngine.getInstance().oneStepForward(tq, sContext);

	// 	for (SimulationContext sc : diversed) {
	// 		tq.addSContexts(sc);
	// 	}
	// }

	// public void print(TaintQuestion tq) {
	// 	for (SimulationContext sContext : tq.getsContexts()) {
	// 		Logger.print(sContext.isContainsSink() + " " + sContext.hashCode());
	// 		for (StmtItem u : sContext.getInstructionTrace()) {
	// 			Logger.print("    " + u.isContainsSink() + " " + u.getU());
	// 			Logger.print("        " + u.getUnitIndex() + " " + u.getSm());
	// 		}
	// 	}
	// }
	
	
}
