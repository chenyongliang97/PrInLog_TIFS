package prinlog.taintanalysis.main;

import java.beans.Statement;
import java.io.File;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;

import org.json.JSONObject;
import org.yaml.snakeyaml.scanner.Constant;

import java.util.Map.Entry;

import prinlog.main.runTest;
import prinlog.stringvsa.backwardslicing.BacktracingContext;
import prinlog.stringvsa.base.BackTraceQuestion;
import prinlog.stringvsa.base.StmtPoint;
import prinlog.stringvsa.forwardexec.LightICCForwardContext;
import prinlog.stringvsa.forwardexec.StmtPath;
import prinlog.stringvsa.graph.CallGraph;
import prinlog.stringvsa.graph.HeapObject;
import prinlog.stringvsa.graph.ValuePoint;
import prinlog.stringvsa.utility.MethodUtility;
import prinlog.stringvsa.utility.OtherUtility;
import prinlog.taintanalysis.base.SinkMethod;
import prinlog.taintanalysis.base.SourcePoint;
import prinlog.taintanalysis.base.TaintQuestion;
import prinlog.taintanalysis.solver.SimulationContext;
import prinlog.taintanalysis.solver.StmtItem;
import prinlog.taintanalysis.solver.TaintQuestionSolver;
import prinlog.taintanalysis.utility.BlockGenerator;
import prinlog.taintanalysis.utility.ListUtility;
import prinlog.taintanalysis.utility.Logger;
import prinlog.taintanalysis.utility.TimeUtility;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.JastAddJ.IfStmt;
import soot.baf.IfCmpEqInst;
import soot.coffi.class_element_value;
import soot.jimple.AssignStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.StringConstant;
import soot.jimple.internal.JArrayRef;
import soot.options.LCMOptions;
import soot.tagkit.SourceLnNamePosTag;
import soot.toolkits.graph.Block;
import soot.util.Chain;


public class QuestionGenerator {
	ArrayList<TaintQuestion> tqInput;
	ArrayList<TaintQuestion> tqArray;

	List<TaintQuestion> solvedInput = new ArrayList<TaintQuestion>();
	List<TaintQuestion> solvedArray = new ArrayList<TaintQuestion>();
	
	public List<BackTraceQuestion> bps = new ArrayList<BackTraceQuestion>();

	public String isInterestedAnalyticAPI(String invokeSig) {
		
		if (invokeSig.contains("<com.google.android.gms.analytics.Tracker") && invokeSig.contains(" send")) return "GA";
//		
		if (invokeSig.contains("<com.google.firebase.analytics.FirebaseAnalytics") && invokeSig.contains(" logEvent")) return "Firebase";
		
		if (invokeSig.contains("<com.mixpanel.android.mpmetrics.MixpanelAPI: void track")) return "MixPanel";  // track/ trackMap/ trackWithGroups
		
		if (invokeSig.contains("<com.facebook.appevents.AppEventsLogger") &&
			(invokeSig.contains(" logEvent") ))return "FB";
			// || invokeSig.contains(" logPurchase")
			// || invokeSig.contains(" logProductItem(")))
		
		if (invokeSig.contains("<com.flurry.android.FlurryAgent: com.flurry.android.FlurryEventRecordStatus log")) return "Flurry";
		
		if (invokeSig.contains(" LogEvent") && invokeSig.contains("de.ecspride")) return "TEST";
		return "";
	}
	
	public HashSet<String> generateInputQuestions() {
		
		HashSet<String> svd = new HashSet<String>();

		for (SootClass sclas : Scene.v().getClasses()) {
			String scName = sclas.toString();
			
			if (scName.contains("com.google.android.gms")) continue;
			if (scName.contains("com.google.firebase.analytics.")) continue;
			if (scName.contains("com.mixpanel.android.mpmetrics.MixpanelAPI")) continue;
			if (scName.contains("com.facebook.appevents")) continue;
			if (scName.contains("com.flurry.android")) continue;

			// if (!scName.contains("com.amakdev.budget.app.system.component.analytics.AnalyticsLogger")) continue;

			if (scName.startsWith("android") || scName.startsWith("org") || scName.startsWith("java") || scName.startsWith("kotlin")) continue;
			
			for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
				if (!smthd.isConcrete()) {	// For interface XX {} and abstract class, get their methods' templates
					continue;
				}

				
				Body body = smthd.retrieveActiveBody();
				if (body == null)
					continue;
				List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();

				if (smthd.toString().contains("MainActivity"))
					for (Block b : bs)
						System.out.println(b.toString());
				
				for (Block block : bs) {
					

					for (Unit unit : block) {

						if (unit instanceof AssignStmt) {
							Value rop = ((AssignStmt) unit).getRightOp();
							
							if (rop instanceof NewExpr) {
								SootClass sclass = ((NewExpr)rop).getBaseType().getSootClass();
							
								if (sclass.isApplicationClass() && sclass.isConcrete()) {
									if (CallGraph.class2NewSite.containsKey(sclass)) CallGraph.class2NewSite.get(sclass).add(new StmtPoint(smthd, block, unit));
									else  {
										HashSet<StmtPoint> sss = new HashSet<>();
										sss.add(new StmtPoint(smthd, block, unit));
										CallGraph.class2NewSite.put(sclass, sss);
										
									}
								}
							}
						}

						if (unit instanceof AssignStmt) {
							
							if (((AssignStmt) unit).getRightOp() instanceof InvokeExpr) {
								String sig = ((InvokeExpr) ((AssignStmt) unit).getRightOp()).getMethodRef().getSignature();
								String libType = isInterestedAnalyticAPI(sig);	///
								
								if (!libType.isEmpty()){
									Logger.print("Found one source: " + unit.toString() + " in " + smthd.getSignature());
						
									String rop = ((InvokeExpr) ((AssignStmt) unit).getRightOp()).toString();
									List<String> paramList = new ArrayList<String>();
									for (String i : ((String) rop.subSequence(rop.indexOf(")>(") + 3, rop.lastIndexOf(")"))).split(","))
										paramList.add(i.trim());
									
									JSONObject ret = new JSONObject();
																		
									int index = 0;
									JSONObject sink = new JSONObject();
									sink.put("method", smthd.getSignature().toString());
									sink.put("unit", unit.toString());
									sink.put("unitIndex", prinlog.taintanalysis.utility.MethodUtility.getUnitIndex(smthd, unit));
									for (Type t : ((InvokeExpr) ((AssignStmt) unit).getRightOp()).getMethodRef().getParameterTypes()) {										
										sink.append("taint_var", paramList.get(index));
										index++;
									}
									
									// Also track the tracker object
									InvokeExpr ive = ((InvokeStmt)((AssignStmt) unit).getRightOp()).getInvokeExpr();
									
									// if (ive instanceof InstanceInvokeExpr) {
									// 	sink.append("taint_var", ((InstanceInvokeExpr) ive).getBase());
										
									// }
									
									
									ret.append("sinks", sink);
									
									JSONObject tmp_json = new JSONObject();
									if (ret.has("sinks")) {
										tmp_json.put("sinks", ret.getJSONArray("sinks"));
										if (!svd.contains(tmp_json.toString())) {
											svd.add(tmp_json.toString());
										}
									}
									
								}
								
							}
						} else if (unit instanceof InvokeStmt) {
							String sig = ((InvokeStmt)unit).getInvokeExpr().getMethodRef().getSignature();
							String libType = isInterestedAnalyticAPI(sig);
							if (!libType.isEmpty()){
								Logger.print("Found one source: " + unit.toString() + " in " + smthd.getSignature());
								String rop = unit.toString();
								List<String> paramList = new ArrayList<String>();
								
								for (String i : ((String) rop.subSequence(rop.indexOf(")>(") + 3, rop.lastIndexOf(")"))).split(","))
									paramList.add(i.trim());
								
								JSONObject ret = new JSONObject();
								JSONObject sink = new JSONObject();
								sink.put("method", smthd.getSignature().toString());
								sink.put("unit", unit.toString());
								sink.put("unitIndex", prinlog.taintanalysis.utility.MethodUtility.getUnitIndex(smthd, unit));
								int index = 0;
								for (Type t : ((InvokeStmt)unit).getInvokeExpr().getMethodRef().getParameterTypes()) {
									sink.append("taint_var", paramList.get(index));
									index++;
								}
										
								ret.append("sinks", sink);
//								
								JSONObject tmp_json = new JSONObject();
								if (ret.has("sinks")) {
									tmp_json.put("sinks", ret.getJSONArray("sinks"));
									if (!svd.contains(tmp_json.toString())) {
										svd.add(tmp_json.toString());
									}
								}
							}
						}
						

					}
				}
			}
		}
		
		return svd;
	}

	private TaintQuestion generateOneFwQuestion(SootMethod smthd, Block block, Unit unit, Value value) {

		SourcePoint sp = new SourcePoint(smthd, block, unit, value);

		TaintQuestion tq = new TaintQuestion(sp, value);
		
		return tq;
	}

	
	public ArrayList<TaintQuestion> findKeyUsages(HashSet<String> targetKeys){
		ArrayList<TaintQuestion> tqList = new ArrayList<>();
		Unit lastUnit = null;
		Block lastBlock = null;

		int dd = 0;
		// System.out.println("Finding usages for keys: " + targetKeys);

		
		for (SootClass sclas : Scene.v().getClasses()) {
			String scName = sclas.getName();
			if (scName.startsWith("android") || scName.startsWith("org") || scName.startsWith("java")) continue;
			
			for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {
				dd = 0;
				if (!smthd.isConcrete())
					continue;

				Body body = smthd.retrieveActiveBody();
				if (body == null)
					continue;
				
				List<Block> bs = BlockGenerator.getInstance().generate(body).getBlocks();
				
				for (Block block : bs) {
					for (Unit unit : block) {
						if (dd > 0) {
							lastUnit = unit;
							lastBlock = block;
							dd += 1;
							continue;
						}

						for (ValueBox box : unit.getUseAndDefBoxes()) {
							Value v = box.getValue();
							if (v instanceof StringConstant && targetKeys.contains(((StringConstant) v).value)){

								if (unit.toString().contains("<android.content.SharedPreferences$Editor: android.content.SharedPreferences$Editor putString(java.lang.String,java.lang.String)>")
								|| unit.toString().contains("<android.content.SharedPreferences$Editor: android.content.SharedPreferences$Editor putStringSet(java.lang.String,java.util.Set)>")
								|| (unit.toString().contains("<android.content.Intent: ") && unit.toString().contains(" put"))) {
									// found target
									

									Logger.print(runTest.dg.getNodes().size());
									Logger.print("Found Target put for Key: " + ((StringConstant) v).value);

									ArrayList<Integer> regIndex = new ArrayList<Integer>();
									regIndex.add(1);
									
									HeapObject ho = HeapObject.getInstance(runTest.dg, ((StringConstant) v).value);
									ValuePoint vp = new ValuePoint(runTest.dg, smthd, block, unit, regIndex);
									ho.getVPs().add(vp);
									runTest.dg.addNode(ho);
									
									
									

								} else if (unit.toString().contains("<android.content.SharedPreferences: java.lang.String getString(java.lang.String,java.lang.String)>") || (unit.toString().contains("<android.content.Intent") && unit.toString().contains(" get"))){
									
								} else {
									tqList.add(generateOneFwQuestion(smthd, lastBlock, lastUnit, v));
									Logger.print("Found Fw Question: " + unit + ", interested Var: " + v);
								}

							}
						}
						lastUnit = unit;
						lastBlock = block;
					}
				}
			}
		}

		return tqList;
		
	}
	
	
	
	boolean containsKey(String key, List<Value> params) {
		for (Value val : params)
			if (val instanceof StringConstant && ((StringConstant) val).value.equals(key))
				return true;
		return false;
	}
	
	

// 	public void solveInputQuestions(boolean gArrayQuestions) {
// 		solvedInput = new ArrayList<TaintQuestion>();

// 		Hashtable<Integer, ArrayList<TaintQuestion>> solvedList = new Hashtable<Integer, ArrayList<TaintQuestion>>();
		
// 		TaintQuestionSolver tgSolver = new TaintQuestionSolver();
// 		int i = 0;
// 		int positive = 0;
// 		TaintQuestion tq = null;
// 		while (getTqInput().size() > 0 && !runTest.timeout){
// 			tq = getTqInput().get(0);
// 			getTqInput().remove(0);
// 			System.out.println("============= Start Solving Q-" + i + ". Now tq size: " + getTqInput().size());
// 			System.out.println(tq.getSourcep().getMethodLocation());
// //			System.out.println(tq.getSourcep().getBlockLocation());
// 			System.out.println("Source method in: " + tq.getSourcep().getMethodLocation().toString());
// 			System.out.println("Instruction: " + tq.getSourcep().getInstructionLocation().toString());
// 			ArrayList<TaintQuestion> solvedtqs = tgSolver.solve(tq);
// 			System.out.println("============= End Solving Q-"+i);
// //			System.out.println("End Solving Q-" + i++);
// 			i++;
// 			if (containsPositive(solvedtqs)) {
// 				solvedList.put(i, solvedtqs);
// 				positive++;
// 				runTest.init_taint_res = TResSolve.saveSolved(solvedList);
// 			}else{
// //				System.out.println("Question Q-"+ i + " is negative!\n");
// 			}
// 		}

// 		System.out.println("Statistic: Total Questions:" + i + " Total Positive: " + positive);


// 	}
	
// 	public boolean containsPositive(ArrayList<TaintQuestion> tqList) {
// 		for (TaintQuestion tq : tqList)
// 			if (tq.isPositive()) return true;
// 		return false;
// 	}



// 	public ArrayList<CrossPath> checkOverlappingAndGetResults() {
// 		ArrayList<CrossPath> paths = new ArrayList<CrossPath>();
// 		if (solvedInput.size() > 0 && solvedArray.size() > 0) {
// 			Hashtable<Unit, List<SimulationContext>> pointsInput = new Hashtable<Unit, List<SimulationContext>>();
// 			Hashtable<Unit, List<SimulationContext>> pointsArray = new Hashtable<Unit, List<SimulationContext>>();

// 			for (TaintQuestion tq : solvedInput) {
// 				for (LightICCForwardContext sc : tq.getsContexts()) {
// 					if (sc.isContainsSink()) {
// 						for (StmtItem stmt : sc.getInstructionTrace()) {
// 							if (stmt.isContainsSink()) {
// 								if (!pointsInput.containsKey(stmt.getU()))
// 									pointsInput.put(stmt.getU(), new ArrayList<SimulationContext>());
// 								pointsInput.get(stmt.getU()).add(sc);
// 							}
// 						}
// 					}
// 				}
// 			}

// 			for (TaintQuestion tq : solvedArray) {
// 				for (LightICCForwardContext sc : tq.getsContexts()) {
// 					if (sc.isContainsSink()) {
// 						for (StmtItem stmt : sc.getInstructionTrace()) {
// 							if (stmt.isContainsSink()) {
// 								if (!pointsArray.containsKey(stmt.getU()))
// 									pointsArray.put(stmt.getU(), new ArrayList<SimulationContext>());
// 								pointsArray.get(stmt.getU()).add(sc);
// 							}
// 						}
// 					}
// 				}
// 			}

// 			for (Unit u : pointsInput.keySet()) {
// 				if (pointsArray.containsKey(u)) {
// 					paths.add(new CrossPath(u, pointsInput.get(u), pointsArray.get(u)));
// 				}
// 			}

// 		}

// 		System.out.println(paths.size());

// 		return paths;
// 	}

}
