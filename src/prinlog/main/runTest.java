package prinlog.main;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;
import java.util.concurrent.locks.Condition;
import java.util.prefs.BackingStoreException;

import org.jf.dexlib2.immutable.ImmutableClassDef;
import org.jf.smali.SmaliMethodParameter;
import org.json.JSONArray;
import org.json.JSONObject;

import prinlog.stringvsa.backwardslicing.BacktracingContext;
import prinlog.stringvsa.backwardslicing.BackwardController;
import prinlog.stringvsa.backwardslicing.TaintRules;
import prinlog.stringvsa.base.BackTraceQuestion;
import prinlog.stringvsa.base.StmtPoint;
import prinlog.stringvsa.graph.CallGraph;
import prinlog.stringvsa.graph.ConditionBlock;
import prinlog.stringvsa.graph.DGraph;
import prinlog.stringvsa.graph.HeapObject;
import prinlog.stringvsa.graph.IDGNode;
import prinlog.stringvsa.graph.ValuePoint;
import prinlog.stringvsa.utility.BlockGenerator;
import prinlog.stringvsa.utility.Logger;
import prinlog.taintanalysis.base.TaintQuestion;
import prinlog.taintanalysis.main.QuestionGenerator;
import prinlog.taintanalysis.solver.InterfaceTree;
import prinlog.taintanalysis.utility.FileUtility;
import prinlog.taintanalysis.utility.TimeUtility;
import netscape.javascript.JSObject;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Value;
// import soot.asm.backend.targets.nullTypes;
import soot.jimple.AssignStmt;
import soot.jimple.infoflow.android.resources.ARSCFileParser;
import soot.options.Options;

public class runTest {
	public static String path;
	public static String pn;
	static Hashtable<String, Hashtable<String, String>> m2m;
	
	public static Hashtable<String, HashSet<String>> interfMthdTplt;
	public static Hashtable<String, ArrayList<SootMethod>> i2c;
	public static HashMap<String, HashSet<Value>> globalVar2MultiThrdCls;
	public static HashMap<SootClass, HashSet<SootClass>> childrenTable;
	public static ArrayList<String> sinkMetds = new ArrayList<String>();
	public static ArrayList<String> vsaMetds = new ArrayList<String>();
	public static HashMap<String, HashSet<Integer>> inputMetds2TaintedVar = new HashMap<String, HashSet<Integer>>(); 
	public static ArrayList<String> inputMetds = new ArrayList<String>();
	public static QuestionGenerator qg = null;
	public static HashSet<String> ImmutableClass = new HashSet<String>();
	public static HashSet<String> intrestedSuperClass = new HashSet<String>();
	
	public static HashSet<String> searchedKeys = new HashSet<>();
	public static boolean reachMaxBCs = false;
	public static final int maxBCs = 2000;
	private List<ARSCFileParser.ResPackage> resourcePackages;

	public static boolean questionTimeout = false;
	public static boolean timeout = false;
	public static HashSet<String> init_taint_res = null;

	public static HashMap<ValuePoint, ArrayList<BacktracingContext>> condition_res = new HashMap<>();


	public static JSONObject target_sinks;

	public static HashSet<String> target_mthd = new HashSet<>();
	public static HashSet<String> target_instr = new HashSet<>();
	
	public static HashMap<String, HashSet<String>> mthd2Tag = new HashMap<>();

	public static HashSet<String> newAddedKeys = new HashSet<>();
	public static HashSet<String> processedKeys = new HashSet<>();;

	public static DGraph dg = new DGraph();

	public static HashSet<String> savedHOs = new HashSet<>();

	// args[0] app package name
	// args[1] android.jar path
	public static void main(String[] args) {
		
		System.out.println("app: " + args[0] + ", android_jar: " + args[1]);

		// String source_file = args[2];
		// String sink_file = args[3];
		
		
		String fp = "";
		fp = args[0];

//		String ajar = "android.jar";
		String ajar = args[1];

		path = fp;
		

		String[] tpn = fp.split("/");
		pn = tpn[tpn.length - 1].substring(0, tpn[tpn.length - 1].length() - 4);
		System.out.println(pn);

		Options.v().set_src_prec(Options.src_prec_apk);
		Options.v().set_process_dir(Collections.singletonList(fp));
		Options.v().set_force_android_jar(ajar);
		Options.v().set_process_multiple_dex(true);
		Options.v().set_android_api_version(24);
		Options.v().set_output_format(Options.output_format_none);
		Options.v().set_force_overwrite(true);
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_whole_program(true);
		Options.v().ignore_resolution_errors();

		Scene.v().loadNecessaryClasses();


		qg = new QuestionGenerator();
		init_taint_res = new HashSet<>();
		
		HashSet<String> svd = qg.generateInputQuestions();
		
		
		CallGraph.init();
		
		// VSA

		ArrayList<ValuePoint> vps = getAllStartValuePoints(new ArrayList<>(svd));
		
		// System.out.print(" VPs size: " + vps.size());

		ArrayList<BackTraceQuestion> btqs = new ArrayList<>();
		vps.forEach(vp -> {btqs.add(new BackTraceQuestion(vp));});

		solveBackTracingQuestions(btqs);

	}


	
	public static void solveBackTracingQuestions(List<BackTraceQuestion> bps) {
		
		TimeUtility.startWatcherBruce(60 * 10);
		int qid = bps.size();
		while (qid > 0) {
			if (runTest.timeout) break;

			qid--;
			BackTraceQuestion bp = bps.get(qid);

			reachMaxBCs = false;
			bp.solve();
			// bp.printResults();
			bp.saveResult();

			ArrayList<BacktracingContext> bcs = runTest.condition_res.get(bp.getStartPoint());
			JSONObject final_result = new JSONObject();
			JSONObject tempobj = new JSONObject();
			


			tempobj.put("startPoint", bp.getStartPoint().getStartStmtPoint().toJSON());
			

			if (bcs != null) {
				for (BacktracingContext bc : bcs) {
					tempobj.append("conditionChains", bc.toCondJSON());
				}

				for (BacktracingContext bc : bcs) {
					ArrayList<JSONObject> t = new ArrayList<>();
					bc.getExecTrace().forEach(stp -> {t.add(stp.toJSON());});
					tempobj.append("DataTraces", (ArrayList<String>)t.clone());
				}

				ArrayList<String> ms;
				ms = new ArrayList<String>();
				for (BacktracingContext bc : bcs) {
					ms.clear();
					bc.getExtendedMthd().forEach(mthd -> {ms.add(mthd.toString());});;
					tempobj.append("methods", (ArrayList<String>)ms.clone());
				}

				final_result.put("backward_result", tempobj);
				FileUtility.wf(pn + "_result.json", final_result.toString(), true);
			}
		
			bps.remove(qid);
			bp = null;


			for (String name : HeapObject.hos.keySet()) {
				if (runTest.savedHOs.contains(name)) continue;
				runTest.savedHOs.add(name);
				HeapObject node = HeapObject.hos.get(name);
				final_result = new JSONObject();
				JSONObject tmpjs = node.toJson();
				final_result.put("field_results", tmpjs);
				FileUtility.wf(pn + "_result.json", final_result.toString(), true);
				node.releaseHO();
			}

		}

		JSONObject final_result = new JSONObject();

		runTest.mthd2Tag.forEach((mthd, tags) -> {
			JSONObject tmpjs = new JSONObject();
			tmpjs.put(mthd, tags);
			final_result.append("method_tags", tmpjs);
		});

		FileUtility.wf(pn + "_result.json", final_result.toString(), true);

			
		
		// saveBackTracingResult();

			// JSONObject final_result = new JSONObject();
			// ArrayList<JSONObject> conditionChainList = new ArrayList<>();
			
			
			// final_result.put("app", pn);
			
			// condition_res.forEach(
			// 	(sp, bcs) -> {
			// 		JSONObject tempobj = new JSONObject();
			// 		ArrayList<ArrayList> templ = new ArrayList<>();
					
					
			// 		tempobj.put("startPoint", sp.getStartStmtPoint().toJSON());
			// 		int ii = 0;
			// 		for (BacktracingContext bc : bcs) {
			// 			templ.add(bc.toCondJSON());
			// 			// Logger.print("  " + ii++ + " " + bc.isDefective() + " " + bc.checkPoint);
			// 		}
					

			// 		templ = new ArrayList<>();

			// 		for (BacktracingContext bc : bcs) {
						
			// 			ArrayList<JSONObject> t = new ArrayList<>();
			// 			bc.getExecTrace().forEach(stp -> {t.add(stp.toJSON());});
			// 			templ.add((ArrayList<String>)t.clone());
			// 		}

			// 		tempobj.put("DataTraces", templ);

			// 		templ = new ArrayList<>();

			// 		ArrayList<String> ms;
			// 		ms = new ArrayList<String>();
			// 		for (BacktracingContext bc : bcs) {
			// 			ms.clear();
			// 			bc.getExtendedMthd().forEach(mthd -> {ms.add(mthd.toString());});;
			// 			templ.add((ArrayList<String>)ms.clone());
			// 		}

					
			// 		tempobj.put("methods", templ);
			// 		// conditionChainList.add(tempobj);
			// 		final_result.append("backward_result", tempobj);
			// 	}
			// );
			
			
			

			// for (HeapObject node : HeapObject.hos.values()) {
				
			// 	JSONObject tmpjs = node.toJson();
			// 	final_result.append("field_results", tmpjs);
			// }
				

			


			// Logger.print(final_result.toString());
			
			
	}


	public static void saveInitResult() {
		
		File f = new File("./" + pn);
//		if(f.exists()) {
//			return;
//		}
		HashSet<String> taint_res = combineTaintRes(init_taint_res);

		for (String result : taint_res) {
			System.out.println(result.toString());
			FileUtility.wf("./" + pn, result.toString(), true);
		}
	}

	static public void parseResource(String fp) throws IOException {
		ARSCFileParser resParser = new ARSCFileParser();
		resParser.parse(fp);
		System.out.println(resParser.findResource(Integer.parseInt("7F0A06D3",16)));

	}

	public static HashSet<String> combineTaintRes(HashSet<String> taint_res) {
		Hashtable<String, String> cres = new Hashtable<String, String>();
		for (String result : taint_res) {
			JSONObject cur_json = new JSONObject(result);
			String tmp_key = cur_json.getJSONObject("source").get("unit").toString();
			tmp_key += cur_json.getJSONObject("source").get("method").toString();
			tmp_key += cur_json.getJSONObject("source").get("unitIndex").toString();
			tmp_key += cur_json.getJSONObject("source").get("RC").toString();
			tmp_key += cur_json.getJSONObject("iniPoint").get("unit").toString();
			tmp_key += cur_json.getJSONObject("iniPoint").get("method").toString();
			tmp_key += cur_json.getJSONObject("iniPoint").get("unitIndex").toString();
			if (!cres.containsKey(tmp_key)) {
				JSONObject tmp_json = new JSONObject();
				tmp_json.put("sinks", cur_json.getJSONArray("sinks"));
				tmp_json.put("source", cur_json.getJSONObject("source"));
				tmp_json.put("originsource", cur_json.getJSONObject("iniPoint"));
				cres.put(tmp_key, tmp_json.toString());
				
			} else {
				JSONObject tmp_json = new JSONObject(cres.get(tmp_key));
				for (Object nsink : cur_json.getJSONArray("sinks")) {
					boolean isHave = false;
					for (Object osink : tmp_json.getJSONArray("sinks")) {
						if (checkSinkJsonStrEquality(nsink.toString(), osink.toString())) {
							isHave = true;
							break;
						}
					}
					if (!isHave) {
						tmp_json.getJSONArray("sinks").put((JSONObject) nsink);
					}
				}
				cres.put(tmp_key, tmp_json.toString());
			}
		}
		HashSet<String> ret_res = new HashSet<String>();
		for (String tkey : cres.keySet()) {
			ret_res.add(cres.get(tkey).toString());
		}
		return ret_res;
		

	}
	
	public static void readSourceFromFile(String path) throws IOException {
        BufferedReader reader;
        reader = new BufferedReader(new FileReader(path));
        String line = reader.readLine();
        while (line != null && line.length() > 0) {
            inputMetds.add(String.join("", "<", line, ">"));
            line = reader.readLine();
        }
        reader.close();
	}

	public static boolean checkSinkJsonStrEquality(String jstr1, String jstr2) {
		JSONObject json1 = new JSONObject(jstr1);
		JSONObject json2 = new JSONObject(jstr2);
		if (!json1.getString("unit").equals(json2.getString("unit"))) {
			return false;
		} else if (!json1.getString("method").equals(json2.getString("method"))) {
			return false;
		} else if (!json1.getString("taint_var").equals(json2.getString("taint_var"))) {
			return false;
		} else if (!json1.get("unitIndex").toString().equals(json2.get("unitIndex").toString())) {
			return false;
		}
		return true;
	}

	public static ArrayList<ValuePoint> getAllStartValuePoints(ArrayList<String> tres) {

		String tmp_smtd;
		String tmp_sinstr;
		HashSet<String> tmp_tvar;
		String tmp_rinstr;

		ArrayList<ValuePoint> allvps = new ArrayList<>();
		
		while (tres.size() > 0) {
			String result = tres.get(0);
			tres.remove(0);
			
			Logger.print("Solving: " + result);
			
			m2m = new Hashtable<String, Hashtable<String, String>>();
			JSONObject cur_json = new JSONObject(result);
			JSONArray sinks_arr = cur_json.getJSONArray("sinks");
			for (Object str : sinks_arr) {
				tmp_smtd = ((JSONObject) str).getString("method").trim();
				
				
				tmp_sinstr = ((JSONObject) str).getString("unit").trim();
				
				
				tmp_tvar = getTvarSet(((JSONObject) str).get("taint_var"));

				for (String v : tmp_tvar){
					tmp_rinstr = tmp_sinstr.replace(v, "taintedVariable");
				
					if (!m2m.containsKey(tmp_smtd)) {
						m2m.put(tmp_smtd, new Hashtable<String, String>());
					}
					if (!m2m.get(tmp_smtd).contains(tmp_rinstr)) {
						m2m.get(tmp_smtd).put(tmp_rinstr, tmp_sinstr);
					}
				}

				// Logger.print(m2m.toString());
				
			}
			
			
			
			allvps.addAll(getStartValuePoints(m2m));
		}
		
		return allvps;
	}

	
	public static boolean hasInterestMthd(String inst) {
		for (String iMthd : vsaMetds) {
			if (inst.contains(iMthd)) return true;
		}
		return false;
	}
	
	public static HashSet<String> getTvarSet(Object object) {
		HashSet<String> tmp_tvar = new HashSet<>();
		
		for (Object v : (JSONArray)object)
			tmp_tvar.add(((String)v).trim());
		
		return tmp_tvar;
	}


	public static List<ValuePoint> getStartValuePoints(Hashtable<String, Hashtable<String, String>> m2m2) {
		

		List<ValuePoint> allvps = new ArrayList<ValuePoint>();
		List<ValuePoint> vps = null;
		JSONObject tmp;

		for (String tmtd : m2m2.keySet()) {
			
			vps = ValuePoint.find(dg, tmtd, m2m2.get(tmtd), 10000);
			for (ValuePoint vp : vps)
				allvps.add(vp);
		}
		return allvps;
	}

	// public static HashSet<String> vsa(Hashtable<String, Hashtable<String, String>> m2m2) {

	// 	DGraph dg = new DGraph();

	// 	List<ValuePoint> allvps = new ArrayList<ValuePoint>();
	// 	List<ValuePoint> vps = null;
	// 	JSONObject tmp;

	// 	for (String tmtd : m2m2.keySet()) {
			
	// 		vps = ValuePoint.find(dg, tmtd, m2m2.get(tmtd), 10000);
	// 		for (ValuePoint vp : vps)
	// 			allvps.add(vp);
	// 	}
		
		
	// 	dg.solve(allvps);
		

	// 	HashSet<String> result = new HashSet<String>();

	// 	JSONObject result_json = new JSONObject();

	// 	for (IDGNode tn : dg.getNodes()) {
	// 		if (!tn.isTimeout())
	// 			Logger.print(tn.toString());
	// 	}
		
	// 	HashSet<String> values = new HashSet();

	// 	for (ValuePoint vp : allvps) { // Change to
	// 		Set<String> includedPoints = new HashSet<String>();
	// 		includedPoints.add(vp.hashCode() + "");
	// 		vp.getDirectAndIndirectDependentsHash(includedPoints);
			
			
	// 		for (IDGNode nd : dg.getNodes())
	// 			if (nd.hasSolved() && includedPoints.contains(nd.hashCode() + "")) {
	// 				tmp = nd.toJson();
	// 				if (vp.hashCode() == nd.hashCode())
	// 					tmp.put("IsRoot", "true");
	// 				result_json.append(vp.hashCode() + "", tmp);
	// 			}
			
	// 	}
		
	// 	FileUtility.wf("./" + pn, result_json.toString(), true);

	// 	return result;
	// }


	public static void saveFinalResult(HashSet<String> taint_res, HashSet<String> vsa_res) {
		JSONObject result = new JSONObject();
//		JSONObject tmp_result = new JSONObject();
		for (String tres : taint_res) {
			JSONObject cur_tres = new JSONObject(tres);
			result.put("package", pn);
			result.put("source", cur_tres.get("source"));
		}
	}

	public static void saveBackTracingResult() {
		JSONObject final_result = new JSONObject();
		ArrayList<JSONObject> conditionChainList = new ArrayList<>();
		final_result.put("app", pn);
		
		condition_res.forEach(
			(sp, bcs) -> {
				JSONObject tempobj = new JSONObject();
				ArrayList<ArrayList> templ = new ArrayList<>();
				
				
				tempobj.put("startPoint", sp.getStartStmtPoint().toJSON());
				int ii = 0;
				for (BacktracingContext bc : bcs) {
					templ.add(bc.toCondJSON());
					// Logger.print("  " + ii++ + " " + bc.isDefective() + " " + bc.checkPoint);
				}
				tempobj.put("conditionChains", templ);

				templ = new ArrayList<>();

				for (BacktracingContext bc : bcs) {
					
					ArrayList<JSONObject> t = new ArrayList<>();
					bc.getExecTrace().forEach(stp -> {t.add(stp.toJSON());});
					templ.add((ArrayList<String>)t.clone());
				}

				tempobj.put("DataTraces", templ);

				templ = new ArrayList<>();

				ArrayList<String> ms;
				ms = new ArrayList<String>();
				for (BacktracingContext bc : bcs) {
					ms.clear();
					bc.getExtendedMthd().forEach(mthd -> {ms.add(mthd.toString());});;
					templ.add((ArrayList<String>)ms.clone());
				}

				
				tempobj.put("methods", templ);
				// conditionChainList.add(tempobj);
				final_result.append("backward_result", tempobj);
			}
		);
		
		
		

		for (HeapObject node : HeapObject.hos.values()) {
			
			JSONObject tmpjs = node.toJson();
			final_result.append("field_results", tmpjs);
			node.releaseHO();
		}
			

		runTest.mthd2Tag.forEach((mthd, tags) -> {
			JSONObject tmpjs = new JSONObject();
			tmpjs.put(mthd, tags);
			final_result.append("method_tags", tmpjs);
		});


		// Logger.print(final_result.toString());
		
		FileUtility.wf(pn + "_result.json", final_result.toString(), true);
		
	}


}
