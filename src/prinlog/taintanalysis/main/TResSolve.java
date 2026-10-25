package prinlog.taintanalysis.main;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import org.json.JSONObject;

import prinlog.main.runTest;
import prinlog.stringvsa.forwardexec.LightICCForwardContext;
import prinlog.taintanalysis.base.TaintQuestion;
import prinlog.taintanalysis.solver.SimulationContext;
import prinlog.taintanalysis.solver.StmtItem;
import prinlog.taintanalysis.utility.FileUtility;
import prinlog.taintanalysis.utility.MethodUtility;

public class TResSolve {

	@SuppressWarnings("unchecked")
	public static HashSet<String> saveSolved(List<TaintQuestion> solved) {

		HashSet<String> svd = new HashSet<String>();
		ArrayList<StmtItem> stmts;
		String tmp;
		for (TaintQuestion tq : solved) {

			JSONObject source = new JSONObject();
			source.put("method", tq.getSourcep().getMethodLocation().toString());
			source.put("unit", tq.getSourcep().getInstructionLocation().toString());
			source.put("unitIndex", MethodUtility.getUnitIndex(tq.getSourcep().getMethodLocation(), tq.getSourcep().getInstructionLocation()));

			for (LightICCForwardContext sc : tq.getsContexts()) {
				if (sc.isContainsSink()) {

					JSONObject ret = new JSONObject();
					ret.put("package", runTest.pn);
					ret.put("source", source);

					stmts = (ArrayList<StmtItem>) sc.getInstructionTrace().clone();
					for (StmtItem stmt : stmts)
						if (stmt.isContainsSink()) {

							JSONObject sink = new JSONObject();
							sink.put("method", stmt.getSm().toString());
							sink.put("unit", stmt.getU());
							sink.put("unitIndex", MethodUtility.getUnitIndex(stmt.getSm(), stmt.getU()));
							
							if (stmt.getCurIntst() != null)
								sink.put("taint_var", stmt.getCurIntst());
							ret.append("sinks", sink);

						}
					tmp = ret.toString();
					if (!svd.contains(tmp)) {
						svd.add(tmp);
//						FileUtility.wf("taintResTmp.txt", tmp, true);
					}
				}
			}
		}
		return svd;
		
	}

}
