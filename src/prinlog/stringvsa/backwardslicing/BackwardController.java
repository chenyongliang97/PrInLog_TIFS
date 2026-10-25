package prinlog.stringvsa.backwardslicing;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;

import prinlog.main.runTest;
import prinlog.stringvsa.base.StmtPoint;
import prinlog.stringvsa.graph.ConditionBlock;
import prinlog.stringvsa.graph.DGraph;
import prinlog.stringvsa.graph.ValuePoint;
import prinlog.stringvsa.main.Config;
import prinlog.stringvsa.utility.Logger;
import soot.toolkits.graph.Block;


public class BackwardController {
	static BackwardController sc = new BackwardController();

	public static BackwardController getInstance() {
		return sc;
	}

	private BackwardController() {

	}

	public static void main(String[] args) {
		// TODO Auto-generated method stub

	}

	public List<BackwardContext> doBackWard(ValuePoint vp, DGraph dg) {
		List<BackwardContext> bcs = new ArrayList<BackwardContext>();
		bcs.add(new BackwardContext(vp, dg));

		BackwardContext bc;
		while (!runTest.timeout) {

			bc = null;
			for (BackwardContext tmp : bcs) {
				if (!tmp.backWardHasFinished()) {
					bc = tmp;
					break;
				}
			}
			if (bc == null) {
				break;
			}
			bcs.addAll(bc.oneStepBackWard());
			Random rand = new Random();

			while (bcs.size() > 20)
				bcs.remove(rand.nextInt(bcs.size()));
			
		}


		
		List<BackwardContext> cachedBcs = new ArrayList<>();
		if (bcs.size() > 0) cachedBcs.add(bcs.get(0));
		for (int i = 1; i < bcs.size(); i++){
			boolean hasSame = false;
			for (int j = 0; j < cachedBcs.size(); j++) {
				if (isTheSame(cachedBcs.get(j), bcs.get(i))) {
					hasSame = true;
					break;
				}
			}
			if (!hasSame) cachedBcs.add(bcs.get(i));
		}

		bcs = cachedBcs;

		// bcs.forEach(var -> {
		// 	var.printExceTrace();
		// });

		return bcs;

	}


	public boolean isTheSame(BackwardContext b1, BackwardContext b2) {

		ArrayList<StmtPoint> trace1 = b1.getExecTrace();
		ArrayList<StmtPoint> trace2 = b2.getExecTrace();

		if (trace1.size() != trace2.size()) return false;
		for (int i = 0; i < trace1.size(); i++)	
			if (!trace1.get(i).sameWith(trace2.get(i))) return false;

		return true;
	}

	public void doBackTracing(List<BacktracingContext> bcs) {
		
		// return bcs;

		// long stime = System.currentTimeMillis();
		BacktracingContext bc;
		int dbcsize = 0;
		int lastbcsize = bcs.size();

		while (dbcsize < runTest.maxBCs && !runTest.timeout) {
			List<Integer> delList = new ArrayList<>();
			for (int i = bcs.size() - 1; i >= 0; i--) {
				if (bcs.get(i).isDefective()) delList.add(i);
			}

			for (int i : delList)
				bcs.remove(i);
				
			bc = null;
			for (BacktracingContext tmp : bcs) {
				if (!tmp.backWardHasFinished()) {
					bc = tmp;
					break;
				}
			}

			

			if (bc == null) {
				break;
			}
			bcs.addAll(bc.oneStepBackWard());

			
			dbcsize = bcs.size() - lastbcsize;
			// Logger.print("Now bcs size: " + bcs.size() + " Incremented: " + dbcsize);

			// bcs.forEach(b -> {
			// 	Logger.print("====================");
			// 	b.getConditionChain().forEach(cb -> {
			// 		Logger.print(" ---- \n" + cb.getUnsolvedField().toString());
			// 		Logger.print(" Intersted Var: " + cb.getInterestedVariables().toString());
			// 	});
			// });

			// if (Config.BackwardContextTimeOut != -1 && System.currentTimeMillis() - stime > Config.BackwardContextTimeOut) {
			// 	for (BacktracingContext tmp : bcs) {
			// 		tmp.finished();
			// 	}
			// }
		}

	}

}
