package prinlog.taintanalysis.base;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.jf.smali.smaliParser.debug_directive_return;

import prinlog.main.runTest;
import prinlog.stringvsa.forwardexec.LightICCForwardContext;
import prinlog.taintanalysis.solver.SimulationContext;
import prinlog.taintanalysis.solver.TaintQuestionSolver;
import prinlog.taintanalysis.utility.ListUtility;
import soot.Scene;
import soot.SootMethod;
import soot.Value;
import soot.jimple.StringConstant;

public class TaintQuestion {
	String targetKey;
	SourcePoint sourcep;
	List<LightICCForwardContext> sContexts = new ArrayList<>();
	boolean hasSolved = false;
	
	
	public TaintQuestion(SourcePoint sourcep, Value targetKey) {
		if (targetKey instanceof StringConstant)
			this.targetKey = ((StringConstant) targetKey).value;
		
			setSourcep(sourcep);
		
		LightICCForwardContext sc = new LightICCForwardContext(sourcep.getMethodLocation(), sourcep.getBlockLocation(), sourcep.getInstructionLocation());

		HashSet<String> set = new HashSet<>();
		
		sc.addIntrestedVariable(sourcep.getTartgetValue());
		sContexts.add(sc);

	}

	

	public SourcePoint getSourcep() {
		return sourcep;
	}
	
	public void setSourcep(SourcePoint sourcep) {
		this.sourcep = sourcep;
	}

	public List<LightICCForwardContext> getsContexts() {
		return sContexts;
	}

	public void addSContexts(List<LightICCForwardContext> list) {
		for (LightICCForwardContext sc : sContexts)
			if (!this.sContexts.contains(sc)) this.sContexts.add(sc);
	}

	public boolean isPositive() {
		for (LightICCForwardContext sContext : sContexts) {
			if(sContext.isContainsSink())
				return true;
		}
		return false;
	}
	
	public void setHasSolved() {
		this.hasSolved = true;
	}

	public boolean hasSolved() {
		return this.hasSolved;
	}

	public String getTargetKey() {
		return this.targetKey;
	}
}



