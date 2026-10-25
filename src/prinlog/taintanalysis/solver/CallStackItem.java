package prinlog.taintanalysis.solver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import prinlog.taintanalysis.utility.ListUtility;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InvokeExpr;
import soot.toolkits.graph.Block;

public class CallStackItem {
	SootMethod smethd;
	Block blcok;
	Unit currentInstruction;
	Value returnTarget;
	String interfName;
	InvokeExpr invokExpr;

	HashSet<Value> intrestedValues;

	@SuppressWarnings("unchecked")
	public CallStackItem(SootMethod smethd, Block blcok, Unit currentInstruction, Value returnTarget, HashSet<Value> intrestedValues,
			InvokeExpr invokExpr) {
		super();
		this.smethd = smethd;
		this.blcok = blcok;
		this.currentInstruction = currentInstruction;
		this.returnTarget = returnTarget;
		
		this.intrestedValues = intrestedValues;
		this.invokExpr = invokExpr;
	}

	public SootMethod getSmethd() {
		return smethd;
	}

	public void setSmethd(SootMethod smethd) {
		this.smethd = smethd;
	}

	public Block getBlcok() {
		return blcok;
	}

	public void setBlcok(Block blcok) {
		this.blcok = blcok;
	}

	public Unit getCurrentInstruction() {
		return currentInstruction;
	}

	public void setCurrentInstruction(Unit currentInstruction) {
		this.currentInstruction = currentInstruction;
	}

	public Value getReturnTarget() {
		return returnTarget;
	}

	public void setReturnTarget(Value returnTarget) {
		this.returnTarget = returnTarget;
	}
	
	
	public HashSet<Value> getInterestedValues() {
		return this.intrestedValues;
	}
	
	public InvokeExpr getInvokeExpr() {
		return this.invokExpr;
	}
	
}
