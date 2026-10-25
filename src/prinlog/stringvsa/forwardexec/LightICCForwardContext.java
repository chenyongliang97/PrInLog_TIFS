package prinlog.stringvsa.forwardexec;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import prinlog.main.runTest;
import prinlog.taintanalysis.solver.CallStackItem;
import prinlog.taintanalysis.solver.StmtItem;
import prinlog.taintanalysis.utility.ListUtility;

import java.util.Set;
import java.util.Stack;

import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.toolkits.graph.Block;

public class LightICCForwardContext{
	SootMethod methodLocation;
	Block blockLocation;
	Unit instructionLocation;

	HashSet<Value> intrestedVariable;	
	
	int invokeLayer;	// The layer of invoke
	int maxAssignStmtCashSize = 10;
	
//	Bruce
	HashSet<Value> curInterestedVariable=null;
	ArrayList<StmtItem> instructionTrace;

	ArrayList<Block> blockTrace;
//	ArrayList<>
	
	Stack<CallStackItem> callStack;

	boolean terminated = false;

	boolean containsSink = false;
	
	boolean isInterestedInBase = false;

	@SuppressWarnings("unchecked")
	public LightICCForwardContext(LightICCForwardContext src) {
		this.methodLocation = src.getMethodLocation();
		this.blockLocation = src.getBlockLocation();
		this.instructionLocation = src.getInstructionLocation();
		this.intrestedVariable = (HashSet<Value>) src.getIntrestedVariable().clone();

		this.blockTrace = (ArrayList<Block>) src.getBlockTrace().clone();
		this.instructionTrace = (ArrayList<StmtItem>) src.getInstructionTrace().clone();
		this.callStack = (Stack<CallStackItem>) src.getCallStack().clone();
		this.invokeLayer = src.invokeLayer;
		this.containsSink = src.isContainsSink();
		this.curInterestedVariable = (HashSet<Value>) src.getCurInterestedVariable().clone();
	}

	public LightICCForwardContext(SootMethod methodLocation, Block blockLocation, Unit instructionLocation) {
		this.intrestedVariable = new HashSet<Value>();
		this.instructionTrace = new ArrayList<StmtItem>();
		this.blockTrace = new ArrayList<Block>();
		this.callStack = new Stack<CallStackItem>();
		this.methodLocation = methodLocation;
		this.setBlockLocation(blockLocation);
		this.instructionLocation = instructionLocation;
		this.curInterestedVariable = new HashSet<>();
		add2InstructionTrace(methodLocation, blockLocation, instructionLocation, true);
		this.invokeLayer = 0;
	}

	public SootMethod getMethodLocation() {
		return methodLocation;
	}

	public void setMethodLocation(SootMethod methodLocation) {
		this.methodLocation = methodLocation;
	}

	public Block getBlockLocation() {
		return blockLocation;
	}

	public void setBlockLocation(Block blockLocation) {
		this.blockLocation = blockLocation;
		blockTrace.add(blockLocation);
	}

	public Unit getInstructionLocation() {
		return instructionLocation;
	}

	public void setInstructionLocation(Unit instructionLocation) {
		this.instructionLocation = instructionLocation;
	}

	public boolean isTerminated() {
		return terminated;
	}

	public void setTerminated(boolean terminated) {
		this.terminated = terminated;
	}
	
	public HashSet<Value> getIntrestedVariable() {
		return intrestedVariable;
	}

	public void setIntrestedVariable(HashSet<Value> intrestedVariable) {
		this.intrestedVariable = (HashSet<Value>) intrestedVariable.clone();
	}

	public void addIntrestedVariable(Value v) {
		this.intrestedVariable.add(v);
	}
	
	public void removeIntrestedVariable(Value var) {
		this.getIntrestedVariable().remove(var);
	}
	
	public void addAllIntrestedVariable(HashSet<Value> intrestedVariables) {
		this.intrestedVariable.addAll(intrestedVariables);
	}

	public boolean isIntrested(Value var) {
		
		return getIntrestedVariable().contains(var);
	}
	
	public boolean containsIntrested(List<Value> intrs) {
		for (Value val : intrs)
			if (isIntrested(val))
				return true;
		return false;
	}

	public ArrayList<Block> getBlockTrace() {
		return blockTrace;
	}

	public void setBlockTrace(ArrayList<Block> blockTrace) {
		this.blockTrace = blockTrace;
	}

	public ArrayList<StmtItem> getInstructionTrace() {
		return instructionTrace;
	}

	public void setInstructionTrace(ArrayList<StmtItem> instructionTrace) {
		this.instructionTrace = instructionTrace;
	}

	public void add2InstructionTrace(SootMethod methodLocation, Block blockLocation, Unit instructionLocation, boolean containsInteresting) {
		StmtItem sItem = new StmtItem(methodLocation, blockLocation, instructionLocation);
		sItem.setContainsInteresting(containsInteresting);
		this.getInstructionTrace().add(sItem);
	}
	
	public void add2InstructionTraceSink(SootMethod methodLocation, Block blockLocation, Unit instructionLocation, boolean containsInteresting) {
		// Only for recording network getOutputStream
		StmtItem sItem = new StmtItem(methodLocation, blockLocation, instructionLocation);
		sItem.setContainsInteresting(containsInteresting);
		sItem.setContainsSink(true, new HashSet<>());
		this.getInstructionTrace().add(sItem);
	}

	public boolean isContainsSink() {
		return containsSink;
	}

//	public void setContainsSink(boolean containsSink) {
//		this.containsSink = containsSink;
//		this.getInstructionTrace().get(this.getInstructionTrace().size() - 1).setContainsSink(containsSink);
//	}
	
	public void setContainsSink(boolean containsSink, HashSet<Value> curIntst) {
		this.containsSink = containsSink;
//		this.getInstructionTrace().get(this.getInstructionTrace().size() - 1).setContainsSink(containsSink);
		this.getInstructionTrace().get(this.getInstructionTrace().size() - 1).setContainsSink(containsSink, curIntst);
	}

	public Stack<CallStackItem> getCallStack() {
		return callStack;
	}

	public void setCallStack(Stack<CallStackItem> callStack) {
		this.callStack = callStack;
	}
	
	public HashSet<Value> getCurInterestedVariable() {
		return curInterestedVariable;
	}

//	public void setCurInterestedVariable(Value curInterestedVariable) {
	public void addCurInterestedVariable(Value curInterestedVariable) {
		this.curInterestedVariable.add(curInterestedVariable);
	}
	
	public void resetCurInterestedVariable() {
		this.curInterestedVariable = new HashSet<>();
	}


	
}
