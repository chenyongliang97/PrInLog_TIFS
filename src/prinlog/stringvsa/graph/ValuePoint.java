package prinlog.stringvsa.graph;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import org.json.JSONObject;

import prinlog.stringvsa.backwardslicing.BackwardContext;
import prinlog.stringvsa.backwardslicing.BackwardController;
import prinlog.stringvsa.backwardslicing.DataSourceType;
import prinlog.stringvsa.base.StmtPoint;
import prinlog.stringvsa.base.TargetType;
import prinlog.stringvsa.forwardexec.SimulateEngine;
import prinlog.stringvsa.utility.Logger;
import prinlog.taintanalysis.solver.CallStackItem;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DoubleConstant;
import soot.jimple.FieldRef;
import soot.jimple.FloatConstant;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.LongConstant;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.toolkits.graph.Block;

public class ValuePoint implements IDGNode {

	DGraph dg;

	SootMethod method_location;
	Block block_location;
	Unit instruction_location;
	HashSet<Integer> target_regs = new HashSet<Integer>();
	List<BackwardContext> bcs = new ArrayList<>();
	HashMap<HashMap<Integer, HashSet<String>>, BackwardContext> simulatedRess = new HashMap<HashMap<Integer, HashSet<String>>, BackwardContext>();

	HashSet<BackwardContext> solvedBCs = new HashSet<BackwardContext>();

	StmtPoint startStmtPoint;

	Object appendix = "";

	public Stack<CallStackItem> referenceCallTrace = null;

	ArrayList<HashMap<Integer, HashSet<String>>> result = new ArrayList<HashMap<Integer, HashSet<String>>>();

	boolean inited = false;
	boolean solved = false;

	public ValuePoint(DGraph dg, SootMethod method_location, Block block_location, Unit instruction_location,
			List<Integer> regIndex) {
		this.dg = dg;
		this.method_location = method_location;
		this.block_location = block_location;
		this.instruction_location = instruction_location;
		for (int i : regIndex) {
			target_regs.add(i);
		}
		dg.addNode(this);

		startStmtPoint = new StmtPoint(method_location, block_location, instruction_location);
	}

	public StmtPoint getStartStmtPoint() {
		return this.startStmtPoint;
	}

	public DGraph getDg() {
		return dg;
	}

	public List<BackwardContext> getBcs() {
		return bcs;
	}

	public SootMethod getMethod_location() {
		return method_location;
	}

	public Block getBlock_location() {
		return block_location;
	}

	public Unit getInstruction_location() {
		return instruction_location;
	}

	public Set<Integer> getTargetRgsIndexes() {
		return target_regs;
	}

	public void setAppendix(Object str) {
		appendix = str;
	}

	@Override
	public Set<IDGNode> getDependents() {
		// TODO Auto-generated method stub

		HashSet<IDGNode> dps = new HashSet<IDGNode>();
		for (BackwardContext bc : bcs) {
			for (IDGNode node : bc.getDependentHeapObjects()) {
				dps.add(node);
			}
		}
		return dps;
	}

	@Override
	public int getUnsovledDependentsCount() {
		// TODO Auto-generated method stub
		int count = 0;
		for (IDGNode node : getDependents()) {
			if (!node.hasSolved()) {
				count++;
			}
		}
		Logger.print(this.hashCode() + "[]" + count + " " + bcs.size());
		return count;
	}

	@Override
	public boolean hasSolved() {

		return solved;
	}

	@Override
	public boolean canBePartiallySolve() {
		boolean can = false;
		boolean dsolved;
		SimulateEngine tmp;
		for (BackwardContext bc : bcs) {
			if (!solvedBCs.contains(bc)) {
				dsolved = true;
				for (HeapObject ho : bc.getDependentHeapObjects()) {
					if (!ho.hasSolved()) {
						dsolved = false;
						break;
					}
				}

				if (dsolved) {
					solvedBCs.add(bc);
					can = true;
					tmp = new SimulateEngine(dg, bc);
					tmp.simulate();
					mergeResult(bc, tmp);
				}
			}
		}
		if (can) {
			solved = true;
		}

		return can;
	}

	@Override
	public void solve() {
		solved = true;
		Logger.print("[SOLVING ME]" + this.hashCode());
		SimulateEngine tmp;
		HashMap<Integer, HashSet<String>> resl;
		for (BackwardContext var : this.getBcs()) {
			tmp = new SimulateEngine(dg, var);
			tmp.simulate();
			resl = mergeResult(var, tmp);

			simulatedRess.put(resl, var);
			result.add(resl);
		}

	}

	public HashMap<Integer, HashSet<String>> mergeResult(BackwardContext var, SimulateEngine tmp) {
		HashMap<Value, HashSet<String>> sval = tmp.getCurrentValues();
		HashMap<Integer, HashSet<String>> resl = new HashMap<Integer, HashSet<String>>();
		Value reg;
		for (int i : target_regs) {
			if (i == TargetType.RIGHTPART.getType()) {
				reg = ((AssignStmt) var.getStmtPathTail()).getRightOp();
			} else if (i == TargetType.BASEOBJECT.getType()) {
				reg = ((soot.jimple.InstanceInvokeExpr) ((Stmt) var.getStmtPathTail()).getInvokeExpr()).getBase();
			} else {
				reg = ((Stmt) var.getStmtPathTail()).getInvokeExpr().getArg(i);
			}

			if (sval.containsKey(reg)) {
				resl.put(i, sval.get(reg));
			} else if (reg instanceof StringConstant) {
				resl.put(i, new HashSet<String>());
				resl.get(i).add(((StringConstant) reg).value);
			} else if (reg instanceof IntConstant) {
				resl.put(i, new HashSet<String>());
				resl.get(i).add(((IntConstant) reg).value + "");
			} else if (reg instanceof LongConstant) {
				resl.put(i, new HashSet<String>());
				resl.get(i).add(((LongConstant) reg).value + "");
			} else if (reg instanceof FloatConstant) {
				resl.put(i, new HashSet<String>());
				resl.get(i).add(((FloatConstant) reg).value + "");
			} else if (reg instanceof DoubleConstant) {
				resl.put(i, new HashSet<String>());
				resl.get(i).add(((DoubleConstant) reg).value + "");
			}
		}
		return resl;
	}

	@Override
	public boolean inited() {
		return inited;
	}

	@Override
	public void initIfHavenot() {
		inited = true;
		// System.out.println("Solving VP: " + startStmtPoint.getInstruction_location());
		bcs = BackwardController.getInstance().doBackWard(this, dg);
		
		
	}



	@Override
	public ArrayList<HashMap<Integer, HashSet<String>>> getResult() {
		return result;
	}


	// Bruce
	public static List<ValuePoint> find(DGraph dg, String mtd, Hashtable<String, String> instrs, int maxsize) {
		List<ValuePoint> vps = new ArrayList<ValuePoint>();
		List<StmtPoint> sps;
		HashMap<String, List<Integer>> regIndex = new HashMap<>();
		String signature;

		String ttins = null;
		
		for (String tins : instrs.keySet()) {
			
			String instr = instrs.get(tins);
			
			if (!regIndex.containsKey(instr))
				regIndex.put(instr, new ArrayList());
			
			
			
			String tmps = tins.substring(tins.indexOf(")>(") + 3, tins.lastIndexOf(")"));
			
			
			int cc = 0;
			for (String i : tmps.split(",")) {
				if (i.trim().equals("taintedVariable")) {
					regIndex.get(instr).add(cc);
					break;
				}
				cc++;
			}
			

			
			if (tins.contains("taintedVariable.<")) regIndex.get(instr).add(TargetType.BASEOBJECT.getType()); // base obj
		}

		// Logger.print(regIndex.toString());
//		pauseWhile();
		
		ValuePoint tmp;
		
		for (String tins : regIndex.keySet()) {
			
			sps = null;
			signature = getSignature(tins);
			sps = StmtPoint.findCaller(signature);
			
			Logger.print("Signature: " + signature);

			if (sps.size() == 0) {
				System.out.println("NO Caller");
				continue;
			}
			
			for (StmtPoint sp : sps) {
				if (sp.getMethod_location().toString().equals(mtd)
						&& tins.equals(sp.getInstruction_location().toString().trim())) {
//						System.out.println(sp.getMethod_location() + " " + sp.getInstruction_location() + " " + regIndex);
					tmp = new ValuePoint(dg, sp.getMethod_location(), sp.getBlock_location(),
							sp.getInstruction_location(), regIndex.get(tins));
					tmp.setAppendix(signature);
					vps.add(tmp);
					if (maxsize != -1 && vps.size() >= maxsize)
						break;
				}
			}
			
		}
		
		
		
		return vps;
	}

	public static String getSignature(String instruction) {
		String signature = instruction.substring(instruction.indexOf("<"), instruction.indexOf(">") + 1);
		
		return signature;
	}


	

	public static boolean hasVP(List<ValuePoint> vps, ValuePoint vp) {
		for (ValuePoint lvp : vps) {
			if (lvp.getMethod_location().toString().equals(vp.getMethod_location().toString())
					&& (lvp.getInstruction_location().toString().equals(vp.getInstruction_location().toString()))) {
				return true;
			}
		}
		return false;
	}

	public void print() {

		System.out.println("===============================================================");
		System.out.println("Class: " + method_location.getDeclaringClass().toString());
		System.out.println("Method: " + method_location.toString());
		System.out.println("Bolck: ");
		block_location.forEach(u -> {
			System.out.println("       " + u);
		});
		target_regs.forEach(u -> {
			System.out.println("              " + u);
		});

	}

	public String toString() {
		if (!inited)
			return super.toString();
		StringBuilder sb = new StringBuilder();
		sb.append("===========================");
		sb.append(this.hashCode());
		sb.append("===========================\n");
		sb.append("Class: " + method_location.getDeclaringClass().toString() + "\n");
		sb.append("Method: " + method_location.toString() + "\n");
		sb.append("Target: " + instruction_location.toString() + "\n");
		sb.append("Solved: " + hasSolved() + "\n");
		sb.append("Depend: ");
		for (IDGNode var : this.getDependents()) {
			sb.append(var.hashCode());
			sb.append(", ");
		}
		sb.append("\n");
		sb.append("BackwardContexts: \n");
		BackwardContext tmp;
		for (int i = 0; i < this.bcs.size(); i++) {
			tmp = this.bcs.get(i);
			sb.append("  " + i + " " + tmp.hashCode() + "\n");
			for (StmtPoint stmt : tmp.getExecTrace()) {
				sb.append("    " + stmt.getInstruction_location() + "\n");
			}
			
		}
		sb.append("ValueSet: \n");
		for (HashMap<Integer, HashSet<String>> resl : result) {
			sb.append("  ");
			for (int i : resl.keySet()) {
				sb.append(" |" + i + ":");
				for (String str : resl.get(i)) {
					sb.append(str + ",");
				}
			}
			sb.append("\n");
		}
		return sb.toString();
	}

	public JSONObject toJson2() {
		JSONObject js = new JSONObject();
		JSONObject tmp;
		for (HashMap<Integer, HashSet<String>> var : this.getResult()) {
			tmp = new JSONObject();
//			tmp.put("CorrespondingBackwardContext", simulatedRess.get(var).hashCode());
			for (int i : var.keySet()) {
				for (String str : var.get(i)) {
					tmp.append(i + "", str);
				}
			}
			js.append("values", tmp);
		}
		if (bcs != null)
			for (BackwardContext bc : bcs) {
//				js.append("BackwardContexts", bc.toJson());
			}

		for (DataSourceType i : this.getDataSrcs()) {
			js.append("src", i.name());
		}

//		js.put("hashCode", this.hashCode() + "");
		js.put("method", this.getMethod_location().toString());
//		js.put("Block", this.getBlock_location().hashCode());
		js.put("unit", this.getInstruction_location());
//		js.put("UnitHash", this.getInstruction_location().hashCode());
//		js.put("appendix", appendix);

		return js;
	}

	public JSONObject toJson() {
		JSONObject js = new JSONObject();
		BackwardContext tmp_bc;
		
		
		js.put("HashCode", this.hashCode());
		js.put("Type", "ValuePoint");
		js.put("Class", method_location.getDeclaringClass().toString());
		js.put("Method", method_location.toString());
		js.put("Target", instruction_location.toString());
		
		js.put("Solved", hasSolved());

		for (int i = 0; i < this.bcs.size(); i++) {
			tmp_bc = this.bcs.get(i);
			ArrayList<JSONObject> path = new ArrayList<>();
			
			for (StmtPoint stmt : tmp_bc.getExecTrace()) {
				// Unit instr = stmt.getInstruction_location();
				// JSONObject stmt_js = new JSONObject();
				
				// SootClass sc = null;
				// sc = stmt.getMethod_location().getDeclaringClass();
				
				
				// stmt_js.put("Method", stmt.getMethod_location().toString());
				// stmt_js.put("Class", sc.toString());
				// stmt_js.put("Instr", instr.toString());
				
				
				path.add(stmt.toJSON());
			}
			
			
				// JSONObject tmp_js = new JSONObject();
				// tmp_js.append("Trace", path);
				js.append("ExecTrace", path);
			
		}
		
		return js;
		 
	}

	@Override
	public Set<IDGNode> getDirectAndIndirectDependents(Set<IDGNode> ret) {
		// TODO Auto-generated method stub
		for (IDGNode i : this.getDependents()) {
			if (!ret.contains(i)) {
				ret.add(i);
				i.getDirectAndIndirectDependents(ret);
			}
		}
		return ret;
	}

	@Override
	public HashSet<DataSourceType> getDataSrcs() {
		Set<IDGNode> dps = new HashSet<IDGNode>();
		getDirectAndIndirectDependents(dps);

		HashSet<DataSourceType> toRet = new HashSet<DataSourceType>();
		for (IDGNode i : dps) {
			if (i instanceof ValuePoint) {
				for (BackwardContext bc : ((ValuePoint) i).getBcs()) {
					toRet.addAll(bc.getDataSrcs());
				}
			}
		}

		for (BackwardContext bc : this.getBcs()) {
			toRet.addAll(bc.getDataSrcs());
		}
		return toRet;
	}

	@Override
	public HashSet<String> getDataHcStrings() {
		// TODO Auto-generated method stub
		Set<IDGNode> dps = new HashSet<IDGNode>();
		getDirectAndIndirectDependents(dps);

		HashSet<String> toRet = new HashSet<String>();
		for (IDGNode i : dps) {
			if (i instanceof ValuePoint) {
				for (BackwardContext bc : ((ValuePoint) i).getBcs()) {
					toRet.addAll(bc.getHcStrings());
				}
			}
		}

		for (BackwardContext bc : this.getBcs()) {
			toRet.addAll(bc.getHcStrings());
		}
		return toRet;
	}

	public void setReferenceTrace(Stack<CallStackItem> cs) {
		this.referenceCallTrace = cs;
	}

}
