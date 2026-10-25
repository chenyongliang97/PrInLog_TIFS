package prinlog.stringvsa.base;

import java.awt.print.Printable;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.json.JSONObject;

import com.google.common.collect.ContiguousSet;

import prinlog.stringvsa.graph.CallGraph;
import prinlog.stringvsa.graph.CallGraphNode;
import prinlog.stringvsa.main.Config;
import prinlog.stringvsa.utility.BlockGenerator;
import prinlog.stringvsa.utility.BlockUtility;
import prinlog.stringvsa.utility.Logger;
import prinlog.stringvsa.utility.MethodUtility;
import soot.PatchingChain;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.ValueBox;
import soot.dava.internal.AST.ASTTryNode.container;
import soot.jimple.FieldRef;
import soot.jimple.Stmt;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;

public class StmtPoint {
	SootMethod method_location;
	Block block_location;
	Unit instruction_location;
	String ICC = null;


	SootField sootField = null;

	public StmtPoint(SootMethod method_location, Block block_location, Unit instruction_location) {
		super();
		this.method_location = method_location;
		this.block_location = block_location;
		this.instruction_location = instruction_location;
	}

	public SootMethod getMethod_location() {
		return method_location;
	}

	public void setMethod_location(SootMethod method_location) {
		this.method_location = method_location;
	}

	public Block getBlock_location() {
		return block_location;
	}

	public void setBlock_location(Block block_location) {
		this.block_location = block_location;
	}

	public Unit getInstruction_location() {
		return instruction_location;
	}

	public void setInstruction_location(Unit instruction_location) {
		this.instruction_location = instruction_location;
	}

	public void setField(SootField sf) {
		this.sootField = sf;
	}

	public void setICC(String s) {
		this.ICC = s;
	}

	public static List<StmtPoint> findCaller(String signature) {
		List<StmtPoint> sps = new ArrayList<StmtPoint>();
		
		HashSet<SootMethod> ms = new HashSet<SootMethod>();
		SootMethod sm = null;

		// Logger.print("Finding signature: " + signature);

		try {
			sm = Scene.v().getMethod(signature);
		} catch (Exception e) {
			// Logger.print(e.toString());
			return sps;
		}

		if (sm == null) {
			Logger.printW("[Failed Find Caller: No Caller] " + signature);
			return sps;
		}

		ms.add(sm);
		if (Config.PARSEINTERFACECALL && sm.getName().charAt(0) != '<') {
			MethodUtility.findAllPointerOfThisMethod(ms, sm.getSubSignature(), sm.getDeclaringClass());
		}
		
		CallGraphNode node;
		CompleteBlockGraph cbg;
		Block block;
		for (SootMethod tmpm : ms) {
			String className = tmpm.getDeclaringClass().toString();
			
			if (className.startsWith("android.") || className.startsWith("java.") || className.startsWith("androidx.")) {
				continue;
			}

			node = CallGraph.getNode(tmpm.toString());
			if (node == null)
				continue;
			for (CallGraphNode bn : node.getCallBy()) {
				PatchingChain<Unit> us = bn.getSmthd().retrieveActiveBody().getUnits();
				for (Unit unit : us) {
					if (unit instanceof Stmt) {
						if (((Stmt) unit).containsInvokeExpr()) {
							if (((Stmt) unit).getInvokeExpr().getMethod() == node.getSmthd()) {
								cbg = BlockGenerator.getInstance().generate(bn.getSmthd().retrieveActiveBody());
								block = BlockUtility.findLocatedBlock(cbg, unit);
								sps.add(new StmtPoint(bn.getSmthd(), block, unit));
								
							}
						}
					}
				}
			}
		}
		return sps;
	}

	public static List<StmtPoint> findSetter(SootField sootField) {
		List<StmtPoint> sps = new ArrayList<StmtPoint>();

		HashSet<SootMethod> mthdes = CallGraph.getSetter(sootField);
		CompleteBlockGraph cbg;
		Block block;
		if (mthdes != null) {
			for (SootMethod mthd : mthdes) {
				PatchingChain<Unit> us = mthd.retrieveActiveBody().getUnits();
				for (Unit unit : us) {
					if (unit instanceof Stmt) {
						for (ValueBox vbox : ((Stmt) unit).getDefBoxes()) {
							if (vbox.getValue() instanceof FieldRef
									&& ((FieldRef) vbox.getValue()).getField() == sootField) {
								cbg = BlockGenerator.getInstance().generate(mthd.retrieveActiveBody());
								block = BlockUtility.findLocatedBlock(cbg, unit);
								sps.add(new StmtPoint(mthd, block, unit));
							}
						}
					}
				}
			}
		} else {
			Logger.printW("no Setter " + sootField);
		}

		return sps;
	}

	public JSONObject toJSON() {
		JSONObject js = new JSONObject();
		js.put("method", this.getMethod_location());
		js.put("block", this.getBlock_location().getIndexInMethod());
		js.put("stmt", this.getInstruction_location());
		js.put("field", this.sootField);
		js.put("ICC", ICC);
		return js;
	}

	public boolean sameWith(StmtPoint sp) {
		return this.getBlock_location().equals(sp.getBlock_location())
		&& this.getMethod_location().equals(sp.getMethod_location())
		&& this.getInstruction_location().equals(sp.getInstruction_location());
	}

}
