package prinlog.stringvsa.forwardexec;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import prinlog.main.runTest;
import prinlog.stringvsa.graph.HeapObject;
import prinlog.stringvsa.graph.ValuePoint;
import prinlog.taintanalysis.base.TaintQuestion;
import prinlog.taintanalysis.solver.CallStackItem;
import prinlog.taintanalysis.utility.BlockGenerator;
import prinlog.taintanalysis.utility.Logger;
import prinlog.taintanalysis.utility.MethodUtility;
import soot.Body;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AbstractStmtSwitch;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;

public class LightICCForwardEngine extends AbstractStmtSwitch {
	int print_count = 0;
	int maxInvokeLayer = 6;
	TaintQuestion tq;
	static LightICCForwardEngine se = new LightICCForwardEngine();

	
	private LightICCForwardEngine() {
	}

	public static LightICCForwardEngine getInstance() {
		return se;
	}


	public List<LightICCForwardContext> oneStepForward(TaintQuestion tq, LightICCForwardContext sContext) {
		this.tq = tq;
		Unit nextInstrct = null;

		if (sContext.getIntrestedVariable().isEmpty()) {
			sContext.setTerminated(true);
			return new ArrayList<LightICCForwardContext>();
		}

		if (sContext.getInstructionLocation() == null) {
			nextInstrct = sContext.getBlockLocation().getHead();
		} else {
			nextInstrct = sContext.getBlockLocation().getSuccOf(sContext.getInstructionLocation());
		}

		Logger.print("nextInstrct: " + nextInstrct + "");
		if (nextInstrct != null) {
			return oneStepForward(sContext, nextInstrct);
		} else {
			Logger.print(sContext.getBlockLocation().getIndexInMethod() + "=>>");
			List<Block> processableBlocks = getProcessableBlocks(sContext);
			for (Block b : sContext.getBlockTrace())
				Logger.print("t:" + b.getIndexInMethod() + "\t" + b.getBody().getMethod());
			for (Block b : processableBlocks)
				Logger.print(b.getIndexInMethod() + "");
			// if(processableBlocks.size() !=
			// sContext.getBlockLocation().getSuccs().size())
			// System.exit(0);
			if (!processableBlocks.isEmpty()) {
				return oneStepForward2EachBlock(sContext, processableBlocks);
			} else {
				// backtofunc
				sContext.setTerminated(true);
			}
		}

		return new ArrayList<LightICCForwardContext>();
	}

	private List<Block> getProcessableBlocks(LightICCForwardContext sContext) {
		List<Block> allBlocks = sContext.getBlockLocation().getSuccs();
		List<Block> bs = new ArrayList<Block>();
		Block tmp;
		boolean canprocess;
		for (Block block : allBlocks) {
			canprocess = true;
			HashSet<Block> hist = new HashSet<Block>();
			ListIterator<Block> li = sContext.getBlockTrace().listIterator(sContext.getBlockTrace().size());
			li.previous();// skip current
			while (li.hasPrevious()) {
				tmp = li.previous();
				if (!tmp.getBody().equals(sContext.getBlockLocation().getBody()))
					break;

				if (tmp == block) {
					if (hist.contains(tmp)) {
						canprocess = false;
						break;
					} else
						hist.add(block);
				}
			}

			if (canprocess)
				bs.add(block);
		}
		return bs;
	}

	private List<LightICCForwardContext> oneStepForward2EachBlock(LightICCForwardContext sContext,
			List<Block> processableBlocks) {
		List<LightICCForwardContext> newBc = new ArrayList<LightICCForwardContext>();
		List<Block> sBlocks = processableBlocks;// sContext.getBlockLocation().getSuccs();

		for (int i = 1; i < sBlocks.size(); i++) {
			LightICCForwardContext tsc = new LightICCForwardContext(sContext);
			tsc.setBlockLocation(sBlocks.get(i));

			newBc.add(tsc);
			newBc.addAll(oneStepForward(tsc, tsc.getBlockLocation().getHead()));
		}

		sContext.setBlockLocation(sBlocks.get(0));
		newBc.addAll(oneStepForward(sContext, sContext.getBlockLocation().getHead()));

		return newBc;
	}

	LightICCForwardContext sContext;

	private List<LightICCForwardContext> oneStepForward(LightICCForwardContext sContext,
			Unit currentInstruction) {
		this.sContext = sContext;
		List<LightICCForwardContext> newBc = new ArrayList<LightICCForwardContext>();

		
		for (CallStackItem csi : sContext.getCallStack()) {
			Logger.print("    " + csi.getSmethd());
		}

		// for (Value value : sContext.getIntrestedVariable()) {
		// Logger.print("iv:" + value);
		// }
		boolean containsIntrestedThings = false;
		
		sContext.resetCurInterestedVariable();
		
		for (ValueBox box : currentInstruction.getUseAndDefBoxes()) {
			// To track the param reachability, only processed in AssignStmt
			if (this.sContext.isIntrested(box.getValue())) {
				containsIntrestedThings = true;
				sContext.addCurInterestedVariable(box.getValue());
//				System.out.println("In Value " + box.getValue());
//				sContext.setInstructionLocation(currentInstruction, containsIntrestedThings, box.getValue());
//				break;
			}
		}

		sContext.setInstructionLocation(currentInstruction);
	
		
		if (!containsIntrestedThings && !(currentInstruction instanceof ReturnStmt)
				&& !(currentInstruction instanceof ReturnVoidStmt)
				&& !(currentInstruction instanceof IdentityStmt))
			return newBc;
		
		sContext.add2InstructionTrace(sContext.getMethodLocation(), sContext.getBlockLocation(), currentInstruction,
				containsIntrestedThings);

		
//		System.out.println("Cur Inst: " + currentInstruction);
		
		
		currentInstruction.apply(this);

		return newBc;
	}

	// InstanceInvokeExpr
	public void handleInvokeStmt(Value assiTo, InvokeExpr invokExpr) {
		
//		pauseWhile();
		
		boolean interestinRet = false;
		
		boolean isInterestedInArgs = this.sContext.containsIntrested(invokExpr.getArgs());

		
		if (!isInterestedInArgs) return;
		
		if (invokExpr.getMethod().getSignature().equals("<android.content.SharedPreferences$Editor: android.content.SharedPreferences$Editor putString(java.lang.String,java.lang.String)>")
					|| invokExpr.getMethod().getSignature().equals("<android.content.SharedPreferences$Editor: android.content.SharedPreferences$Editor putStringSet(java.lang.String,java.util.Set)>")
					|| (invokExpr.getMethod().getSignature().contains("<android.content.Intent: ") && invokExpr.getMethod().getSignature().contains(" put"))) {
			if (assiTo != null) {
					// found target and create question

					Logger.print("Found Target put for Key: " + tq.getTargetKey());

					ArrayList<Integer> regIndex = new ArrayList<Integer>();
					regIndex.add(1);

					HeapObject ho = HeapObject.getInstance(runTest.dg, tq.getTargetKey());
					ValuePoint vp = new ValuePoint(runTest.dg, this.sContext.getMethodLocation(), this.sContext.getBlockLocation(), this.sContext.instructionLocation, regIndex);
					vp.setReferenceTrace(sContext.getCallStack());
					ho.getVPs().add(vp);
					runTest.dg.addNode(ho);

					sContext.setTerminated(true);
					tq.setHasSolved();
					return;
				}
			} else if (invokExpr.getMethod().getSignature().equals("<android.content.SharedPreferences: java.lang.String getString(java.lang.String,java.lang.String)>") || (invokExpr.getMethod().getSignature().contains("<android.content.Intent") && invokExpr.getMethod().getSignature().contains(" get"))){
				sContext.setTerminated(true);
				Logger.print("Go to get cases, returning");
									
				tq.setHasSolved();
				return;
			} 
			
				
		
		this.jump2callee(assiTo, invokExpr);
	}
	
	
	@Override
	public void caseInvokeStmt(InvokeStmt stmt) {
		handleInvokeStmt(null, stmt.getInvokeExpr());
	}

	@Override
	public void caseAssignStmt(AssignStmt stmt) {
		// TODO Auto-generated method stub
		
		Value lop = getValue(stmt.getLeftOp());
		Value rop = getValue(stmt.getRightOp());
		
		
		if (rop instanceof InvokeExpr) {
			handleInvokeStmt(lop, stmt.getInvokeExpr());
		} else if (this.sContext.isIntrested(rop)){
			sContext.addIntrestedVariable(lop);
			
		} else {
			defaultCase(stmt);
		}
		
	}


	@Override
	public void caseReturnStmt(ReturnStmt stmt) {
		// TODO Auto-generated method stub
		boolean interestinRet = false;
//		System.out.println("At return cur taint: " + this.sContext.getIntrestedVariable().keySet());
		if (stmt != null && this.sContext.isIntrested(stmt.getOp())) {
			interestinRet = true;
			
		}
		
		// if (this.sContext.invokeLayer == 0) sContext.setTerminated(true);
		
		for (ValueBox vb : this.sContext.getBlockLocation().getBody().getDefBoxes()) {
			this.sContext.intrestedVariable.remove(vb.getValue());
		}
		
		back2caller(interestinRet);
	}

	@Override
	public void caseReturnVoidStmt(ReturnVoidStmt stmt) {
		// TODO Auto-generated method stub
		caseReturnStmt(null);
	}

	@Override
	public void caseIdentityStmt(IdentityStmt stmt) {
		// TODO Auto-generated method stub

		Value rop = stmt.getRightOp();
		Value lop = stmt.getLeftOp();

		if (rop instanceof ParameterRef && this.sContext.isIntrested(rop)) {
				this.sContext.addIntrestedVariable(lop);
		} else
			defaultCase(stmt);
	}

	@Override
	public void defaultCase(Object obj) {
		// TODO Auto-generated method stub
//		System.out.println("unsupported stmt:" + obj);
	}

	// //////////////////////////////////////////////////
	// handle call
	
	private void jump2callee(Value assiTo, InvokeExpr invokExpr) {
//		System.out.println("++++++invoke method: " + invokExpr.toString() + ", current Layer: " + this.sContext.invokeLayer);	
		if (invokExpr.getMethod().isConcrete() && invokExpr.getMethod().getDeclaringClass().isApplicationClass()){
			CallStackItem citem = new CallStackItem(this.sContext.getMethodLocation(), this.sContext.getBlockLocation(), this.sContext.getInstructionLocation(), assiTo, new HashSet<Value>(), invokExpr);	// caller site
			
			
			ParameterRef pref;
	
			for (int i = 0; i < invokExpr.getArgs().size(); i++) {
				if (this.sContext.isIntrested(invokExpr.getArgs().get(i))) {
					pref = MethodUtility.getParameterRef(invokExpr.getMethod(), i);
					this.sContext.addIntrestedVariable(pref);
				}
			}
			
//			System.out.println("*****jump2callee: " + citem.getSmethd().toString());
			this.sContext.getCallStack().push(citem);
			
			this.sContext.setMethodLocation(invokExpr.getMethod());
			Body body = this.sContext.getMethodLocation().retrieveActiveBody();
			CompleteBlockGraph cbg = BlockGenerator.getInstance().generate(body);
			// for (Block b : cbg.getHeads()) {
			//
			// }
	
			if (cbg.getHeads().size() > 1) {
				Logger.printW("header size > 1");
			}
	
			this.sContext.setBlockLocation(cbg.getHeads().get(0));
			this.sContext.setInstructionLocation(cbg.getHeads().get(0).getHead());	//TOCHECK
			this.sContext.invokeLayer++;
			
		} 

	}

	private void back2caller(boolean interestinRet) {
//		if (sContext.getMethodLocation().toString().contains("android.net.Uri[] getSelectedFiles(android.content.Intent,int"))
//			System.out.println("Now in func: " + sContext.getMethodLocation().toString() + ". Is interested in return value? " + interestinRet);
		this.sContext.invokeLayer--;
		
		if (this.sContext.getCallStack().isEmpty()) {
//				System.out.println("******back2caller: empty callstack, set termination");

			this.sContext.setTerminated(true);
			return;

		} else {
			CallStackItem citem = this.sContext.getCallStack().pop();
			// Add the tainted actual params
			InvokeExpr invokExpr = citem.getInvokeExpr();
			
			// Propagate taint back to caller site
			// -2 : return target, -1 : base Obj, >=0 : params
			// Firstly remove the original tainted vars, and then add back the new ones with Fields 
			if (invokExpr != null) {
				this.sContext.setMethodLocation(citem.getSmethd());
				this.sContext.setBlockLocation(citem.getBlcok());
				this.sContext.setInstructionLocation(citem.getCurrentInstruction());
				this.sContext.setIntrestedVariable(citem.getInterestedValues());
				if (interestinRet && citem.getReturnTarget() != null) {
					this.sContext.addIntrestedVariable(citem.getReturnTarget());
				}
			}
		}
		
	}
	
	public Value getBaseValue(Value r) {
		if (r instanceof ArrayRef) return ((ArrayRef) r).getBase();
		if (r instanceof InstanceFieldRef) {
			return ((InstanceFieldRef) r).getBase();
			
		}
		if (r instanceof CastExpr) return getBaseValue(((CastExpr) r).getOp());
		
		if (r instanceof InstanceInvokeExpr) return ((InstanceInvokeExpr)r).getBase();
		return r;
	}

	
	public Value getValue(Value r) {
		if (r instanceof ArrayRef) return ((ArrayRef) r).getBase();
		if (r instanceof CastExpr) return ((CastExpr) r).getOp();
		return r;
	}
	
	
}