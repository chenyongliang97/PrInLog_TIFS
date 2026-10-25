package prinlog.stringvsa.backwardslicing;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;
import java.util.concurrent.locks.Condition;

import javax.sound.midi.SysexMessage;

import org.javatuples.Pair;
import org.json.JSONObject;

import prinlog.main.runTest;
import prinlog.stringvsa.base.GlobalStatistics;
import prinlog.stringvsa.base.ParameterTransferStmt;
import prinlog.stringvsa.base.StmtPoint;
import prinlog.stringvsa.base.TargetType;
import prinlog.stringvsa.forwardexec.StmtPath;
import prinlog.stringvsa.graph.CallGraph;
import prinlog.stringvsa.graph.ConditionBlock;
import prinlog.stringvsa.graph.DGraph;
import prinlog.stringvsa.graph.HeapObject;
import prinlog.stringvsa.graph.ValuePoint;
import prinlog.stringvsa.main.Config;
import prinlog.stringvsa.utility.BlockGenerator;
import prinlog.stringvsa.utility.BlockUtility;
import prinlog.stringvsa.utility.Logger;
import prinlog.stringvsa.utility.MethodUtility;
import prinlog.stringvsa.utility.OtherUtility;
import soot.CharType;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.JastAddJ.IntType;
import soot.jimple.AbstractStmtSwitch;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.GotoStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InterfaceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.LengthExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NullConstant;
import soot.jimple.NumericConstant;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JimpleLocal;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.util.HashChain;

public class BacktracingContext extends AbstractStmtSwitch implements StmtPath, IBCollecter {

	static HashMap<SootClass, String> classTag = new HashMap<>();
	static ArrayList<String> UIComp = new ArrayList<>();
	static {
		UIComp.add("android.app.Activity");
		UIComp.add("android.app.Service");
		UIComp.add("android.app.Fragment");
		// UIComp.add("Menu");
		// UIComp.add("android.content.BroadcastReceiver");
	}

	ValuePoint startPoint;
	DGraph dg;

	HashMap<String, HashSet<String>> block2AffectedCons;
	
	ArrayList<ConditionBlock> conditionChain;
	HashSet<ConditionBlock> leftInterestedBlocks;
	HashSet<ConditionBlock> currentInterestedBlocks;
	

	ArrayList<SootMethod> methodes;
	ArrayList<Pair<Block, Integer>> blockes;
	ArrayList<String> blockesTag;
	Unit currentInstruction;
	
	

	HashSet<Value> intrestedVariable;
	ArrayList<StmtPoint> execTrace;

	HashSet<HeapObject> dependentHeapObjects;
	Stack<CallStackItem> callStack;

	HashSet<DataSourceType> dataSrcs;
	HashSet<String> hcStrings;

	ArrayList<SootMethod> extendedMthd;

	public boolean checkPoint = false;
	boolean dependentsSolved = true;
	
	boolean isThisInterested = false;

	boolean finished = false;
	boolean defective = false;

	boolean containsIntrestedThingsInCB = false;
	boolean containsIntrestedThingsInData = false;

	HashSet<String> criticalDataBlocks;

	HashMap<Value, StmtPoint> foundKeys;


	@SuppressWarnings("unchecked")
	public BacktracingContext(BacktracingContext oldBc) {
		startPoint = oldBc.getStartPoint();
		dg = oldBc.getDg();
		methodes = (ArrayList<SootMethod>) oldBc.getMethodes().clone();
		blockes = (ArrayList<Pair<Block, Integer>>) oldBc.getBlockes().clone();
		currentInstruction = oldBc.getCurrentInstruction();
		intrestedVariable = (HashSet<Value>) oldBc.getIntrestedVariable().clone();
		execTrace = (ArrayList<StmtPoint>) oldBc.getExecTrace().clone();
		dependentHeapObjects = (HashSet<HeapObject>) oldBc.getDependentHeapObjects().clone();
		callStack = (Stack<CallStackItem>) oldBc.getCallStack().clone();
		dataSrcs = (HashSet<DataSourceType>) oldBc.getDataSrcs().clone();
		hcStrings = (HashSet<String>) oldBc.getHcStrings().clone();
		
		conditionChain = new ArrayList<ConditionBlock>();
		oldBc.getConditionChain().forEach(cb -> conditionChain.add(cb.clone()));
		
		currentInterestedBlocks = new HashSet<ConditionBlock>();
		oldBc.getcurrentInterestedBlocks().forEach(cb -> currentInterestedBlocks.add(cb.clone()));

		leftInterestedBlocks = new HashSet<ConditionBlock>();
		oldBc.getLeftInterestedBlocks().forEach(cb -> leftInterestedBlocks.add(cb.clone()));
		block2AffectedCons = new HashMap<String, HashSet<String>>();
		oldBc.getBlock2AffectedCons().forEach((b, bs) -> {block2AffectedCons.put(b, (HashSet<String>)bs.clone());});
		blockesTag = (ArrayList<String>)oldBc.getBlockTags().clone();
		extendedMthd = (ArrayList<SootMethod>) oldBc.getExtendedMthd().clone();
		dependentsSolved = oldBc.hasSolvedDependents();
		criticalDataBlocks = (HashSet<String>) oldBc.getDataCriticalBlocks().clone();
		foundKeys = (HashMap<Value, StmtPoint>) oldBc.getFoundKeys().clone();

	}

	public BacktracingContext(ValuePoint sp, DGraph dg) {
		this.startPoint = sp;
		this.dg = dg;
		// this.currentConditionPoint = cp;

		intrestedVariable = new HashSet<Value>();
		execTrace = new ArrayList<StmtPoint>();
		dependentHeapObjects = new HashSet<HeapObject>();
		callStack = new Stack<CallStackItem>();

		methodes = new ArrayList<SootMethod>();
		methodes.add(0, startPoint.getMethod_location());

		blockes = new ArrayList<Pair<Block, Integer>>();
		blockesTag = new ArrayList<>();
		setCurrentBlock(startPoint.getBlock_location());

		dataSrcs = new HashSet<DataSourceType>();
		hcStrings = new HashSet<String>();

		currentInstruction = startPoint.getInstruction_location();

		execTrace.add(0, new StmtPoint(startPoint.getMethod_location(), startPoint.getBlock_location(),
				startPoint.getInstruction_location()));


		conditionChain = new ArrayList<ConditionBlock>();

		leftInterestedBlocks = new HashSet<ConditionBlock>();
		currentInterestedBlocks = new HashSet<ConditionBlock>();

		block2AffectedCons = new HashMap<String, HashSet<String>>();
		extendedMthd = new ArrayList<SootMethod>();
		extendedMthd.add(getCurrentMethod());

		dependentsSolved = true;

		criticalDataBlocks = new HashSet<>();
		foundKeys = new HashMap<Value, StmtPoint>();
		
		// init
		Value tmp;
		for (int index : startPoint.getTargetRgsIndexes()) {
			if (index == TargetType.RIGHTPART.getType()) {// set heap object
				tmp = ((JAssignStmt) currentInstruction).getRightOp();
			} else if (index == TargetType.BASEOBJECT.getType()) {
				tmp = ((soot.jimple.InstanceInvokeExpr) ((Stmt) currentInstruction).getInvokeExpr()).getBase();
			} else {
				tmp = ((Stmt) currentInstruction).getInvokeExpr().getArg(index);
			}

			if (tmp instanceof JimpleLocal) {
				// Logger.printI("Target Variable is" + tmp.getClass() + " " + currentInstruction);
				this.addIntrestedVariableIfNotConstant(tmp);
			} else if (OtherUtility.isStrConstant(tmp)) {
				this.addNewDataSrc(DataSourceType.HARDCODED_STR);
				this.addNewHcString(tmp.toString());
			} else if (OtherUtility.isNumConstant(tmp)) {
				// this.addNewDataSrc(DataSourceType.HARDCODED_NUM);
			} else if (tmp instanceof NullConstant) {
				// Logger.printI("Target Variable is null " + currentInstruction);
			} else {
				// Logger.printW("Target Variable is" + tmp.getClass() + " " + currentInstruction);
			}
		}
	}

	public boolean hasSolvedDependents() {
		return this.dependentsSolved;
	}

	public boolean isDefaultCheckClass(Value v) {
		String sclasName = v.getType().toString();
		if (sclasName.contains("String") || sclasName.contains("Bundle") || sclasName.contains("Map")
		|| sclasName.contains("CharSequence") || sclasName.contains("Intent"))
		return true;
		return false;
	}


	public void finished() {
		finished = true;
	}

	public boolean backWardHasFinished() {
		// return intrestedVariable.size() == 0;
		// return finished || intrestedVariable.size() == 0 || this.getMethodes().size() > Config.MAXMETHODCHAINLEN;

		boolean dependentsSolved = hasSolvedDependents();
		

        return finished && dependentsSolved;
	}

	public boolean isDefective() {
		return defective;
	}

	public HashMap<Value, StmtPoint> getFoundKeys() {
		return this.foundKeys;
	}

	
	public List<BacktracingContext> oneStepBackWard() {

		Unit nextInstrct = this.getCurrentBlock().getPredOf(currentInstruction);

		if (extendedMthd.size() > 20) {
			finished = true;
			return new ArrayList<BacktracingContext>();
		}
		// Logger.print(getCurrentBlock().toString());

		leftInterestedBlocks.clear();

		if (nextInstrct != null) {
			return oneStepBackWard(nextInstrct);

		} else {
			List<BacktracingContext> newBc = new ArrayList<BacktracingContext>();
			BacktracingContext tmp;

			CompleteBlockGraph cbg = BlockGenerator.getInstance()
					.generate(this.getCurrentMethod().retrieveActiveBody());
            
            
            
			if (cbg.getHeads().contains(cbg.getBlocks().get(this.getCurrentBlock().getIndexInMethod()))) {  // First block of the method
				// go back to other method
                // System.out.println("Method head");
				GlobalStatistics.getInstance().countBackWard2Caller();
				if (this.getCallStack().isEmpty()) {

					// Logger.print("++++ Current Mthd: " + this.getCurrentMethod());
					String className = this.getCurrentMethod().getDeclaringClass().toString();
					
					boolean allisParameterRef = this.getIntrestedVariable().size() > 0;
					
					String ostr = "";
					for (Value var : this.getIntrestedVariable()) {
						ostr += var + ",";
						if (!(var instanceof ParameterRef)) {
							allisParameterRef = false;
						}

					}
                    // System.out.println("Callstack empty, method head, ostr: " + ostr);

					if (!allisParameterRef) {
						Logger.printW(String.format("[%s] [Not all the intresteds are ParameterRef]: %s",
								this.hashCode(), ostr));
						finished = true;
						return newBc;
					}

					return oneStepBackWard2Caller();    // Find the generation of the param if all the intersted vars are param

				} else {    // back call

					getBackFromACall();
					return newBc;
				}
			} else {
				// go back to previous block
                // System.out.println("Try to move to previous block: " + this.getCurrentBlock().getIndexInMethod());

                List<Block> bs = BlockGenerator.removeBlocksThatHaveBeenVisitedTwice(this.getBlockes(),
						cbg.getPredsOf(this.getCurrentBlock()));

				if (bs.size() == 0) {
					// System.out.print(
					// 		String.format("[%s] [No PredsOf]: %s", this.hashCode(), this.getCurrentInstruction()));
					finished = true; // joe: test
					defective = true;	// Ring BC, no need to save;
					return newBc;
				}
                // System.out.println("Move to previous block: " + this.getCurrentBlock().getIndexInMethod() + " " + this.getCurrentBlock().hashCode());

				if (runTest.reachMaxBCs) {
					List<Block> tmpblk = new ArrayList<Block>();
					tmpblk.add(bs.get(0));
					bs = tmpblk;
				}


				for (Block tb : bs) {
					if (tb == bs.get(0))
						continue;

					tmp = this.clone();
					tmp.setCurrentBlock(tb);
					newBc.addAll(tmp.oneStepBackWard(tb.getTail()));
					newBc.add(tmp);
				}

				this.setCurrentBlock(bs.get(0));

				// Logger.print("SPREADING AND COMPLETED NEW BLOCKS ONESTEP");

				newBc.addAll(this.oneStepBackWard(this.getCurrentBlock().getTail()));
				return newBc;
			}
		}
	}

	public List<BacktracingContext> oneStepBackWard(Unit nextInstrct) {
		List<BacktracingContext> newBc = new ArrayList<BacktracingContext>();
		currentInstruction = nextInstrct;

		
		containsIntrestedThingsInCB = false;
		containsIntrestedThingsInData = false;

		getcurrentInterestedBlocks().clear();

		for (ValueBox box : currentInstruction.getUseAndDefBoxes()) {
			HashSet<ConditionBlock> temps = this.containsInterestedVariableInCB(box.getValue());
			getcurrentInterestedBlocks().addAll(temps);
			if (temps.size() > 0) containsIntrestedThingsInCB = true; 
			else if (box.getValue() instanceof ArrayRef) {
				Value tmpv = ((ArrayRef) box.getValue()).getBase();
				temps = this.containsInterestedVariableInCB(tmpv);
				getcurrentInterestedBlocks().addAll(temps);
				if (temps.size() > 0) containsIntrestedThingsInCB = true;
			}


			if (intrestedVariable.contains(box.getValue())) {
				containsIntrestedThingsInData = true;
			} else if (box.getValue() instanceof ArrayRef
					&& intrestedVariable.contains(((ArrayRef) box.getValue()).getBase())) {
				containsIntrestedThingsInData = true;
			}
		}

		// if (currentInstruction.toString().contains("java.lang.reflect.Method"))
		// 	containsIntrestedThings = false;
		// String ostr = this.getIntrestedVariableString();
		// Logger.printI(String.format("[%s] [Next Ins]: %s (%s)", this.hashCode(), currentInstruction,
		// 		containsIntrestedThings ? "Y" : "N"));

		// Logger.print(" " + currentInstruction + " " + containsIntrestedThings);

		if (currentInstruction instanceof IfStmt) containsIntrestedThingsInCB = true;

		if (!(containsIntrestedThingsInCB || containsIntrestedThingsInData)) {
			return newBc;
		}
		
		StmtPoint stmt = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(), currentInstruction);


		if (containsIntrestedThingsInData) {
			this.getExecTrace().add(0, stmt);
			this.getDataCriticalBlocks().add(getCurrentMethod().toString() + "+" + String.valueOf(getCurrentBlock().getIndexInMethod()));
		}

		this.clear();

		((Stmt) currentInstruction).apply(this);
		newBc.addAll(this.retrieve());  // get new context generated from method call
		this.clear();

		// String nstr = this.getIntrestedVriableString();

		// Logger.printI(String.format("                 %s -> %s ", ostr, nstr));

		return newBc;
	}

	public String getTagsFromSuperclasses(SootClass sc) {
		if (sc.toString().equals("java.lang.Object")) {
			return "Normal";
		}

		for (String tag : UIComp) 
			if (sc.toString().contains(tag))
				return tag;
		
		if (sc.getSuperclass() != sc && sc.getSuperclass() != null) {
			return getTagsFromSuperclasses(sc.getSuperclass());
		}

		return "UNFOUND";
	}

	public void addMethodCallCB(StmtPoint sp) {
		ConditionBlock cb = new ConditionBlock(sp, NullConstant.v().v(), true);
		cb.addDeterminent(NullConstant.v().v(), NullConstant.v().v(), "mthd invoke", true);
		cb.setNotIF();
		cb.solvedDeterminent = true;
		getConditionChain().add(cb);
	}

	
	public List<BacktracingContext> oneStepBackWard2Caller() {
		List<BacktracingContext> newBc = new ArrayList<BacktracingContext>();
		List<StmtPoint> sps = StmtPoint.findCaller(this.getCurrentMethod().toString());
		StmtPoint currentMthdSP = new StmtPoint(getCurrentMethod(), getCurrentBlock(), currentInstruction);


		this.addMethodCallCB(currentMthdSP);
	
		if (!classTag.containsKey(getCurrentMethod().getDeclaringClass())) {
			String tag = getTagsFromSuperclasses(getCurrentMethod().getDeclaringClass());
			classTag.put(getCurrentMethod().getDeclaringClass(), tag);
		}

		if (UIComp.contains(classTag.get(getCurrentMethod().getDeclaringClass())) && getCurrentMethod().getSubSignature().contains(" on")) {
			finished = true;	// Finished here with found UI
			// Logger.print(" Found targeted callback: " + getCurrentMethod().toString());
			return newBc;
		}

		if (sps.size() <= 0) {

			if (!runTest.mthd2Tag.containsKey(getCurrentMethod().toString())) runTest.mthd2Tag.put(getCurrentMethod().toString(), MethodUtility.getMthdTag(getCurrentMethod()));
			
			//No caller, check whether can stop here
			if (this.getCurrentMethod().isConstructor()) sps = findNewLocator();
			
			int idx = sps.size() - 1;
			while (idx >= 0) {	// New 
				StmtPoint sp = sps.get(idx);
				if (extendedMthd.contains(sp.getMethod_location())) sps.remove(idx);
				idx--;
			}

			if (sps.size() <= 0) {
				Logger.print(" +++++ No New Locator for: " + getCurrentMethod().getDeclaringClass().toString());
				finished = true;	// Finished here
				return newBc;
			}
			// else {

			// 	if (runTest.reachMaxBCs) {
			// 		List<StmtPoint> tmpsps = new ArrayList<StmtPoint>();
			// 		tmpsps.add(sps.get(0));
			// 		sps = tmpsps;
			// 	}


			// 	int len = sps.size();
			// 	for (int i = 1; i < len; i++) {
			// 		newBc.add(0, this.clone());
			// 	}
			// 	newBc.add(0, this);

			// 	BacktracingContext tmpBC;
			// 	StmtPoint tmpSP;
			// 	for (int i = 0; i < len; i++) {
			// 		tmpBC = newBc.get(i);
			// 		tmpSP = sps.get(i);

			// 		tmpBC.setCurrentMethod(tmpSP.getMethod_location());
			// 		tmpBC.setCurrentBlock(tmpSP.getBlock_location());
			// 		tmpBC.setCurrentInstruction(tmpSP.getInstruction_location());
			// 		tmpBC.getExtendedMthd().add(tmpSP.getMethod_location());

			// 		tmpBC.getIntrestedVariable().clear();
			// 		tmpBC.getConditionChain().forEach(cb -> {cb.getInterestedVariables().clear();});
			// 		// Logger.print(" Added new : " + getCurrentMethod().toString());
					
			// 	}
			// 	newBc.remove(0);

			// 	return newBc;
			// }
		}


		int idx = sps.size() - 1;
		// while (idx >= 0) {
		// 	String mthd = sps.get(idx).getMethod_location().toString();
		// 	if (!(mthd.contains("co.talenta.modul.splash.SplashActivity: void s()") || mthd.contains("co.talenta.modul.splash.SplashActivity: void onCreate(android.os.Bundle)>") || mthd.contains("co.talenta.data.manager.FirebaseAnalyticManager: void logEvent(co.talenta.domain.entity.analytic.AnalyticEvent,java.util.Map)")))
		// 		sps.remove(idx);
		// 	idx--;
		// }

		// idx = sps.size() - 1;

		while (idx >= 0) {	// New 
			StmtPoint sp = sps.get(idx);
			if (getExtendedMthd().contains(sp.getMethod_location())) sps.remove(idx);
			idx--;
		}

		if (sps.size() == 0) {
			finished = true;
			Logger.print("Have already visited all callers.");
			return newBc;
		}

		
		if (runTest.reachMaxBCs) {
			List<StmtPoint> tmpsps = new ArrayList<StmtPoint>();
			tmpsps.add(sps.get(0));
			sps = tmpsps;
		}

		int len = sps.size();
		
		if (len > 10) len = 10;
		for (int i = 1; i < len; i++) {
			newBc.add(0, this.clone());
		}
		newBc.add(0, this);

		BacktracingContext tmpBC;
		StmtPoint tmpSP;
		for (int i = 0; i < len; i++) {
			tmpBC = newBc.get(i);
			tmpSP = sps.get(i);
			// tmpBC.addMethodCallCB(currentMthdSP);
			tmpBC.oneStepBackWard2Caller(tmpSP);
			// Logger.print("NEW ADDED: " + sps.get(i).getMethod_location().toString());			
			// tmpBC.getConditionChain().forEach(cb -> {cb.getInterestedVariables().clear();});
		}
		newBc.remove(0);

		return newBc;
	}

	public void oneStepBackWard2Caller(StmtPoint tmpSP) {

		this.setCurrentMethod(tmpSP.getMethod_location());
		this.setCurrentBlock(tmpSP.getBlock_location());
		this.setCurrentInstruction(tmpSP.getInstruction_location());

		this.getExtendedMthd().add(tmpSP.getMethod_location());

		// String ostr = this.getIntrestedVariableString();
		// Logger.printI(String.format("[%s] [Next Ins]: %s (caller:%s)", this.hashCode(), this.getCurrentInstruction(), this.getCurrentMethod()));

		InvokeExpr inve = ((Stmt) tmpSP.getInstruction_location()).getInvokeExpr();
		ParameterTransferStmt tmp;
		

		// For condition blocks
		HashSet<Value> InterestedVars = new HashSet<>();
		
		this.getConditionChain().forEach(cb -> {InterestedVars.addAll(cb.getInterestedVariables());});
		
		HashMap<Integer, Value> regs = new HashMap<Integer, Value>();
		HashMap<Integer, HashSet<ConditionBlock>> regs2CB = new HashMap<>();
		HashMap<Integer, Value> regsCBVar = new HashMap<Integer, Value>();
		
		for (Value var : InterestedVars) {
			if (var instanceof ParameterRef) {
				regs2CB.put(((ParameterRef) var).getIndex(), new HashSet<>());
				regsCBVar.put(((ParameterRef) var).getIndex(), var);
				this.getConditionChain().forEach(cb -> {
					if (cb.getInterestedVariables().contains(var))
						regs2CB.get(((ParameterRef) var).getIndex()).add(cb);
				});
			}
		}

		this.getConditionChain().forEach(cb -> {cb.getInterestedVariables().clear();});
		
		
		for (int j : regs2CB.keySet()) {
			
			if (inve.getArgCount() <= j) continue;

			tmp = new ParameterTransferStmt(regsCBVar.get(j), inve.getArg(j));
			StmtPoint tmpSPaaa = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(), tmp);
			if (inve.getArg(j) instanceof Local || inve.getArg(j) instanceof Constant)
				this.addVarToInterestedBlocks(regs2CB.get(j), inve.getArg(j), tmpSPaaa);

		}


		// For target values

		regs = new HashMap<Integer, Value>();
		for (Value var : this.getIntrestedVariable()) {
			if (var instanceof ParameterRef)
				regs.put(((ParameterRef) var).getIndex(), var);
		}

		this.getIntrestedVariable().clear();
		
		for (int j : regs.keySet()) {
			
			if (inve.getArgCount() <= j) continue;

			this.addIntrestedVariableIfNotConstant(inve.getArg(j));
			tmp = new ParameterTransferStmt(regs.get(j), inve.getArg(j));
			StmtPoint tmpSPaaa = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(), tmp);
			this.getExecTrace().add(0, tmpSPaaa);

			if (foundKeys.keySet().contains(regs.get(j))) updateICCKeys(regs.get(j), inve.getArg(j));

		}



		// String nstr = this.getIntrestedVariableString();
		// Logger.printI(String.format("                 %s -> %s ", ostr, nstr));
	}

	public void getBackFromACall() {
		CallStackItem citem = this.getCallStack().pop();

		Stmt retStmt = (Stmt) citem.getCurrentInstruction();

		// this.currentInterestedBlocks = citem.getInterestedCBs();
		
		
		for (Value param : this.getCurrentMethod().getActiveBody().getParameterRefs()) {

			
			HashSet<ConditionBlock> interestedCB = this.containsInterestedVariableInCB(param);
			
			// if (interestedCB.size() > 0) {
			// 	Value opsite;	
			// 	opsite = retStmt.getInvokeExpr().getArg(((ParameterRef) param).getIndex());
			// 	interestedCB.forEach(cb -> {cb.removeInterestedVariable(param);});	
			// 	StmtPoint tmpSPaaa = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(),
			// 	new ParameterTransferStmt(param, opsite));
			// 	this.addIntrestedVariableIfNotConstant(opsite);
			// 	if (opsite instanceof Local || opsite instanceof Constant)
			// 		this.addVarToInterestedBlocks(interestedCB, opsite, tmpSPaaa);
				
				
			// 	interestedCB.forEach(cb -> {
			// 		if (cb.isDeterminent(param) && !cb.hasSolvedDeterminent()) {
			// 				cb.updateDeterminent(opsite);
			// 		}
			// 	});				
			// }
			
			
			if (this.getIntrestedVariable().contains(param)) {
				Value opsite;	
				opsite = retStmt.getInvokeExpr().getArg(((ParameterRef) param).getIndex());
				this.removeIntrestedVariable(param);
				this.addIntrestedVariableIfNotConstant(opsite);
				StmtPoint tmpSPaaa = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(),
						new ParameterTransferStmt(param, opsite));
				this.getExecTrace().add(0, tmpSPaaa);
				if (foundKeys.keySet().contains(param)) updateICCKeys(param, opsite);
			}
			
			
		}

		// InvokeExpr ive = retStmt.getInvokeExpr();
		// if (ive instanceof InstanceInvokeExpr) {
		// 	Value bv = ((InstanceInvokeExpr) ive).getBase();
		// 	this.getConditionChain().forEach(cb -> {
		// 		if (!cb.isThisInterested) cb.removeInterestedVariable(bv);
		// 	});
		// }

		// TODO: taint base for interseted field
		// if (retStmt.getInvokeExpr() instanceof InstanceInvokeExpr)

		// 	if (unsolvedField.containsKey(((InstanceInvokeExpr) retStmt.getInvokeExpr()).getBase()))


		this.setCurrentMethod(citem.getSmethd());

		this.setCurrentBlock(citem.getBlcok());
		this.setCurrentInstruction(citem.getCurrentInstruction());

	}

	public List<StmtPoint> findNewLocator() {
		
		SootClass sclas = this.getCurrentMethod().getDeclaringClass();

		List<StmtPoint> sps = new ArrayList<StmtPoint>();
		
		// boolean fromNew = true;
		// if (this.getCurrentMethod().isConstructor()) fromNew = false;

		HashSet<StmtPoint> sss = CallGraph.getNewClassPoints(sclas);
		

		if (sss != null) {
			for (StmtPoint sp : sss) sps.add(new StmtPoint(sp.getMethod_location(), sp.getBlock_location(), sp.getInstruction_location()));
		}

		return sps;
	}

	public ValuePoint getStartPoint() {
		return startPoint;
	}

	public void setStartPoint(ValuePoint startPoint) {
		this.startPoint = startPoint;
	}

	public DGraph getDg() {
		return dg;
	}

	public void setDg(DGraph dg) {
		this.dg = dg;
	}

	public SootMethod getCurrentMethod() {
		return getMethodes().get(0);
	}

	public void setCurrentMethod(SootMethod currentMethod) {
		this.getMethodes().add(0, currentMethod);
	}

	public Block getCurrentBlock() {
		return getBlockes().get(0).getValue0();
	}

	public Block getLastBlock() {
		if (getBlockes().size() > 1)
			return getBlockes().get(1).getValue0();
		else return null;
	}

	public void setCurrentBlock(Block currentBlock) {
		getBlockes().add(0, Pair.with(currentBlock, this.getCallStack().size()));
		getBlockTags().add(0, getCurrentMethod().toString() + "+" + currentBlock.getIndexInMethod());
	}

	public ArrayList<SootMethod> getMethodes() {
		return methodes;
	}

	public ArrayList<Pair<Block, Integer>> getBlockes() {
		return blockes;
	}

	public Unit getCurrentInstruction() {
		return currentInstruction;
	}

	public void setCurrentInstruction(Unit currentInstruction) {
		this.currentInstruction = currentInstruction;
	}

	public String getIntrestedVariableString() {
		String ostr = "";
		for (Value var : this.getIntrestedVariable()) {
			ostr += var + ",";
		}
		return ostr;
	}

	

	public HashSet<Value> getIntrestedVariable() {
		return intrestedVariable;
	}

	public HashSet<ConditionBlock> getLeftInterestedBlocks() {
		return this.leftInterestedBlocks;
	}

	public HashSet<ConditionBlock> getcurrentInterestedBlocks() {
		return this.currentInterestedBlocks;
	}

	public void addIntrestedVariableIfNotConstant(Value v) {

		if (v instanceof Local) {
			intrestedVariable.add(v);
		} else if (OtherUtility.isStrConstant(v)) {
			// this.addNewDataSrc(DataSourceType.HARDCODED_STR);
			// this.addNewHcString(v.toString());
		} else if (OtherUtility.isNumConstant(v)) {
			// this.addNewDataSrc(DataSourceType.HARDCODED_NUM);
		} else if (v instanceof NullConstant) {
			// Logger.printI("Variable is null no need to taint ");
		} else {
			// Logger.printW(String.format("[%s] [unknow addIntrestedVariableIfNotConstant] %s(%s)", this.hashCode(), v,
			// 		v.getClass()));
		}
	}

	public void addIntrestedVariable(Value v) {
		intrestedVariable.add(v);
	}

	public void removeIntrestedVariable(Value v) {
		intrestedVariable.remove(v);
	}

	public void setIntrestedVariable(HashSet<Value> intrestedVariable) {
		this.intrestedVariable = intrestedVariable;
	}

	public void addInterestedVariableInCB(ConditionBlock cb, Value v) {
		cb.addInterestedVariable(v);
	}

	public void removeInterestedVariableInCB(ConditionBlock cb, Value v) {
		cb.addInterestedVariable(v);
	}

	public void removeInterestedVariableInAllCB(Value v) {
		for (ConditionBlock cb : this.getConditionChain())
			cb.removeInterestedVariable(v);
	}

	public ArrayList<StmtPoint> getExecTrace() {
		return execTrace;
	}

	public void addConditionBlockVariable(ConditionBlock cb, Value v, StmtPoint sp) {	// Check for each instruction then add.
		cb.addInterestedVariable(v);
		if (sp != null) cb.getCBExecTrace().add(0, sp);	
	}

	public ArrayList<StmtPoint> removeFromExecTrace(Unit u) {
		StmtPoint tmp = null;
		for (StmtPoint sp : getExecTrace()) {
			if (sp.getInstruction_location() == u) {
				tmp = sp;
			}
		}
		if (tmp != null)
			getExecTrace().remove(tmp);
		return execTrace;
	}

	public ArrayList<ConditionBlock> getConditionChain() {
		return this.conditionChain;
	}

	public HashSet<DataSourceType> getDataSrcs() {
		return dataSrcs;
	}

	public HashSet<String> getHcStrings() {
		return hcStrings;
	}

	public void addNewDataSrc(DataSourceType dst) {
		dataSrcs.add(dst);
	}

	public void addNewHcString(String dst) {
		hcStrings.add(dst);
	}

	public void setExecTrace(ArrayList<StmtPoint> execTrace) {
		this.execTrace = execTrace;
	}


	public void addVarToInterestedBlocks(HashSet<ConditionBlock> cbs, Value v, StmtPoint sp) {
		if (cbs.size() > 0) cbs.forEach(cb -> {addConditionBlockVariable(cb, v, sp);});
		// else Logger.printW(" Try to add to empty Interested Blocks!!!");
	}

	public HashSet<ConditionBlock> containsInterestedVariableInCB(Value v) {
		if (v instanceof ArrayRef) v = ((ArrayRef) v).getBase();
		SootClass sclas = v instanceof FieldRef ? ((FieldRef) v).getField().getDeclaringClass() : null;
		
		sclas = v instanceof InvokeExpr ? ((InvokeExpr) v).getMethod().getDeclaringClass() : sclas;

		HashSet<ConditionBlock> cbs = new HashSet<>();
		if (v.toString().contains("testString")) {
			Logger.print("Found testString: " + currentInstruction.toString());
		}
		for (ConditionBlock cb : this.getConditionChain()) {

			if (cb.isInterested(v)) cbs.add(cb);
			// else 
			// if (sclas != null && cb.getUnsolvedField().containsKey(sclas)) { 
			// 	if (v instanceof FieldRef && cb.getUnsolvedField().get(sclas).contains(((FieldRef) v).getField())) 
			// 		cbs.add(cb);
			// 	else if (v instanceof InvokeExpr) cbs.add(cb);	// Invoke Expr with field interested in the class
			// }
		}
	
		return cbs;
	}

	public void printExceTrace() {
		Logger.print("[Start]:" + this.getStartPoint().getInstruction_location());
		for (StmtPoint var : this.getExecTrace()) {
			Logger.print(" instr: " + var.getInstruction_location() + " block: " + var.getBlock_location().getIndexInMethod());
		}
	}

	public void setDependentHeapObjects(HashSet<HeapObject> dependentHeapObjects) {
		this.dependentHeapObjects = dependentHeapObjects;

	}

	public HashSet<HeapObject> getDependentHeapObjects() {
		return dependentHeapObjects;
	}

	public Stack<CallStackItem> getCallStack() {
		return callStack;
	}

	public BacktracingContext clone() {
		BacktracingContext tmp = new BacktracingContext(this);
		return tmp;
	}

	

	// //////////////////////////////////////////////////////
	// ////////////////////// StmtSwitch/////////////////////

	@Override
	public void caseGotoStmt(GotoStmt stmt) {
    	String gotoTarget = stmt.getTarget().toString();;
		Block lastBlock = this.getLastBlock();

		String lastStmt = lastBlock.getHead().toString();

		if (getCurrentBlock().getIndexInMethod() == 1) {
			checkPoint = true;
		}
		if (!gotoTarget.equals(lastStmt) && getCurrentBlock().getTail().equals(currentInstruction)) {
			
			// Logger.print("Found defective goto : " + currentInstruction + "\n" + getCurrentBlock());
			finished = true;
			// defective = true;
		}


  	}


	@Override
	public void caseAssignStmt(AssignStmt stmt) {
		// TODO Auto-generated method stub
		// boolean leftisIntrested = this.getIntrestedVariable().contains(stmt.getLeftOp());



		Value leftOp = stmt.getLeftOp();
		leftInterestedBlocks = this.containsInterestedVariableInCB(leftOp);
		boolean leftIsIntrestedCB = leftInterestedBlocks.size() > 0 ? true : false;
		boolean leftIsIntrestedData = this.getIntrestedVariable().contains(leftOp);


		this.removeInterestedVariableInAllCB(leftOp);
		this.removeIntrestedVariable(leftOp);

		StmtPoint tsp = new StmtPoint(getCurrentMethod(), getCurrentBlock(), getCurrentInstruction());

		Value value = stmt.getRightOp();

		

		if (leftIsIntrestedCB) {
			leftInterestedBlocks.forEach(cb -> {
				if (cb.isDeterminent(leftOp) && !cb.hasSolvedDeterminent()) {
					if (value instanceof NullConstant || OtherUtility.isStrConstant(value) || OtherUtility.isNumConstant(value)) {
						
						if (!cb.satisfyDeterminent((Constant) value)) {
							finished = true;
							defective = true;
							// Logger.print("Found defective for " + currentInstruction.toString());
							return;
						} 
						// else Logger.print("Solve and satisfy condition: " + cb.hasSolvedDeterminent());
					} else  {
						cb.updateDeterminent(value);
					}
				}
				
				// if (leftOp instanceof FieldRef) cb.solveField((FieldRef)leftOp);
				
				String currentBlockTAG = getCurrentMethod().toString() + "+" + getCurrentBlock().getIndexInMethod();
				if (!getBlock2AffectedCons().containsKey(currentBlockTAG)) getBlock2AffectedCons().put(currentBlockTAG, new HashSet<>());
				getBlock2AffectedCons().get(currentBlockTAG).add(cb.TAG);
				
			});

		}

		if (value instanceof InvokeExpr) {
			currentInterestedBlocks.forEach(cb -> {cb.getCBExecTrace().add(0, tsp);}); // can add more conditions
			InvokeExpr tmp = (InvokeExpr) value;
			handleInvokeExpr(stmt.getLeftOp(), leftIsIntrestedCB, leftIsIntrestedData, tmp);


			//  addVarToInterestedBlocks(leftInterestedBlocks, value, tsp);	// need to check
			
		} else if (value instanceof JNewExpr) {
			JNewExpr tjne = (JNewExpr) value;
			String clasName = tjne.getBaseType().toString();
			if (clasName.equals("java.lang.StringBuilder")) {

			} else if (clasName.equals("android.widget.EditText")) {

				this.addNewDataSrc(DataSourceType.UI);
			} else if (clasName.equals("java.io.File")) {

				this.addNewDataSrc(DataSourceType.LOCALFILE);
			} else if (clasName.equals("java.util.HashMap") || clasName.equals("java.util.ArrayList")
					|| clasName.equals("java.util.Map") || clasName.equals("java.util.Set")
					|| clasName.equals("java.util.List")) {
				this.addNewDataSrc(DataSourceType.LOCALFILE);

			} else {
				// Logger.printW(String.format("[%s] [Can't Handle caseAssignStmt->JNewExpr]: %s (%s)", this.hashCode(),
				// 		stmt, value.getClass()));

			}

			// addVarToInterestedBlocks(leftInterestedBlocks,value, tsp);
			leftInterestedBlocks.forEach(cb -> {cb.getCBExecTrace().add(0, tsp);});
			

		} else if (value instanceof NewArrayExpr) {
			// NewArrayExpr arraye = (NewArrayExpr) value;
			// if (arraye.getBaseType().toString().equals("java.lang.Object")) {

			// } else if (arraye.getBaseType().toString().equals("byte")) {

			// } else if (arraye.getBaseType().toString().equals("java.lang.String")) {

			// } else if (arraye.getBaseType().toString().equals("android.widget.EditText")) {

			// } else {
			// 	Logger.printW(String.format("[%s] [Can't Handle caseAssignStmt->NewArrayExpr]: %s (%s)(%s)",
			// 			this.hashCode(), stmt, value.getClass(), arraye.getBaseType()));
			// }
			leftInterestedBlocks.forEach(cb -> {cb.getCBExecTrace().add(0, tsp);});

		} else if (value instanceof FieldRef) {// dependent field, add to ho and solve later
			
			// leftInterestedBlocks.forEach(cb -> {cb.addUnsolvedField((FieldRef) value); cb.getCBExecTrace().add(0, tsp);});
			

			if (leftIsIntrestedData || leftIsIntrestedCB) {
				HeapObject ho = HeapObject.getInstance(dg, ((FieldRef) value).getField());

				if (!this.getDependentHeapObjects().contains(ho)) {
					this.getDependentHeapObjects().add(ho);
					dg.addNode(ho);
				}

				if (leftIsIntrestedData) this.getExecTrace().get(0).setField(((FieldRef) value).getField());
				tsp.setField( ((FieldRef) value).getField());
				leftInterestedBlocks.forEach(cb -> {cb.getCBExecTrace().add(0, tsp);});
			}

		} else if (value instanceof JimpleLocal) {

			if (foundKeys.keySet().contains(leftOp)) updateICCKeys(leftOp, value);
			
			addVarToInterestedBlocks(leftInterestedBlocks,value, tsp);

			if (leftIsIntrestedData) this.addIntrestedVariable(value);
		} else if (value instanceof JArrayRef) {
			
			addVarToInterestedBlocks(leftInterestedBlocks,((JArrayRef) value).getBase(), tsp);

			if (leftIsIntrestedData) this.addIntrestedVariable(((JArrayRef) value).getBase());

			// this.addNewDataSrc(DataSourceType.List);

		} else if (value instanceof CastExpr) {
			if (((CastExpr) value).getOp() instanceof Local) 
				addVarToInterestedBlocks(leftInterestedBlocks,((CastExpr) value).getOp(), tsp);
				
			if (leftIsIntrestedData) this.addIntrestedVariableIfNotConstant(((CastExpr) value).getOp());

			if (foundKeys.keySet().contains(leftOp)) updateICCKeys(leftOp, ((CastExpr) value).getOp());

		} else if (value instanceof BinopExpr) {
			// + - * /
			BinopExpr be = ((BinopExpr) value);
			if (leftIsIntrestedData) {
				this.addIntrestedVariableIfNotConstant(be.getOp1());
				this.addIntrestedVariableIfNotConstant(be.getOp2());
			}

			if (be.getOp1() instanceof Local)
				addVarToInterestedBlocks(leftInterestedBlocks,be.getOp1(), tsp);

			if (be.getOp2() instanceof Local)
				addVarToInterestedBlocks(leftInterestedBlocks,be.getOp2(), tsp);
				

		} else if (value instanceof LengthExpr) {
			// Logger.printW(String.format("LengthExpr " + value + " " + ((LengthExpr) value).getOp()));
			if (leftIsIntrestedData) this.addIntrestedVariable(((LengthExpr) value).getOp());
			addVarToInterestedBlocks(leftInterestedBlocks,((LengthExpr) value).getOp(), tsp);
			
		} 
		// else if (OtherUtility.isStrConstant(value)) {
		// 	// this.addNewDataSrc(DataSourceType.HARDCODED_STR);
		// 	// this.addNewHcString(value.toString());
		// } else if (OtherUtility.isNumConstant(value)) {
		// 	// this.addNewDataSrc(DataSourceType.HARDCODED_NUM);
		// } else if (value instanceof NullConstant) {

		// }
		else if ((value instanceof NullConstant || OtherUtility.isStrConstant(value) || OtherUtility.isNumConstant(value))) {

			if (foundKeys.keySet().contains(leftOp)) updateICCKeys(leftOp, value);
			leftInterestedBlocks.forEach(cb -> {cb.getCBExecTrace().add(0, tsp);});
		}
		else {

			addVarToInterestedBlocks(leftInterestedBlocks, value, tsp);
			Logger.printW(String.format("[%s] [Can't Handle caseAssignStmt->RightOp]: %s (%s)", this.hashCode(), stmt,
					value.getClass()));
		}

	}

	@Override
	public void caseInvokeStmt(InvokeStmt stmt) {
		// TODO Auto-generated method stub

		StmtPoint tsp = new StmtPoint(getCurrentMethod(), getCurrentBlock(), getCurrentInstruction());
		currentInterestedBlocks.forEach(cb -> {cb.getCBExecTrace().add(0, tsp);});
		

		// if (stmt.getInvokeExpr() instanceof InstanceInvokeExpr) 
		// 	addVarToInterestedBlocks(currentInterestedBlocks, ((InstanceInvokeExpr)stmt.getInvokeExpr()).getBase(), null);
		
		handleInvokeExpr(null, false, false, stmt.getInvokeExpr());
	
	}

	

	public void handleInvokeExpr(Value restAssignTo, boolean leftisIntrestedCB, boolean leftisIntrestedData, InvokeExpr invokExp) {


		String mthSig = invokExp.getMethod().toString();
		if (invokExp instanceof InterfaceInvokeExpr) {
			mthSig = invokExp.getMethodRef().toString();
		}

		if (leftisIntrestedCB) {
			if (invokExp instanceof InstanceInvokeExpr && isDefaultCheckClass(((InstanceInvokeExpr)invokExp).getBase())) 
				addVarToInterestedBlocks(leftInterestedBlocks, ((InstanceInvokeExpr) invokExp).getBase(), null);
			
			for (int i = 0; i < invokExp.getArgCount(); i++) {
				if (invokExp.getArg(i) instanceof Local) {
					// Logger.print("      Testsss: " + invokExp.getArg(i).getType().toString());
					addVarToInterestedBlocks(currentInterestedBlocks, invokExp.getArg(i), null);
				}
			}
		}


		if (containsIntrestedThingsInData){
			if (mthSig.equals("<java.lang.System: void arraycopy(java.lang.Object,int,java.lang.Object,int,int)>")) {
				if (this.getIntrestedVariable().contains(invokExp.getArg(2))) {

					this.addIntrestedVariableIfNotConstant(invokExp.getArg(0));
				}
			} else if (TaintRules.getInstance().hasRuleFor(mthSig)) {

				if (invokExp instanceof InstanceInvokeExpr && TaintRules.getInstance().isBaseIntrested(mthSig)) {
					this.addIntrestedVariable(((InstanceInvokeExpr) invokExp).getBase());
					
				}
	
				for (int i : TaintRules.getInstance().getInterestedArgIndexes(invokExp.getMethod(), invokExp.getArgCount()))
					this.addIntrestedVariableIfNotConstant(invokExp.getArg(i));

				if (mthSig.equals("<android.content.SharedPreferences: java.lang.String getString(java.lang.String,java.lang.String)>") || (mthSig.contains("<android.content.Intent") && mthSig.contains(" get"))) {
					// System.out.println("Found SP");
					if (invokExp.getArgCount() > 0)
						if (invokExp.getArg(0).getType().toString().contains("java.lang.String"))
							updateICCKeys(null, invokExp.getArg(0));
				}

				List<Object> sdret = TaintRules.getInstance().getDataSrc(mthSig);
				if (sdret != null)
					for (Object obj : sdret) {
						this.addNewDataSrc(DataSourceType.valueOf(obj.toString()));
					}

			} else if (mthSig.startsWith("<android") || mthSig.startsWith("<java")|| mthSig.startsWith("<android.widget")) {

			} else if (mthSig.startsWith("<java.lang.reflect.Method")) {

			} else if (!diveIntoMethodCall(restAssignTo, leftisIntrestedData, leftisIntrestedCB, invokExp)) {

	
				if (leftisIntrestedCB) {
					if (invokExp instanceof InstanceInvokeExpr && isDefaultCheckClass(((InstanceInvokeExpr)invokExp).getBase())) 
						addVarToInterestedBlocks(leftInterestedBlocks, ((InstanceInvokeExpr) invokExp).getBase(), null);
					
					for (int i = 0; i < invokExp.getArgCount(); i++) {
						if (invokExp.getArg(i) instanceof Local) {
							// Logger.print("      Testsss: " + invokExp.getArg(i).getType().toString());
							addVarToInterestedBlocks(currentInterestedBlocks, invokExp.getArg(i), null);
						}
					}
				}

				if (invokExp.getMethod().isNative()) {
					for (int i = 0; i < invokExp.getArgCount(); i++) {
						if (containsIntrestedThingsInData) this.addIntrestedVariableIfNotConstant(invokExp.getArg(i));
					}
					Logger.printW(String.format("[%s] [Native call, just add all args]: %s=%s (%s)", this.hashCode(),
							restAssignTo, invokExp, invokExp.getClass()));
					
				} else {
					
					if (invokExp.getMethod().getDeclaringClass().isApplicationClass()){
						
					} else {
	
						if (invokExp instanceof InstanceInvokeExpr && isDefaultCheckClass(((InstanceInvokeExpr)invokExp).getBase())) {
							// so that we can get all the unhandled in the logs
							if (containsIntrestedThingsInData) this.addIntrestedVariable(((InstanceInvokeExpr) invokExp).getBase());
							
						}
						for (int i = 0; i < invokExp.getArgCount(); i++) {
							if (containsIntrestedThingsInData) this.addIntrestedVariableIfNotConstant(invokExp.getArg(i));
						}
					}
				}
			}
		}

		// }		

	}

	@Override
	public void caseIdentityStmt(IdentityStmt stmt) {
		// TODO Auto-generated method stub
		this.removeIntrestedVariable(stmt.getLeftOp());
		removeInterestedVariableInAllCB(stmt.getLeftOp());
		
		if (containsIntrestedThingsInCB || containsIntrestedThingsInData) {
			
			if (stmt.getRightOp() instanceof ParameterRef) {
				// Bruce
				// String tmp_paraType = ((ParameterRef) stmt.getRightOp()).getType().toString();
				// if (	tmp_paraType.startsWith("android.app") || tmp_paraType.startsWith("android.content")
				// 		|| tmp_paraType.startsWith("android.view") || tmp_paraType.startsWith("java.lang.Class")
				// 		|| tmp_paraType.startsWith("java.lang.Object")) {

				// } else {
					Value value = stmt.getRightOp();
					Value leftOp = stmt.getLeftOp();
					currentInterestedBlocks.forEach(cb -> {
						if (cb.isDeterminent(leftOp) && !cb.hasSolvedDeterminent()) {
								cb.updateDeterminent(value);
						}
					});
					// Logger.print(getCurrentInstruction().toString());
					if (containsIntrestedThingsInData) this.addIntrestedVariable(value);
					addVarToInterestedBlocks(currentInterestedBlocks, value, new StmtPoint(getCurrentMethod(), getCurrentBlock(), getCurrentInstruction()));
					if (foundKeys.keySet().contains(leftOp)) updateICCKeys(leftOp, value);
				// }

			} 
			// else if (stmt.getRightOp() instanceof ThisRef) {
				
			// 	SootClass sc = getCurrentMethod().getDeclaringClass();
			// 	HashSet<ConditionBlock> tempCBs = new HashSet<>();
				
			// 	currentInterestedBlocks.forEach(cb -> {if (cb.getUnsolvedField().containsKey(sc)) {
			// 		tempCBs.add(cb);
			// 		cb.isThisInterested = true;
			// 	} else cb.isThisInterested = false;});

			// 	addVarToInterestedBlocks(tempCBs, stmt.getRightOp(), new StmtPoint(getCurrentMethod(), getCurrentBlock(), getCurrentInstruction()));
			// }

		}
		// if (this.getIntrestedVariable().contains(stmt.getLeftOp())) {
		// 	this.removeIntrestedVariable(stmt.getLeftOp());
		// 	if (stmt.getRightOp() instanceof ParameterRef) {
		// 		// Bruce
		// 		String tmp_paraType = ((ParameterRef) stmt.getRightOp()).getType().toString();
		// 		if (tmp_paraType.startsWith("android") || tmp_paraType.startsWith("android.os")
		// 				|| tmp_paraType.startsWith("android.app") || tmp_paraType.startsWith("android.content")
		// 				|| tmp_paraType.startsWith("android.view") || tmp_paraType.startsWith("java.lang.Class")
		// 				|| tmp_paraType.startsWith("java.lang.Object")) {

		// 		} else {
		// 			this.addIntrestedVariable(stmt.getRightOp());
		// 		}
		// 		//

		// 	} else {
		// 		Logger.printW(String.format("[%s] [Can't Handle caseIdentityStmt->RightOpUnrecognized]: %s (%s)",
		// 				this.hashCode(), stmt, stmt.getLeftOp().getClass()));
		// 	}
		// } else {
		// 	Logger.printW(String.format("[%s] [Can't Handle caseIdentityStmt->LeftOpNotIntrested]: %s (%s)",
		// 			this.hashCode(), stmt, stmt.getLeftOp().getClass()));
		// }
	}

	@Override
	public void caseIfStmt(IfStmt stmt) {
		// TODO Auto-generated method stub
		// Logger.printW("[ignore if]");

		// Logger.printI(stmt.toString());
		// Logger.printI(stmt.getCondition().toString());
		// for (ValueBox vb : stmt.getCondition().getUseBoxes()) 
		// 	Logger.printI(vb.getValue() + " " + (vb.getValue() instanceof NullConstant));
		
		Block lastBlock = this.getLastBlock();

		// boolean isSatisfyCondition = lastBlock.getHead().toString().equals(gotoStmt) ? true : false;
		
		boolean isSatisfyCondition = BlockUtility.isEqualBlock(this.getCurrentBlock().getSuccs().get(0), lastBlock) ? false : true;
		Value target = stmt.getCondition();
		
		// Create a new Condition Point
		StmtPoint sp = new StmtPoint(getCurrentMethod(), getCurrentBlock(), currentInstruction);
		ConditionBlock cb = new ConditionBlock(sp, target, isSatisfyCondition);

		if (target.getUseBoxes().get(0).getValue() instanceof Local) cb.addInterestedVariable(target.getUseBoxes().get(0).getValue());

		if (target.getUseBoxes().get(1).getValue() instanceof Local) cb.addInterestedVariable(target.getUseBoxes().get(1).getValue());
		
		
		if (target instanceof BinopExpr) {
			BinopExpr be = ((BinopExpr) target);

			String operator = be.getSymbol();
			Value left, right;
			
			if (target.getUseBoxes().get(0).getValue() instanceof Local) {
				left = be.getOp1();
				right = be.getOp2();
			} else {
				left = be.getOp2();
				right = be.getOp1();	
			}

			// Logger.print("  " + left + operator + right);

			if (right instanceof Constant) {
				cb.addDeterminent(left, (Constant) right, operator, isSatisfyCondition);
			} else {
				cb.addDeterminent(left, right, operator, isSatisfyCondition);
				// Logger.printE("Not a constant determinent: " + currentInstruction);
			}
		}
		
		conditionChain.add(cb);


	}

	@Override
	public void defaultCase(Object obj) {
		// TODO Auto-generated method stub
		Logger.printW(String.format("[%s] [Can't Handle]: %s (%s)", this.hashCode(), obj, obj.getClass()));
	}

	public boolean diveIntoMethodCall(Value leftOp, boolean leftisIntrestedData, boolean leftisInterestedCB, InvokeExpr ive) {
		
		GlobalStatistics.getInstance().countDiveIntoMethodCall();
		
		// Logger.print(ive + " " + ive.getMethod().getDeclaringClass().isApplicationClass() + " " + ive.getMethod().isConcrete());

		// System.out.println(this.getCurrentInstruction());
		if (!ive.getMethod().getDeclaringClass().isApplicationClass() || !ive.getMethod().isConcrete())
			return false;

		
		if (!leftisIntrestedData) return false;

		String className = ive.getMethod().getDeclaringClass().toString();

		if (className.startsWith("android.") || className.startsWith("java.") || className.startsWith("androidx.")) return false;

		// this.getExecTrace().remove(this.getCurrentInstruction());	// TODO: check in CB cases
		removeFromExecTrace(currentInstruction);

		CallStackItem citem = new CallStackItem(this.getCurrentMethod(), this.getCurrentBlock(),
				this.getCurrentInstruction(), leftOp, getcurrentInterestedBlocks());

		this.getCallStack().push(citem);

		GlobalStatistics.getInstance().updateMaxCallStack(this.getCallStack().size());

		CompleteBlockGraph cbg = BlockGenerator.getInstance().generate(ive.getMethod().retrieveActiveBody());
		List<Block> tails = new ArrayList<Block>();

		for (Block block : cbg.getTails()) {
			if (leftOp == null || block.getTail() instanceof ReturnStmt) {
				tails.add(block);
			}
		}

		if (tails.size() == 0) {
			Logger.printW(String.format("[%s] [All Tail not ReturnStmt]: %s (%s)", this.hashCode(),
					this.getCurrentInstruction(), this.getCurrentInstruction().getClass()));
		}

		List<BacktracingContext> bcs = new ArrayList<BacktracingContext>();
		int len = tails.size();

		for (int i = 1; i < len; i++) {
			bcs.add(this.clone());
		}
		bcs.add(0, this);

		BacktracingContext tbc;
		Block tblock;
		Stmt rets;
		ParameterTransferStmt tmp;
		for (int i = 0; i < len; i++) {
			tbc = bcs.get(i);
			tblock = tails.get(i);

			rets = (Stmt) tblock.getTail();

			

			if (leftOp != null) {

				if (!(tblock.getTail() instanceof ReturnStmt)) {
					Logger.printW(String.format("[%s] [Tail not ReturnStmt]: %s (%s)", this.hashCode(),
							tblock.getTail(), tblock.getTail().getClass()));
				}


				tmp = new ParameterTransferStmt(leftOp, ((ReturnStmt) rets).getOp());
				StmtPoint tmpSPaaa = new StmtPoint(this.getCurrentMethod(), this.getCurrentBlock(), tmp);

				if (leftisIntrestedData) {
					
					tbc.getExecTrace().add(0, tmpSPaaa);
					tbc.addIntrestedVariableIfNotConstant(((ReturnStmt) rets).getOp()); // Start to track the returned var
					if (foundKeys.keySet().contains(leftOp)) updateICCKeys(leftOp, ((ReturnStmt) rets).getOp());
				}
				
				if (leftisInterestedCB) {
					for (ConditionBlock cb : leftInterestedBlocks) {
						if (cb.isDeterminent(leftOp) && !cb.hasSolvedDeterminent())
							cb.updateDeterminent(((ReturnStmt) rets).getOp());
					}

					if (((ReturnStmt) rets).getOp() instanceof Local)
						addVarToInterestedBlocks(leftInterestedBlocks,((ReturnStmt) rets).getOp(), tmpSPaaa);
					else leftInterestedBlocks.forEach(cb -> {cb.getCBExecTrace().add(0, tmpSPaaa);});

				}
				// parameter
			}
			tbc.setCurrentMethod(ive.getMethod());
			tbc.setCurrentBlock(tblock);
			tbc.setCurrentInstruction(rets);
			
		}
		bcs.remove(0);

		bcs.forEach(bc -> {
			this.put(bc);
		});
		bcs.clear();

		return true;
	}

	// //////////////////////////////////////////////////////
	// ////////////////////// StmtPath //////////////////////
	@Override
	public Unit getStmtPathHeader() {
		// TODO Auto-generated method stub
		return this.getExecTrace().get(0).getInstruction_location();
	}

	@Override
	public Unit getSuccsinStmtPath(Unit u) {
		// TODO Auto-generated method stub
		if (u == null)
			return null;
		Unit told = null;
		for (StmtPoint tnew : this.getExecTrace()) {
			if (u == told) {
				return tnew.getInstruction_location();
			}
			told = tnew.getInstruction_location();
		}

		return null;
	}

	@Override
	public Unit getPredsinStmtPath(Unit u) {
		// TODO Auto-generated method stub
		if (u == null)
			return null;
		Unit told = null;
		for (StmtPoint tnew : this.getExecTrace()) {
			if (u == tnew.getInstruction_location()) {
				return told;
			}
			told = tnew.getInstruction_location();
		}

		return null;
	}

	@Override
	public Unit getStmtPathTail() {
		// TODO Auto-generated method stub
		return this.getExecTrace().get(this.getExecTrace().size() - 1).getInstruction_location();
	}

	@Override
	public List<StmtPoint> getStmtPath() {
		return this.getExecTrace();
	}

	// //////////////////////////////////////////////////////
	// ////////////////////// ICollecter ////////////////////
	List<BacktracingContext> newGeneratedContext = new ArrayList<BacktracingContext>();

	@Override
	public void clear() {
		// TODO Auto-generated method stub
		newGeneratedContext.clear();
	}

	@Override
	public void put(BacktracingContext bc) {
		newGeneratedContext.add(bc);
	}

	@Override
	public List<BacktracingContext> retrieve() {
		// TODO Auto-generated method stub
		return newGeneratedContext;
	}

	// //////////////////////////////////////////////////////

	public JSONObject toJson() {
		JSONObject result = new JSONObject();

		result.put("hashcode", this.hashCode());

		for (SootMethod sm : methodes) {
			result.append("methodes", sm.toString());
		}
		for (Pair<Block, Integer> blk : blockes) {
			result.append("blockes", blk.getValue0().hashCode());
		}
		for (StmtPoint stmt : execTrace) {
			result.append("execTrace", stmt.toJSON());
		}

		JSONObject execTraceDetails = new JSONObject();
		HashSet<ValueBox> boxes = new HashSet<ValueBox>();
		for (StmtPoint stmt : execTrace) {
			boxes.addAll(stmt.getInstruction_location().getUseAndDefBoxes());
		}

		JSONObject tmp;
		for (ValueBox vb : boxes) {
			tmp = new JSONObject();
			tmp.put("class", vb.getValue().getClass().getSimpleName());
			tmp.put("str", vb.getValue().toString());
			tmp.put("hashCode", vb.getValue().hashCode() + "");

			execTraceDetails.put(vb.getValue().hashCode() + "", tmp);
		}
		result.put("ValueBoxes", execTraceDetails);

		return result;
	}


	public ArrayList<JSONObject> toCondJSON() {
		ArrayList<JSONObject> jsobj = new ArrayList<>();
		for (ConditionBlock cb : getConditionChain()) jsobj.add(cb.toJSON());
		
		return jsobj;
	}


    // public void printTrace() {
    //     for (StmtPoint sp : this.execTrace) {
    //         System.out.println("instr: " + sp.getInstruction_location() + " block: " + sp.getBlock_location().getIndexInMethod());
    //     }
    // }

	public HashMap<String, HashSet<String>> getBlock2AffectedCons() {
		return this.block2AffectedCons;
	}

	public ArrayList<String> getBlockTags() {
		return this.blockesTag;
	}

	public ArrayList<SootMethod> getExtendedMthd() {
		return this.extendedMthd;
	}

	public HashSet<String> getDataCriticalBlocks() {
		return this.criticalDataBlocks;
	}
	
	// public Value
	public void updateICCKeys(Value oldv, Value newv) {
		if (newv instanceof StringConstant) {
			
			String keyVal = ((StringConstant) newv).value;
			// System.out.print("Found Key: " + keyVal);

			if (oldv == null) {
				String label = getCurrentInstruction().toString().contains("SharedPreferences") ? "ICC_SP:" + keyVal: "ICC_INTENT:" + keyVal;
				getExecTrace().get(0).setICC(label); 	// Can resolve the key in the ICC get invocation

			} else {
				StmtPoint p = foundKeys.get(oldv);
				if (p == null) return;
				foundKeys.remove(oldv);
				String label = p.getInstruction_location().toString().contains("SharedPreferences") ? "ICC_SP:" + keyVal: "ICC_INTENT:" + keyVal;
				p.setICC(label);
			}

			if (!runTest.processedKeys.contains(keyVal)) {
				runTest.newAddedKeys.add(keyVal);
				return;
			}
			

		} else {
			if (oldv == null) {
				foundKeys.put(newv, getExecTrace().get(0));
			} else {
				if (!(foundKeys.keySet().contains(oldv))) return;
				foundKeys.put(newv, foundKeys.get(oldv));
				foundKeys.remove(oldv);
			}
		}
	}

}
