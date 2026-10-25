package prinlog.stringvsa.graph;

import java.lang.invoke.SwitchPoint;
import java.util.HashSet;
import java.util.Hashtable;

import prinlog.stringvsa.base.StmtPoint;
import prinlog.stringvsa.utility.ListUtility;
import prinlog.stringvsa.utility.Logger;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.NewExpr;
import soot.jimple.Stmt;
import soot.jimple.parser.node.Switchable;

public class CallGraph {

	static Hashtable<String, CallGraphNode> nodes = new Hashtable<String, CallGraphNode>();

	static Hashtable<String, HashSet<SootMethod>> fieldSetters = new Hashtable<String, HashSet<SootMethod>>();

	public static Hashtable<SootClass, HashSet<StmtPoint>> class2NewSite = new Hashtable<SootClass, HashSet<StmtPoint>>();

	public static void init() {
		long st = System.currentTimeMillis();
		CallGraphNode tmp;
		Value tv;
		FieldRef fr;
		String str;
		for (SootClass sclas : Scene.v().getClasses()) {

			for (SootMethod smthd : sclas.getMethods()) {

				tmp = new CallGraphNode(smthd);
				nodes.put(smthd.toString(), tmp);
				if (smthd.isConcrete())
					smthd.retrieveActiveBody();
			}
		}
		Logger.printI("[CG time]:" + (System.currentTimeMillis() - st));
		for (SootClass sclas : Scene.v().getClasses()) {
			for (SootMethod smthd : ListUtility.clone(sclas.getMethods())) {

				if (!smthd.isConcrete())
					continue;
				Body body = smthd.retrieveActiveBody();
				if (body == null)
					continue;
				for (Unit unit : body.getUnits()) {

					if (unit instanceof Stmt) {
						if (((Stmt) unit).containsInvokeExpr()) {
							try {

								addCall(smthd, ((Stmt) unit).getInvokeExpr().getMethod());
							} catch (Exception e) {
								Logger.printW(e.getMessage());
							}
						}
						for (ValueBox var : ((Stmt) unit).getDefBoxes()) {
							tv = var.getValue();

							if (tv instanceof FieldRef) {
								fr = (FieldRef) tv;
								if (fr.getField().getDeclaringClass().isApplicationClass()) {
									str = fr.getField().toString();
									if (!fieldSetters.containsKey(str)) {
										fieldSetters.put(str, new HashSet<SootMethod>());
									}
									fieldSetters.get(str).add(smthd);
								}
							}
						}
					}
				}
			}
		}

		Logger.printI("[CG time]:" + (System.currentTimeMillis() - st));
	}

	private static void addCall(SootMethod from, SootMethod to) {
		CallGraphNode fn, tn;
		fn = getNode(from);
		tn = getNode(to);


		if (fn == null || tn == null) {
			return;
		}

		fn.addCallTo(tn);
		tn.addCallBy(fn);

	}

	public static CallGraphNode getNode(SootMethod from) {
		return getNode(from.toString());
	}

	public static CallGraphNode getNode(String from) {
		return nodes.get(from);
	}

	public static HashSet<SootMethod> getSetter(SootField sootField) {
		return fieldSetters.get(sootField.toString());
	}

	public static HashSet<StmtPoint> getNewClassPoints(SootClass sclas) {
		return class2NewSite.containsKey(sclas) ? class2NewSite.get(sclas) : null;
	}
}
