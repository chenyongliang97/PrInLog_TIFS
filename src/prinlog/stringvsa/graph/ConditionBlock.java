package prinlog.stringvsa.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.locks.Condition;

import org.json.JSONObject;

import prinlog.stringvsa.backwardslicing.BacktracingContext;
import prinlog.stringvsa.backwardslicing.BackwardContext;
import prinlog.stringvsa.backwardslicing.BackwardController;
import prinlog.stringvsa.base.StmtPoint;
import prinlog.stringvsa.utility.Logger;
import prinlog.stringvsa.utility.OtherUtility;
import soot.Local;
import soot.SootClass;
import soot.SootField;
import soot.Unit;
import soot.Value;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.IntConstant;
import soot.jimple.NullConstant;
import soot.jimple.NumericConstant;
import soot.jimple.StaticFieldRef;

public class ConditionBlock {
    public String TAG;

    public Value conditionValue = null;
    // public boolean
    ArrayList<StmtPoint> execTrace = null;
    StmtPoint startPoint = null;
    boolean isSatisfyCondition;

    HashSet<Value> interestedVariable;
    public boolean isThisInterested = false;
    public boolean isIF = true;

    // HashMap<SootClass, HashSet<SootField>> unsolvedField;

    Determinent determinent;

    public boolean solvedDeterminent = false;

    public class Determinent {
        Value interestedVar;
        SootField interestedField;
        OPS target_ops;
        Value target;

        public Determinent clone() {
            Determinent tmp = new Determinent();
            tmp.interestedVar = this.interestedVar;
            tmp.target_ops = this.target_ops;
            tmp.target = this.target;
            tmp.interestedField = this.interestedField;
            return tmp;

        }


    }


    public static enum OPS{
        NOT_EQUAL, GREATER, LESS, GREATER_EQUAL, LESS_EQUAL, EQUAL;
    }

    static HashMap<String, OPS> string2Op = new HashMap<String, OPS>();
    static {
        string2Op.put(" != ", OPS.NOT_EQUAL);
        string2Op.put(" == ", OPS.EQUAL);
        string2Op.put(" >= ", OPS.GREATER_EQUAL);
        string2Op.put(" <= ", OPS.LESS_EQUAL);
        string2Op.put(" < ", OPS.LESS);
        string2Op.put(" > ", OPS.GREATER);
    }


    public ConditionBlock(StmtPoint startPoint, Value target, boolean b) {
        this.conditionValue = target;
        this.startPoint = startPoint;
        execTrace = new ArrayList<>();
        isSatisfyCondition = b;
        interestedVariable = new HashSet<>();
        isThisInterested = false;
        // unsolvedField = new HashMap<>();
        execTrace.add(startPoint);
        TAG = startPoint.getMethod_location().toString() + "+" + String.valueOf(startPoint.getBlock_location().getIndexInMethod());
        
    }

    @SuppressWarnings("unchecked")
    public ConditionBlock(ConditionBlock oldb) {
        this.conditionValue = (Value) oldb.getConditionValue();
        this.startPoint =  new StmtPoint(oldb.getStartPoint().getMethod_location(), oldb.getStartPoint().getBlock_location(), oldb.getStartPoint().getInstruction_location());
        this.execTrace = (ArrayList<StmtPoint>) oldb.getCBExecTrace().clone();
        this.interestedVariable = (HashSet<Value>) oldb.getInterestedVariables().clone();
        this.isSatisfyCondition = oldb.isSatisfyCondition();
        this.isThisInterested = oldb.isThisInterested;
        // unsolvedField = new HashMap<SootClass, HashSet<SootField>>();
        
        // oldb.getUnsolvedField().forEach((sclas, fieldSet) -> {
        //     unsolvedField.put(sclas, new HashSet());
        //     fieldSet.forEach(f -> unsolvedField.get(sclas).add(f));
        // });
        // (HashMap<SootClass, HashSet<SootField>>) oldb.getUnsolvedField().clone();
        this.determinent = (Determinent) oldb.getDeterminent().clone();
        this.solvedDeterminent = oldb.hasSolvedDeterminent();
        isIF = oldb.isIF;

        TAG = oldb.TAG;
    }

    public void setNotIF() {
		this.isIF = false;
        TAG = "METHOD INVOKE: ".concat(TAG);
	}

    public void setTerminateCallback() {
        TAG = "TERMINATING ".concat(TAG);
	}

    public Value getConditionValue() {
        return this.conditionValue;
    }

    public StmtPoint getStartPoint() {
        return this.startPoint;
    }

    public ArrayList<StmtPoint> getCBExecTrace() {
        return this.execTrace;
    }

    public boolean isSatisfyCondition() {
        return isSatisfyCondition;
    }

    public boolean isInterested(Value v) {
        // if (v instanceof FieldRef) {
        //     SootField field = ((FieldRef) v).getField();
        //     SootClass sc = field.getDeclaringClass();
        //     return (unsolvedField.containsKey(sc) && unsolvedField.get(sc).contains(field));
        // } 
        return interestedVariable.contains(v);

    }

    public void addInterestedVariable(Value v) {
        interestedVariable.add(v);
    }

    public HashSet<Value> getInterestedVariables() {
        return this.interestedVariable;
    }

    public void removeInterestedVariable(Value v) {
        this.interestedVariable.remove(v);
    }

    public void printExecTrace() {
        for (StmtPoint sp : getCBExecTrace()) 
            Logger.printI(sp.getInstruction_location().toString());
    }


	// public HashMap<SootClass, HashSet<SootField>> getUnsolvedField() {
	// 	return this.unsolvedField;
	// }

	// public void solveField(FieldRef field) {
	// 	SootClass sc = field.getField().getDeclaringClass();
    //     SootField f = field.getField();
	// 	if (unsolvedField.containsKey(sc)) {
	// 		unsolvedField.get(sc).remove(f);
    //         // Logger.print("  REMOVED : " + sc.toString() + " " + f.toString());
	// 		if (unsolvedField.get(sc).size() == 0) {
	// 			unsolvedField.remove(sc);
    //             // Logger.print("  REMOVED : " + sc.toString());
	// 		}

	// 	}
	// }

	// public void addUnsolvedField(FieldRef field) {
	// 	SootClass sc = field.getField().getDeclaringClass();
	// 	if (!unsolvedField.containsKey(sc)) unsolvedField.put(sc, new HashSet<>());
	// 	unsolvedField.get(sc).add(field.getField());

    //     // Logger.print("  Added : " + sc.toString() + " " + unsolvedField.get(sc).toString());
	// }

    public void addDeterminent(Value left, Value right, String operator, boolean isSatisfyCondition) {
        determinent = new Determinent();
        determinent.interestedVar = left;
        determinent.target = right;
        determinent.interestedField = null;
        if (!(right instanceof Constant) || !string2Op.containsKey(operator)) return;
        switch (string2Op.get(operator)) {
            case EQUAL:
                determinent.target_ops = isSatisfyCondition ? OPS.EQUAL : OPS.NOT_EQUAL;
                break;

            case NOT_EQUAL:
                determinent.target_ops = isSatisfyCondition ? OPS.NOT_EQUAL : OPS.EQUAL;
                break;
            
            case GREATER:
                determinent.target_ops = isSatisfyCondition ? OPS.GREATER : OPS.LESS_EQUAL;
                break;
            
            case LESS:
                determinent.target_ops = isSatisfyCondition ? OPS.LESS : OPS.GREATER_EQUAL;
                break;
            
            case GREATER_EQUAL:
                determinent.target_ops = isSatisfyCondition ? OPS.GREATER_EQUAL : OPS.LESS;
                break;

            case LESS_EQUAL:
                determinent.target_ops = isSatisfyCondition ? OPS.LESS_EQUAL : OPS.GREATER;
                break;

            default:
                Logger.printE("Cannot find operator for: " + operator);
        }

        // Logger.print(" +++ New added determinent: " + left + operator + right + determinent.target_ops);

    }

    public Determinent getDeterminent() {
        return this.determinent;
    }

    public boolean hasSolvedDeterminent() {
        return this.solvedDeterminent;
    }

    

    public boolean satisfyDeterminent(Constant v) {    // numerical or Null
        
        if (!(determinent.target instanceof Constant)) return true;

        Constant t = (Constant) determinent.target;
        
        // Logger.print(" Now evaluating " + v + " " + t + " " + determinent.target_ops);

        switch (determinent.target_ops) {
            case EQUAL:
                solvedDeterminent = true;
                return OtherUtility.isStrConstant(v) ? (t.toString().equals(v.toString())) : getValue(t) == getValue(v);
            
            case NOT_EQUAL:
                solvedDeterminent = true;
                return OtherUtility.isStrConstant(v) ? (!t.toString().equals(v.toString())) : getValue(t) != getValue(v);

            case GREATER:
                solvedDeterminent = true;
                return (getValue(v) > getValue(t));

            case LESS:
                solvedDeterminent = true;
                return (getValue(v) < getValue(t));

            case GREATER_EQUAL:
                solvedDeterminent = true;
                return (getValue(v) >= getValue(t));

            case LESS_EQUAL:
                solvedDeterminent = true;
                return (getValue(v) <= getValue(t));

            default:
                Logger.printW("Cannot eval Constant: " + v.toString());
                return true;
        }
    }

    public boolean isDeterminent(Value v) {
        // Logger.print(" +++ Checking " + v.toString() + (v instanceof FieldRef));
        return v instanceof FieldRef ? ((FieldRef) v).getField().equals(determinent.interestedField) : v.equals(determinent.interestedVar);
    }

    public JSONObject toJSON() {
        JSONObject jsobj = new JSONObject();
        jsobj.put("condition", getConditionValue().toString());
        jsobj.put("satisfy", Boolean.valueOf(isSatisfyCondition()));
        jsobj.put("solvedDeterminent", Boolean.valueOf(hasSolvedDeterminent()));
        ArrayList<JSONObject> tmpl = new ArrayList<JSONObject>();

        for (StmtPoint sp : getCBExecTrace())
			tmpl.add(sp.toJSON());

        jsobj.put("execTrace", tmpl);
        return jsobj;
    }

    public void updateDeterminent(Value v) {
        if (v instanceof FieldRef) {
            
            getDeterminent().interestedField = ((FieldRef) v).getField();
            getDeterminent().interestedVar = null;
            // Logger.print(" +++++ UPDATE determinent to " + getDeterminent().interestedField.toString());
        } else if (v instanceof Local) {
            getDeterminent().interestedVar = v;
            getDeterminent().interestedField = null;
        }
    }

    public ConditionBlock clone() {
		ConditionBlock tmp = new ConditionBlock(this);
		return tmp;
	}


    public static double getValue(Constant value) {
        if (value instanceof NullConstant) return -19970708;
        double retVal;
        String str = value.toString();
        boolean isInt = value.getType().toString().equals("int");
		boolean isLong = value.getType().toString().equals("long");
		boolean isFloat = value.getType().toString().equals("float");
		boolean isDouble = value.getType().toString().equals("double");

        if (isInt) return (double) OtherUtility.string2Int(str);
        if (isLong) return (double) OtherUtility.string2Long(str);
        if (isFloat) return (double) OtherUtility.string2Float(str);
        return OtherUtility.string2Double(str);
    }

}