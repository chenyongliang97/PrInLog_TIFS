package prinlog.stringvsa.graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.json.JSONObject;

import prinlog.stringvsa.backwardslicing.BackwardContext;
import prinlog.stringvsa.backwardslicing.DataSourceType;
import prinlog.stringvsa.base.StmtPoint;
import prinlog.stringvsa.base.TargetType;
import prinlog.stringvsa.graph.specialcase.FindInClassAdd;
import prinlog.stringvsa.utility.Logger;
import soot.SootField;
import soot.jimple.Stmt;

public class HeapObject implements IDGNode {
	DGraph dg;
	
	static public HashMap<String, HeapObject> hos = new HashMap<String, HeapObject>();
	SootField sootField = null;
	String ICCKey = null;
	boolean inited = false;
	boolean solved = false;
	ArrayList<ValuePoint> vps;
	HashSet<ValuePoint> solvedVps = new HashSet<ValuePoint>();

	ArrayList<HashMap<Integer, HashSet<String>>> result = new ArrayList<HashMap<Integer, HashSet<String>>>();

	public HeapObject(DGraph dg, SootField sootField) {
		this.dg = dg;
		this.sootField = sootField;
		this.vps = new ArrayList<>();
	}

	public HeapObject(DGraph dg, String ICCKey) {
		this.dg = dg;
		this.ICCKey = ICCKey;
		this.vps = new ArrayList<>();
	}

	public ArrayList<ValuePoint> getVPs() {
		return this.vps;
	}

	@Override
	public Set<IDGNode> getDependents() {
		// TODO Auto-generated method stub

		HashSet<IDGNode> dps = new HashSet<IDGNode>();
		for (ValuePoint vp : vps) {
			dps.add(vp);
			// System.out.print(getField() + " " + vp.bcs.size());
		}
		return dps;

	}

	@Override
	public int getUnsovledDependentsCount() {
		// TODO Auto-generated method stub
		int count = 0;
		for (IDGNode vp : getDependents()) {
			if (!vp.hasSolved()) {
				count++;
			}
		}
		return count;
	}

	@Override
	public boolean hasSolved() {
		// TODO Auto-generated method stub
		return solved;
	}

	@Override
	public void solve() {
		// TODO Auto-generated method stub
		solved = true;
		Logger.print("[HEAP SOLVE]" + sootField);
		Logger.print("[SOLVING ME]" + this.hashCode());

		for (ValuePoint vp : vps) {
			ArrayList<HashMap<Integer, HashSet<String>>> vpResult = vp.getResult();
			for (HashMap<Integer, HashSet<String>> res : vpResult) {
				if (res.containsKey(-1)) {
					result.add(res);
				}
			}
		}
	}

	@Override
	public boolean canBePartiallySolve() {
		boolean can = false;
		for (ValuePoint vp : vps) {
			if (!solvedVps.contains(vp) && vp.hasSolved()) {
				solvedVps.add(vp);
				can = true;
				for (HashMap<Integer, HashSet<String>> res : vp.getResult()) {
					if (res.containsKey(-1)) {
						result.add(res);
					}
				}
			}
		}

		if (can) {
			solved = true;
		}

		return can;
	}

	@Override
	public void initIfHavenot() {
		// TODO Auto-generated method stub
		Logger.print("[HEAP INIT]" + sootField + " " + ICCKey);
		if (this.sootField != null) {
			vps = new ArrayList<ValuePoint>();
			ValuePoint tmp;
			List<StmtPoint> sps = StmtPoint.findSetter(sootField);


			int i = 0;
			for (StmtPoint sp : sps) {
				i++;
				tmp = new ValuePoint(dg, sp.getMethod_location(), sp.getBlock_location(), sp.getInstruction_location(), Collections.singletonList(TargetType.RIGHTPART.getType()));
				tmp.setAppendix(sootField.toString());
				vps.add(tmp);
				if (i >= 5) break;
			}

			// if (FindInClassAdd.isAddable(sootField))
			// 	for (StmtPoint sp : FindInClassAdd.getAll(dg, sootField)) {
			// 		int targetRegIndex = ((Stmt) sp.getInstruction_location()).getInvokeExpr().getArgCount() - 1;
			// 		tmp = new ValuePoint(dg, sp.getMethod_location(), sp.getBlock_location(), sp.getInstruction_location(), Collections.singletonList(targetRegIndex));
			// 		tmp.setAppendix(sootField.toString());
			// 		vps.add(tmp);
			// 	}
			
			
		}


		inited = true;
	}

	@Override
	public boolean inited() {
		// TODO Auto-generated method stub
		return inited;
	}

	@Override
	public ArrayList<HashMap<Integer, HashSet<String>>> getResult() {
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((sootField == null) ? 0 : sootField.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		HeapObject other = (HeapObject) obj;
		if (sootField == null) {
			if (other.sootField != null)
				return false;
		} else if (!sootField.equals(other.sootField))
			return false;
		return true;
	}

	public JSONObject toJson() {
		JSONObject js = new JSONObject();
		JSONObject tmp_js;
		BackwardContext tmp_bc;
		
		
		js.put("HashCode", this.hashCode());
		js.put("Type", "HeapObject");
		js.put("Field", sootField);
		js.put("ICCKey", this.ICCKey);
		js.put("Solved", hasSolved());

		for (IDGNode var : this.getDependents()) {
			js.append("Depend", var.toJson());

		}

		return js;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		if (!inited)
			return super.toString();
		StringBuilder sb = new StringBuilder();
		sb.append("===========================");
		sb.append(this.hashCode());
		sb.append("===========================\n");
		sb.append("Field: " + sootField + "\n");
		sb.append("Solved: " + hasSolved() + "\n");
		sb.append("Depend: ");
		for (IDGNode var : this.getDependents()) {
			sb.append(var.hashCode());
			sb.append(", ");
		}
		sb.append("\n");
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

	

	public static HeapObject getInstance(DGraph dg, SootField sootField) {
		String str = sootField.toString();
		if (!hos.containsKey(str)) {
			hos.put(str, new HeapObject(dg, sootField));
		}
		return hos.get(str);
	}

	public static HeapObject getInstance(DGraph dg, String icckey) {
		if (!hos.containsKey(icckey)) {
			Logger.print(" New added ICCKEY: " + icckey);
			hos.put(icckey, new HeapObject(dg, icckey));
		}
		return hos.get(icckey);
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
		return toRet;
	}

	public SootField getField() {
		return this.sootField;
	}

	public void releaseHO() {
		solvedVps.clear();
		vps.clear();
	}
}
