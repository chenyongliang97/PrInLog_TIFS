package prinlog.stringvsa.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.json.JSONObject;

import prinlog.stringvsa.backwardslicing.DataSourceType;

public interface IDGNode {

	public Set<IDGNode> getDependents();
	
	public Set<IDGNode> getDirectAndIndirectDependents(Set<IDGNode> ret);

	public int getUnsovledDependentsCount();

	public boolean hasSolved();

	public void solve();

	public boolean canBePartiallySolve();

	public void initIfHavenot();

	public boolean inited();

	public HashSet<DataSourceType> getDataSrcs();
	
	public HashSet<String> getDataHcStrings();
	
	public ArrayList<HashMap<Integer, HashSet<String>>> getResult();

	public JSONObject toJson();
}
