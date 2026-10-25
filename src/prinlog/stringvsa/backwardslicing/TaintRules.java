package prinlog.stringvsa.backwardslicing;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.json.JSONObject;

import soot.SootMethod;

public class TaintRules {

	static String RULE_PATH = "taintrules.json";
	static String RULE_TAINT_KEY = "taint";
	static String RULE_TAINT_BASENAME = "base";
	static String RULE_TAINT_ALLARGS = "args";
	static String RULE_TAINT_ARGS_PRE = "arg";
	static String RULE_TAINT_IS_SYS_API_SRC = "isSystemAPISrc";

	static JSONObject rules;
	static {
		String rjs = null;
		try {
			rjs = new String(Files.readAllBytes(Paths.get(RULE_PATH)));
		} catch (IOException e) {
			System.err.println("TaintRules load error!");
			e.printStackTrace();
			System.exit(0);
		}

		rules = new JSONObject(rjs);
	}

	private TaintRules() {
	}

	static TaintRules tr = new TaintRules();

	public static TaintRules getInstance() {
		return tr;
	}

	HashMap<String, Boolean> CACHEisBaseIntrested = new HashMap<String, Boolean>();
	HashMap<String, List<Integer>> CACHEgetInterestedArgIndexes = new HashMap<String, List<Integer>>();

	public boolean hasRuleFor(String msig) {
		return rules.has(msig)
				|| msig.contains("<android.os.Bundle: void put") 
				|| msig.contains("<android.os.BaseBundle: void put")
				|| msig.contains("<org.json.JSONObject: org.json.JSONObject put")
				
				|| msig.contains("<com.flurry.android.FlurryEvent.Params: put")	//putString/Boolean/Double/Integer/Long : static invoke
				|| msig.contains("<com.flurry.android.FlurryAgent: void addSessionProperty")
				|| msig.contains("<com.flurry.android.FlurryAgent: void addOrigin")
				|| msig.contains("<com.flurry.android.FlurryAgent: set")
				
				|| msig.contains("<com.google.android.gms.analytics.Tracker: set")
				|| (msig.contains("<com.google.android.gms.analytics.HitBuilders") && (msig.contains(" build()")|| msig.contains(" set")))
						
				|| msig.contains("<com.google.firebase.analytics.FirebaseAnalytics: void setUser")
				|| msig.contains("<com.google.firebase.analytics.FirebaseAnalytics: void setCurrentScreen")
				
				|| msig.contains("<com.facebook.appevents.AppEventsLogger: void setUser")	//setUserData, setUserID
				|| msig.contains("<com.facebook.appevents.AppEventsLogger: void setPushNotificationsRegistrationId")
				|| msig.contains("<com.facebook.appevents.AppEventsLogger: void updateUserProperties")
				
				|| msig.contains("<com.mixpanel.android.mpmetrics.MixpanelAPI: void registerSuperProperties");
	}

	public boolean isBaseIntrested(String msig) {
		if (CACHEisBaseIntrested.containsKey(msig)) {
			return CACHEisBaseIntrested.get(msig);
		}
		boolean res = false;
		if (msig.contains("<android.os.Bundle: void put") 
			|| msig.contains("<android.os.BaseBundle: void put")
			|| msig.contains("<org.json.JSONObject: org.json.JSONObject put")
			
			|| msig.contains("<com.flurry.android.FlurryEvent.Params: put")
			|| msig.contains("<com.flurry.android.FlurryAgent: void addSessionProperty")
			|| msig.contains("<com.flurry.android.FlurryAgent: void addOrigin")
			
			|| msig.contains("<com.google.android.gms.analytics.Tracker: set")
			|| (msig.contains("<com.google.android.gms.analytics.HitBuilders") && (msig.contains(" build()") || msig.contains(" set")))
			
			|| msig.contains("<com.google.firebase.analytics.FirebaseAnalytics: void setUser")
			// || msig.contains("<com.google.firebase.analytics.FirebaseAnalytics: void setCurrentScreen")
			
			|| msig.contains("<com.facebook.appevents.AppEventsLogger: void setUser")	//setUserData, setUserID
			|| msig.contains("<com.facebook.appevents.AppEventsLogger: void setPushNotificationsRegistrationId")
			|| msig.contains("<com.facebook.appevents.AppEventsLogger: void updateUserProperties")
			
			|| msig.contains("<com.mixpanel.android.mpmetrics.MixpanelAPI: void registerSuperProperties"))
			res = true;
		else if (rules.has(msig))res = rules.getJSONObject(msig).getJSONArray(RULE_TAINT_KEY).toList().contains(RULE_TAINT_BASENAME);
	
		CACHEisBaseIntrested.put(msig, res);
		return res;
	}

	public List<Integer> getInterestedArgIndexes(SootMethod mthSig, int argsLen) {
		String msig = mthSig.toString();
		if (CACHEgetInterestedArgIndexes.containsKey(msig)) {
			return CACHEgetInterestedArgIndexes.get(msig);
		}

		List<Integer> indexes = new ArrayList<Integer>();
		if (msig.contains("<android.os.Bundle: void put")
		|| msig.contains("<android.os.BaseBundle: void put")
		|| msig.contains("<org.json.JSONObject: org.json.JSONObject put")
		
		|| msig.contains("<com.google.android.gms.analytics.Tracker: set")
		|| (msig.contains("<com.google.android.gms.analytics.HitBuilders") && (msig.contains(" build()")|| msig.contains(" set")))

		|| msig.contains("com.flurry.android.FlurryEvent.Params: put")
		|| msig.contains("<com.flurry.android.FlurryAgent: void addSessionProperty")
		|| msig.contains("<com.flurry.android.FlurryAgent: void addOrigin")
		
		|| msig.contains("<com.google.firebase.analytics.FirebaseAnalytics: void setUser")
		|| msig.contains("<com.google.firebase.analytics.FirebaseAnalytics: void setCurrentScreen")
		
		|| msig.contains("<com.facebook.appevents.AppEventsLogger: void setUser")	//setUserData, setUserID
		|| msig.contains("<com.facebook.appevents.AppEventsLogger: void setPushNotificationsRegistrationId")
		|| msig.contains("<com.facebook.appevents.AppEventsLogger: void updateUserProperties")
		
		|| msig.contains("<com.mixpanel.android.mpmetrics.MixpanelAPI: void registerSuperProperties")) {
			
			for (int i = 0; i < argsLen; i++) {
				String typeI = mthSig.getParameterType(i).toString();
				if (typeI.contains("java.lang.String") || typeI.contains("Bundle") 
				|| typeI.contains("Map") || typeI.contains("java.lang.Object") || typeI.contains("org.json.JSONObject"))
				indexes.add(i);
			}
			
		} else {
			List<Object> ts = rules.getJSONObject(msig).getJSONArray(RULE_TAINT_KEY).toList();
	
			for (int i = 0; i < argsLen; i++) {
				if (ts.contains(RULE_TAINT_ALLARGS) || ts.contains(RULE_TAINT_ARGS_PRE + i)) {
					indexes.add(i);
				}
			}
		}
		CACHEgetInterestedArgIndexes.put(msig, indexes);
		return indexes;

	}


	public List<Object> getDataSrc(String msig) {
		if (!rules.has(msig)) return null;
		if (rules.getJSONObject(msig).has(RULE_TAINT_IS_SYS_API_SRC))
			return rules.getJSONObject(msig).getJSONArray(RULE_TAINT_IS_SYS_API_SRC).toList();
		return null;
	}


}
