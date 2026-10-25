package prinlog.taintanalysis.utility;

public class Logger {
	public static String TAG = "Logger ";
	public static boolean showMsg = false;

	public static void printI(String args) {
		if (showMsg) println(TAG + args);
	}

	public static void printW(String args) {
		String str = TAG + "[W]" + args;
		if (showMsg) println(str);
		// FileUtility.wf("./logs/warnning.txt", str, true);
	}

	public static void print(Object args) {
		if (showMsg) println(TAG + args);
	}

	public static void printE(String args) {
		args = TAG + args;
		// FileUtility.wf("./logs/error.txt", args, true);
		if (showMsg) println(args);
	}

	private static void println(Object obj) {
		if (showMsg) System.out.println(obj);
	}

}
