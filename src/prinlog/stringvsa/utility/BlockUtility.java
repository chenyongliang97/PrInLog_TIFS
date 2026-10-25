package prinlog.stringvsa.utility;

import java.util.Iterator;

import soot.Unit;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.CompleteBlockGraph;

public class BlockUtility {

	public static Block findLocatedBlock(CompleteBlockGraph cbg, Unit unit) {
		// TODO Auto-generated method stub

		for (Block block : cbg.getBlocks()) {
			Iterator<Unit> us = block.iterator();
			while (us.hasNext()) {
				if (us.next() == unit) {
					return block;
				}
			}
		}
		return null;

	}

	public static boolean isEqualBlock(Block b1, Block b2) {
		return b1.toString().equals(b2.toString()) && b1.getIndexInMethod() == b2.getIndexInMethod();
	}

}
