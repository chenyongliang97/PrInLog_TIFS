package prinlog.stringvsa.backwardslicing;

import java.util.List;

public interface IBCollecter {
    public void clear();

	public void put(BacktracingContext bc);

	public List<BacktracingContext> retrieve();
}
