package prinlog.stringvsa.base;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.concurrent.locks.Condition;

import org.json.JSONArray;
import org.json.JSONObject;

import prinlog.main.runTest;
import prinlog.stringvsa.backwardslicing.BacktracingContext;
import prinlog.stringvsa.backwardslicing.BackwardController;
import prinlog.stringvsa.graph.ConditionBlock;
import prinlog.stringvsa.graph.DGraph;
import prinlog.stringvsa.graph.HeapObject;
import prinlog.stringvsa.graph.ValuePoint;
import prinlog.stringvsa.utility.Logger;
import prinlog.taintanalysis.base.TaintQuestion;
import prinlog.taintanalysis.main.QuestionGenerator;
import prinlog.taintanalysis.solver.TaintQuestionSolver;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.toolkits.graph.Block;

public class BackTraceQuestion {
    ValuePoint starPoint;
    ArrayList<BacktracingContext> bcs;


    HashMap<String, HashSet<Boolean>> satisfyCons = new HashMap<>();
    HashSet<String> criticalCons = new HashSet<>();
    HashSet<String> criticalBlocks = new HashSet<>();
    HashMap<String, HashSet<String>> block2AffectedCons = new HashMap<>();
    HashMap<String, HashSet<String>> blocksInRing = new HashMap<>();
    HashSet<String> twoBranchCons = new HashSet<>();

    HashSet<String> processedCons = new HashSet<>();


    

    public BackTraceQuestion(ValuePoint sp) {
        this.starPoint = sp;
        this.bcs = new ArrayList<BacktracingContext>();
    }


    public void solve() {
        boolean solvedAll = false;
        
        bcs.add(new BacktracingContext(starPoint, starPoint.getDg()));

        while (!solvedAll && !runTest.timeout) {
            
            BackwardController.getInstance().doBackTracing(bcs);

            Logger.print(" Finish building bcs, BC size: " + bcs.size());

            findCriticalCons();

            Logger.print(" Finish finding critical cons ...");
            
            ArrayList<Integer> toDeleteIdx = filterCriticalCons();
            
            for (int i : toDeleteIdx)
                bcs.remove(i);
            
            Logger.print(" Finish filtering bcs, new BC size: " + bcs.size() + " /// New Crit2ical Con size: " + criticalCons.size());

            // System.out.print(runTest.newAddedKeys);

            
            
            Logger.print(" Ready to solve Found HOs");

            solveAllFoundHOs();


            Logger.print(" Finish solving Found HOs");
            solvedAll = true;
            for (BacktracingContext bc : bcs) 
                if (!bc.backWardHasFinished()) {
                    solvedAll = false;
                    break;
                }

            if (bcs.size() >= runTest.maxBCs) {
                runTest.reachMaxBCs = true;
                Logger.print(" Has reached maximum BCs in this question...");
            }
        }
        
    }

    public void forwardSearchKeyUsage(HashSet<String> newKeys) {
        QuestionGenerator qg = new QuestionGenerator();
        ArrayList<TaintQuestion> tqs = qg.findKeyUsages(newKeys);

        while (!runTest.timeout) {
            TaintQuestion target = null;
            for (TaintQuestion tq : tqs) {
                if (!tq.hasSolved()) {
                    target = tq;
                    break;
                }
            }

            if (target == null) break;

            TaintQuestionSolver.solveOneTq(target);
        }
    }

    public ArrayList<Integer> filterCriticalCons() {
        // ArrayList<ConditionBlock> cc = (ArrayList<ConditionBlock>)bc.getConditionChain().clone();
        
        ArrayList<Integer> toDeleteIdx = new ArrayList<>();
        HashSet<String> foundTraces = new HashSet<>();



        for (int i = bcs.size() - 1; i >= 0; i--) {
            BacktracingContext bc = bcs.get(i);
            ArrayList<ConditionBlock> cc = bc.getConditionChain();
            
            int idx = cc.size() - 1;
            
            String sig = "";
            while (idx >= 0) {
                ConditionBlock cb = cc.get(idx);
                if (!criticalCons.contains(cb.TAG) || cb.hasSolvedDeterminent() && cb.isIF) {
                } else sig = sig.concat(cb.TAG).concat(Boolean.toString(cb.isSatisfyCondition()));
                idx--;
            }

            if (foundTraces.contains(sig)) toDeleteIdx.add(i);
            else foundTraces.add(sig);

        }
        
        return toDeleteIdx;
    }

    public void removeNonCriticalCBs() {
        for (BacktracingContext bc : bcs) {
            ArrayList<ConditionBlock> cc = bc.getConditionChain();
            
            int idx = cc.size() - 1;
            
            while (idx >= 0) {
                ConditionBlock cb = cc.get(idx);
                if (!criticalCons.contains(cb.TAG) || cb.hasSolvedDeterminent() && cb.isIF) cc.remove(idx);
                idx--;
            }
        }

    }

    @SuppressWarnings("unchecked")
    public void findCriticalCons() {
        
        satisfyCons = new HashMap<>();
        criticalCons = new HashSet<>();
        criticalBlocks = new HashSet<>();
        block2AffectedCons = new HashMap<>();
        blocksInRing = new HashMap<>();
        twoBranchCons = new HashSet<>();


        for (BacktracingContext bc : bcs) {

            criticalBlocks.addAll(bc.getDataCriticalBlocks());

            for (ConditionBlock cb : bc.getConditionChain()) {
    
                // if (!newCBs.contains(cb.TAG)) continue;

                if (!satisfyCons.containsKey(cb.TAG)) {
                    satisfyCons.put(cb.TAG, new HashSet<>());
                }
        
                satisfyCons.get(cb.TAG).add(cb.isSatisfyCondition());
            }

            bc.getBlock2AffectedCons().forEach((b, cons) -> {
                if (!block2AffectedCons.containsKey(b)) block2AffectedCons.put(b, new HashSet());
                block2AffectedCons.get(b).addAll((HashSet<String>) cons.clone());
            });

        }


        for (String c : satisfyCons.keySet()) {
            // if (!newCBs.contains(c)) continue;

            if (satisfyCons.get(c).size() < 2) {
                criticalCons.add(c); // one branch

                // Logger.print("Critical Con: " + c);

                // add all affected blocks critical
                block2AffectedCons.forEach((b, cons) -> {
                    if (cons.contains(c)) criticalBlocks.add(b);
                });
            } else twoBranchCons.add(c);

        }

        
        // Check all conditions with both branches reaching to target
        // Check whether blocks in loops can affect the critical conditions


        ArrayList<ArrayList<String>> interestedTraces = new ArrayList<>();

        for (BacktracingContext bc : bcs) { 
        // for (BacktracingContext bc : interestedBCs) { 
            HashSet<String> ss = new HashSet<>(bc.getBlockTags());
            ss.retainAll(twoBranchCons);
            // ss.retainAll(newCBs);
            if (ss.size() > 0) interestedTraces.add(bc.getBlockTags());
        }

        for (int i = 0; i < interestedTraces.size() - 1; i ++)
            for (int j = i + 1; j < interestedTraces.size(); j ++) {
                getBlocksInIfRing(interestedTraces.get(i), interestedTraces.get(j));
            }


        boolean updated = true;

        // Logger.print("====== Critical cons pre: " + getCriticalCons());
        // Logger.print(" blocks In Ring: " + blocksInRing.toString());
        while (updated) {
            updated = false;
            
            for (String con : twoBranchCons) {
                if (criticalCons.contains(con)) continue;
                HashSet<String> blocks = new HashSet<String>();
                if (blocksInRing.containsKey(con))
                    blocks.addAll((HashSet<String>)blocksInRing.get(con).clone());
                blocks.retainAll(criticalBlocks);
                if (blocks.size() > 0) {
                    updated = true;
                    criticalCons.add(con);
                    criticalBlocks.addAll(blocks);
                    break;
                }
            }
        }


        // Logger.print("====== Critical cons after: " + getCriticalCons());
    }

    public void getBlocksInIfRing(ArrayList<String> trace1, ArrayList<String> trace2) {
        

        ArrayList<String> overlappedBlocks = new ArrayList<>();
        
        int i = trace1.size() - 1; 
        int j = trace2.size() - 1;
        int last_j = j; // the first position that i <> j

        while (i >= 0 && j >= 0) {
            if (trace1.get(i).equals(trace2.get(j))) {
                overlappedBlocks.add(0, trace1.get(i));
                i -= 1;
                j -= 1;
                last_j = j;
                
            } else if (j > 0) {
                j -= 1;
            } else {
                i -= 1;
                j = last_j;
            }

            // i = i >= 0 ? i : 0;
            // j = j >= 0 ? j : 0;
        }


        String currentBlockTag = overlappedBlocks.get(0);
        String pastBlockTag = currentBlockTag;
        boolean inIfLoop = false;
        
        overlappedBlocks.remove(0);

        while (overlappedBlocks.size() > 0) {
            inIfLoop = twoBranchCons.contains(pastBlockTag);
            currentBlockTag = overlappedBlocks.get(0);
            overlappedBlocks.remove(0);
            if (!inIfLoop) {
                pastBlockTag = currentBlockTag;
                continue;
            }

            i = trace1.indexOf(pastBlockTag) + 1;
            j = trace2.indexOf(pastBlockTag) + 1;

            if (!blocksInRing.containsKey(pastBlockTag)) blocksInRing.put(pastBlockTag, new HashSet<>());


            while (i < trace1.size() && !trace1.get(i).equals(currentBlockTag)) {
                
                blocksInRing.get(pastBlockTag).add(trace1.get(i));
                i ++;
            }

            while (j < trace2.size() && !trace2.get(j).equals(currentBlockTag)) {
                
                blocksInRing.get(pastBlockTag).add(trace2.get(j));
                j ++;
            }

            pastBlockTag = currentBlockTag;
        }
    
    }

    public void saveResult() {
        removeNonCriticalCBs();

        for (BacktracingContext bc : bcs){
            // if (!bc.backWardHasFinished()) continue;
            if (!runTest.condition_res.containsKey(bc.getStartPoint())) runTest.condition_res.put(bc.getStartPoint(), new ArrayList<>());
            runTest.condition_res.get(bc.getStartPoint()).add(bc);
        }
    }

    public boolean isCriticalCon(String s) {
        return criticalCons.contains(s);
    }

    public void printResults() {
        for (BacktracingContext bc : bcs) {
            Logger.print("====================");
            // bc.printExceTrace();
            Logger.print(" Condition chain size: " + bc.getConditionChain().size());
            for (ConditionBlock cb : bc.getConditionChain()) {
                Logger.print("------------" + cb.getStartPoint().getMethod_location().toString() + " : " + cb.getStartPoint().getInstruction_location().toString());
                Logger.print("-----Satisfy: " + cb.isSatisfyCondition());
                cb.printExecTrace();
                // Logger.print(" " + cb.getAffectedCons().toString());
            }

            Logger.print(" Method Invoke Chain: ");

            for (SootMethod smthd : bc.getExtendedMthd())
                Logger.print(" " + smthd.toString());
            
        }
    }

    public HashSet<String> getCriticalCons() {
        return this.criticalCons;
    }


    public void solveAllFoundHOs() {
        
        HashSet<ValuePoint> newVPs = new HashSet<>();

        while (!runTest.timeout) {
            ValuePoint tmpVP = null;
            
            for (ValuePoint vp : newVPs) {
                if (!vp.inited()) {
                    tmpVP = vp;
                }
            }

            if (tmpVP == null) {
                newVPs = new HashSet<>();

                if (runTest.newAddedKeys.size() > 0) forwardSearchKeyUsage(runTest.newAddedKeys);
                runTest.processedKeys.addAll(runTest.newAddedKeys);
                runTest.newAddedKeys.clear();


                for (String name : HeapObject.hos.keySet()) {
                    HeapObject node = HeapObject.hos.get(name);
                    // System.out.println("Added new HO: " + name);
                    if (!node.inited()) {
                        node.initIfHavenot();
                        newVPs.addAll(new HashSet<>(node.getVPs()));
                    }
                }
                if (newVPs.size() == 0) break;
            } else tmpVP.initIfHavenot();

            
        }
    }

    public ValuePoint getStartPoint() {
        return this.starPoint;
    }

}
