/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.possibilistic;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import ida.utils.VectorUtils;
import ida.utils.collections.MultiMap;
import ida.utils.tuples.Pair;
import supertweety.logic.ProgramSolver;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 19/01/15.
 */
public class PossibilisticLogic {

    private TreeSet<Double> weights = new TreeSet<Double>();

    private MultiMap<Double, Clause> rules = new MultiMap<Double, Clause>();

    private ProgramSolver ps = new ProgramSolver();

    public PossibilisticLogic(){}

    public PossibilisticLogic(MultiMap<Double, Clause> rules) {
        this.set(rules);
    }

    public PossibilisticLogic(List<Pair<Clause,Double>> rules){
        MultiMap<Double,Clause> mm = new MultiMap<Double,Clause>();
        for (Pair<Clause,Double> rule : rules){
            mm.put(rule.s, rule.r);
        }
        this.set(mm);
    }

    private void set(MultiMap<Double,Clause> rules){
        for (Map.Entry<Double, Set<Clause>> entry : rules.entrySet()) {
            for (Clause c : entry.getValue()) {
                rules.put(entry.getKey(), c);
            }
            weights.add(entry.getKey());
        }
    }

    public void add(Clause rule, double weight){
        this.rules.put(weight, rule);
        this.weights.add(weight);
    }

    public Pair<Set<Literal>,Double> solve(Collection<Literal> evidence){
        double[] levels = VectorUtils.toDoubleArray(this.rules.keySet());
        Arrays.sort(levels);
        int min = 0;
        int max = levels.length-1;
        Set<Literal> solution = null;
        double solutionLevel = Double.NaN;
        while (max >= min){
            int mid = (min+max)/2;
            Set<Literal> currentSolution = null;
            if ((currentSolution = this.solve(levels[mid], evidence)) != null){
                max = mid-1;
                solution = currentSolution;
                solutionLevel = levels[mid];
            } else {
                min = mid+1;
            }
        }
        if (solution == null){
            return null;
        } else {
            return new Pair<Set<Literal>,Double>(solution, solutionLevel);
        }
    }

    public Set<Literal> solve(double alpha, Collection<Literal> evidence){
        return ps.solve(this.getAlphaCut(alpha), Sugar.setFromCollections(evidence));
    }

    public List<Clause> getAlphaCut(double alpha){
        List<Clause> retVal = new ArrayList<Clause>();
        Double higher = new Double(alpha);
        while (higher != null) {
            retVal.addAll(rules.get(higher));
            higher = weights.higher(higher);
        }
        return retVal;
    }

    public List<Clause> getStrictAlphaCut(double alpha){
        List<Clause> retVal = new ArrayList<Clause>();
        Double higher = new Double(alpha);
        higher = weights.higher(higher);
        while (higher != null) {
            retVal.addAll(rules.get(higher));
            higher = weights.higher(higher);
        }
        return retVal;
    }

    public List<Clause> getAlphaLevel(double alpha){
        return Sugar.listFromCollections(this.rules.get(alpha));
    }

    public TreeSet<Double> levels(){
        return this.weights;
    }

    public String toString(){
        StringBuilder sb = new StringBuilder();
        for (double level : levels()){
            sb.append("---------------------\nLevel "+level+"\n");
            for (Clause clause : getAlphaLevel(level)) {
                sb.append(clause);
                sb.append("\n");
            }
        }
        return sb.toString();
    }

    public static void main(String[] args){
        Clause a = Clause.parse("!bird(X), flies(X)");
        Clause b = Clause.parse("antarctic(X), flies(X)");
        PossibilisticLogic pl = new PossibilisticLogic();
        pl.add(a, 0.5);
        pl.add(b, 0.75);
        System.out.println(pl.solve(Clause.parse("bird(tweety),!flies(tweety)").literals()));
    }

}
