/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.logic;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import ida.utils.collections.ValueToIndex;
import ida.utils.tuples.Pair;
import org.sat4j.core.VecInt;
import org.sat4j.maxsat.WeightedMaxSatDecorator;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;

import java.math.BigInteger;
import java.util.*;

/**
 * Created by kuzelkao_cardiff on 04/02/15.
 */
public class GroundProgramSolver {

    private List<Pair<Clause,BigInteger>> softProgram = new ArrayList<Pair<Clause,BigInteger>>();

    private List<Clause> hardProgram = new ArrayList<Clause>();

    private List<int[]> hardDimacsClauses;

    private List<Pair<int[],BigInteger>> softDimacsClauses;

    private ValueToIndex<Literal> literalsToIndices = new ValueToIndex<Literal>(1);

    private int optimizationTimeout = Integer.MAX_VALUE;

    public GroundProgramSolver(Collection<Clause> hardProgram){
        for (Clause c : hardProgram){
            this.hardProgram.add(c);
        }
        this.hardDimacsClauses = this.toHardDimacsClauses(this.hardProgram);
    }

    public GroundProgramSolver(Collection<Clause> hardProgram, Collection<Pair<Clause,BigInteger>> softProgram){
        for (Pair<Clause,BigInteger> c : softProgram){
            for (Literal literal : c.r.literals()){
                literalsToIndices.valueToIndex(literal);
            }
            if (c.s == null) {
                this.hardProgram.add(c.r);
            } else  {
                this.softProgram.add(new Pair<Clause, BigInteger>(c.r, c.s));
            }
        }
        this.softDimacsClauses = this.toSoftDimacsClauses(this.softProgram);
        for (Clause c : hardProgram){
            for (Literal literal : c.literals()){
                literalsToIndices.valueToIndex(literal);
            }
            this.hardProgram.add(c);
        }
        this.hardDimacsClauses = this.toHardDimacsClauses(this.hardProgram);
    }

    public Set<Literal> solve(){
        try {
            ISolver solver = SolverFactory.newDefault();
            solver.newVar(this.literalsToIndices.size());
            solver.setExpectedNumberOfClauses(softProgram.size());
            for (int[] clause : hardDimacsClauses){
                //System.out.println("hard dimacs clause: "+VectorUtils.intArrayToString(clause));
                try {
                    solver.addClause(new VecInt(clause));
                } catch (ContradictionException ce){
                    //no solution
                    return null;
                }
            }
            IProblem problem = solver;
            if (problem.isSatisfiable()) {
                int[] model = problem.model();
                Set<Literal> solution = new HashSet<Literal>();
                for (int i : model){
                    if (i > 0){
                        solution.add(literalsToIndices.indexToValue(i));
                    }
                }
                return solution;
            } else {
                return null;
            }
        } catch (Exception e){
            e.printStackTrace();
        }
        return null;
    }

    public Set<Literal> optimize(){
        try {
            WeightedMaxSatDecorator solver = new WeightedMaxSatDecorator(org.sat4j.pb.SolverFactory.newDefaultOptimizer());
            solver.newVar(this.literalsToIndices.size());
            solver.setExpectedNumberOfClauses(softProgram.size()+hardProgram.size());
            //solver.setTopWeight(BigInteger.valueOf(Integer.MAX_VALUE));
            solver.setTimeoutMs(optimizationTimeout);
            if (this.hardDimacsClauses != null) {
                for (int[] clause : hardDimacsClauses) {
                    solver.addHardClause(new VecInt(clause));
                }
            }

            if (this.softDimacsClauses != null) {
                for (Pair<int[], BigInteger> clause : this.softDimacsClauses) {
                    solver.addSoftClause(clause.s, new VecInt(clause.r));
                }
            }
            if (solver.isSatisfiable()) {
                int[] model = solver.model();
                Set<Literal> solution = new HashSet<Literal>();
                model = solver.model();

                for (int i : model) {
                    if (i > 0) {
                        solution.add(literalsToIndices.indexToValue(i));
                    }
                }
                return solution;
            }
        } catch (Exception e){
            return null;
        }
        return null;
    }

    private List<Pair<int[],BigInteger>> toSoftDimacsClauses(Collection<Pair<Clause, BigInteger>> program){
        List<Pair<int[],BigInteger>> retVal = new ArrayList<Pair<int[],BigInteger>>();
        for (Pair<Clause,BigInteger> c : program) {
            int[] clause = new int[c.r.literals().size()];
            int i = 0;
            for (Literal l : c.r.literals()){
                if (l.isNegated()){
                    clause[i] = -literalsToIndices.valueToIndex(l.negation());
                } else {
                    clause[i] = literalsToIndices.valueToIndex(l);
                }
                i++;
            }

            retVal.add(new Pair<int[],BigInteger>(clause,c.s));
        }
        return retVal;
    }

    private List<int[]> toHardDimacsClauses(List<Clause> program){
        List<int[]> retVal = new ArrayList<int[]>();
        for (Clause c : program) {
            int[] clause = new int[c.literals().size()];
            int i = 0;
            for (Literal l : c.literals()){
                if (l.isNegated()){
                    clause[i] = -literalsToIndices.valueToIndex(l.negation());
                } else {
                    clause[i] = literalsToIndices.valueToIndex(l);
                }
                i++;
            }
            retVal.add(clause);
        }
        return retVal;
    }

    public static void main(String[] args) {
        Clause c1 = Clause.parse("!smokes(alice),!friends(alice,bob),smokes(bob)");
        Clause c2 = Clause.parse("smokes(alice)");
        Clause c3 = Clause.parse("friends(alice,bob)");
        Clause c4 = Clause.parse("!smokes(bob)");
        GroundProgramSolver gps = new GroundProgramSolver(Sugar.<Clause>list(c2, c4), Sugar.list(
                new Pair<Clause, BigInteger>(c1, BigInteger.ONE), new Pair<Clause, BigInteger>(c3, BigInteger.ONE)
        ));
        System.out.println(gps.optimize());
    }

    public void setOptimizationTimeout(int optimizationTimeout) {
        this.optimizationTimeout = optimizationTimeout;
    }
}
