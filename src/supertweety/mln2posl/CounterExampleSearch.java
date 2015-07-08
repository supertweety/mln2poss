/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.mln2posl;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.ilp.logic.Term;
import ida.ilp.logic.Variable;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import supertweety.mln.MarkovLogic;
import supertweety.possibilistic.PossibilisticLogic;

import java.math.BigInteger;
import java.util.*;

/**
 * Created by kuzelkao_cardiff on 24/02/15.
 */
public class CounterExampleSearch {

    private Random random;

    private Clause randomRule(int numPredicates, int maxLength){
        List<Literal> literals = new ArrayList<Literal>();
        Variable x = Variable.construct("X");
        for (int i = 0; i < maxLength; i++){
            literals.add(new Literal("p"+(random.nextInt(numPredicates)+1), random.nextBoolean(), x));
        }
        return new Clause(Sugar.funcall(literals,
                new Sugar.Fun<Literal,Literal>(){
                    private Map<String,Literal> predicates = new HashMap<String,Literal>();
                    @Override
                    public Literal apply(Literal literal) {
                        if (!predicates.containsKey(literal.predicate())){
                            predicates.put(literal.predicate(), literal);
                        }
                        return predicates.get(literal.predicate());
                    }
                }
        ));
    }

    private MarkovLogic randomMLN(int numPredicates, int maxRuleLength, int numRules){
        MarkovLogic mln = new MarkovLogic();
        mln.addHardRule(Clause.parse("o(x)"));
        for (int i = 0; i < numRules; i++){
            mln.addRule(randomRule(numPredicates, maxRuleLength), random.nextInt(10)+1);
        }
        return mln;
    }

    public void searchForCounterExamples(int numPredicates, int maxRuleLength, int numRules, int maxEvidenceLength){
        int round = 1;
        while (true){
            random = new Random(round);
            System.out.println("Starting round "+(round++));
            MarkovLogic randomMLN = randomMLN(numPredicates, maxRuleLength, numRules);
            for (Pair<Clause,BigInteger> rule : randomMLN.rules()){
                System.out.println(rule.s+" : "+rule.r);
            }
            ExhaustiveConvertor exhaustiveConvertor = new ExhaustiveConvertor(randomMLN, Sugar.<Term>set());
            exhaustiveConvertor.convert(Integer.MAX_VALUE);
            randomMLN.resetState();

            PossibilisticLogic pl = exhaustiveConvertor.possibilisticLogic();

            Set<Literal> randomEvidence = Sugar.funcall(randomRule(numPredicates, maxEvidenceLength).literals(),
                        new Sugar.Fun<Literal,Literal>(){
                            @Override
                            public Literal apply(Literal literal) {
                                return Literal.parseLiteral(literal.toString().toLowerCase());
                            }
                        }
                    );
            System.out.println(pl+"\n\n\n\n");

            randomMLN.resetEvidence();
            randomMLN.addEvidence(randomEvidence);
            randomMLN.runMAPInference(10000);
            Set<Literal> state = randomMLN.completeState();
            Pair<Set<Literal>,Double> solution0 = pl.solve(randomEvidence);
            System.out.println("SOLUTION FOR EVIDENCE: "+solution0);
            Pair<Set<Literal>,Double> solution = pl.solve(state);
            System.out.println("SOLUTION FOR MAP STATE: "+solution);
            System.out.println("state: "+state+" "+randomMLN.state());
            System.out.println("Evidence: "+randomEvidence);

            if (solution0 != null && (double)solution0.s != (double)solution.s){
                throw new RuntimeException();
            }

        }
    }

    public static void main(String[] args){
        new CounterExampleSearch().searchForCounterExamples(4, 4, 3, 2);
        //new CounterExampleSearch().searchForCounterExamples(3, 4, 3, 4);
        //new CounterExampleSearch().searchForCounterExamples(2, 4, 3, 4);
    }

}
