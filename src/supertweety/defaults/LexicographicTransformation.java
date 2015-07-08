/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.defaults;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Constant;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import supertweety.misc.Utils;
import supertweety.mln.MarkovLogic;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Predicate;

/**
 * Created by ondrejkuzelka on 18/04/15.
 */
public class LexicographicTransformation {

    private Set<Literal> deterministic = new HashSet<Literal>();

    private PossibilisticZRanker zranker;

    public MarkovLogic transform(Collection<DefaultRule> defaultRules, Collection<Clause> hardRules, List<Set<Constant>> universe){
        if (this.zranker != null){
            throw new IllegalStateException("Each instance of the class LexicographicTransformation can be used only once.");
        }
        this.zranker = new PossibilisticZRanker();
        Pair<List<Set<DefaultRule>>,Set<Clause>> zranking = zranker.zrank(defaultRules, hardRules, universe, deterministic);


        int universeCardinality = 0;
        for (Set<Constant> set : zranker.interchangeable()){
            universeCardinality += set.size();
        }

        List<Pair<Clause,BigInteger>> mlnRules = new ArrayList<Pair<Clause, BigInteger>>();

        BigInteger currentWeight = BigInteger.ONE;
        for (Set<DefaultRule> level : zranking.r){
            BigInteger weightIncrement = BigInteger.ZERO;
            for (DefaultRule defaultRule : level) {
                Clause defaultRuleAsClause = new Clause(Sugar.iterable(Utils.flipSigns(defaultRule.body()).literals(), defaultRule.head().literals()));
                mlnRules.add(new Pair<Clause, BigInteger>(
                        defaultRuleAsClause,
                        currentWeight));
                weightIncrement = weightIncrement.add(currentWeight.multiply(
                        BigInteger.valueOf(universeCardinality).pow(defaultRuleAsClause.variables().size())));
            }
            currentWeight = currentWeight.add(weightIncrement);

        }
        return buildMLN(mlnRules, hardRules);
    }

    private MarkovLogic buildMLN(List<Pair<Clause,BigInteger>> rules, Collection<Clause> hardRules) {
        MarkovLogic mln = new MarkovLogic();
        for (Pair<Clause,BigInteger> rule : rules){
                mln.addRule(rule.r, rule.s);
        }
        for (Clause hardRule : hardRules) {
            mln.addHardRule(hardRule);
        }
        for (Literal deterministic : this.makeTyping(this.deterministic)){
            mln.addDeterministicLiteral(deterministic);

        }
        return mln;
    }

    public void addDeterministicCWLiteral(Literal literal){
        this.deterministic.add(literal);
    }

    public Set<Literal> makeTyping(Collection<Literal> literals){
        return zranker.makeTyping(literals);
    }

    public static void main(String[] args){
        DefaultRule a = new DefaultRule(Clause.parse("@neq(X,tweety), bird(X)"), Clause.parse("flies(X)"));
        DefaultRule b = new DefaultRule(Clause.parse("heavy(X), bird(X)"), Clause.parse("!flies(X)"));
        DefaultRule c = new DefaultRule(Clause.parse("bird(X), heavy(X), hasAirplane(X)"), Clause.parse("flies(X)"));
        DefaultRule d = new DefaultRule(Clause.parse("heavy(X), sameSpecies(X,Y)"), Clause.parse("heavy(Y)"));
        DefaultRule e = new DefaultRule(Clause.parse("bird(X), sameSpecies(X,Y)"), Clause.parse("bird(Y)"));

        Clause transitivity = Clause.parse("!sameSpecies(X,Y), !sameSpecies(Y,Z), sameSpecies(X,Z)");
        Clause symmetry = Clause.parse("!sameSpecies(X,Y), sameSpecies(Y,X)");

        LexicographicTransformation lt = new LexicographicTransformation();

        MarkovLogic mln = lt.transform(Sugar.list(a, b, c, d, e), Sugar.<Clause>list(transitivity, symmetry),
                Sugar.list(Sugar.set(Constant.construct("tweety"), Constant.construct("donald"), Constant.construct("scrooge"),
                        Constant.construct("huey"), Constant.construct("dewey"), Constant.construct("louie"),
                        Constant.construct("eagle")
                ))
        );
        for (Pair<Clause,BigInteger> rule : mln.rules()) {
            System.out.println(rule.s+" "+rule.r);
        }
        mln.addEvidence(lt.makeTyping(Clause.parse(
                "sameSpecies(donald, scrooge), sameSpecies(donald, huey), sameSpecies(donald, dewey), sameSpecies(donald, louie)," +
                "bird(donald), hasAirplane(donald), bird(tweety), heavy(tweety), " +
                "heavy(donald), bird(eagle)").literals()));
        mln.setMAPTimeout(Integer.MAX_VALUE);
        mln.runMAPInference(100);
        List<Literal> filteredState = Sugar.listFromCollections(mln.state());
        filteredState.<Literal>removeIf(new Predicate<Literal>() {
            @Override
            public boolean test(Literal literal) {
                return literal.predicate().equals("sameSpecies");
            }
        });
        System.out.println("MAP: "+filteredState);
    }

}
