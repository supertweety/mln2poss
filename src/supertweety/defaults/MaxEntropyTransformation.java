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

import ida.ilp.logic.*;
import ida.utils.Sugar;
import ida.utils.collections.MultiMap;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;
import supertweety.logic.ProgramSolver;
import supertweety.mln.MarkovLogic;

import java.math.BigInteger;
import java.util.*;
import java.util.function.Predicate;

/**
 * Created by kuzelkao_cardiff on 02/04/15.
 */
public class MaxEntropyTransformation {

    private Set<Literal> deterministic = new HashSet<Literal>();

    private List<Set<Constant>> interchangeable;

    public MarkovLogic transform(Collection<DefaultRule> rules, Collection<Clause> hardRules, List<Set<Constant>> universe) {
        if (interchangeable != null) {
            throw new IllegalStateException("The method maxEntropyTransformation(...) can be used only once per an object.");
        }

        rules = Sugar.<DefaultRule>setFromCollections(rules);
        this.interchangeable = DefaultTransformationUtils.partitionInterchangeableConstants(rules, hardRules);

//        Set<Constant> universeAsSet = Sugar.setFromCollections(universe);
//        for (DefaultRule rule : rules) {
//            universeAsSet.removeAll(rule.head().terms());
//            universeAsSet.removeAll(rule.body().terms());
//        }
//        for (Clause hardRule : hardRules) {
//            universeAsSet.removeAll(hardRule.terms());
//        }
//        this.interchangeable.add(universeAsSet);

        List<Set<Constant>> universeAsSets = Sugar.<Set<Constant>,Set<Constant>>funcall(universe, new Sugar.Fun<Set<Constant>,Set<Constant>>(){
            @Override
            public Set<Constant> apply(Set<Constant> constants) {
                return Sugar.setFromCollections(constants);
            }
        });
        for (DefaultRule rule : rules){
            for (Set<Constant> set : universeAsSets) {
                set.removeAll(rule.head().terms());
                set.removeAll(rule.body().terms());
            }
        }
        for (Clause hardRule : hardRules){
            for (Set<Constant> set : universeAsSets) {
                set.removeAll(hardRule.terms());
            }
        }
        this.interchangeable.addAll(universeAsSets);

        Triple<Set<DefaultRule>, Set<Clause>, List<Set<Constant>>> preprocessed = DefaultTransformationUtils.preprocessConstants(rules, hardRules, this.interchangeable);
        rules = preprocessed.r;
        hardRules = preprocessed.s;
        this.interchangeable = preprocessed.t;

        MultiMap<BigInteger, DefaultRule> weightedRules = new MultiMap<BigInteger, DefaultRule>();
        while (!rules.isEmpty()) {
            System.out.println(rules.size());
            List<Clause> clauses = DefaultTransformationUtils.clausesFromDefaults(rules);
            Set<DefaultRule> deltai = new HashSet<DefaultRule>();
            BigInteger min = null;
            MultiMap<BigInteger, DefaultRule> scores = new MultiMap<BigInteger, DefaultRule>();

            MultiMap<DefaultRule, DefaultRule> originalsToSpecializations = new MultiMap<DefaultRule, DefaultRule>();
            HashMap<DefaultRule, DefaultRule> specializationsToOriginals = new HashMap<DefaultRule, DefaultRule>();
            Set<DefaultRule> impossible = new HashSet<DefaultRule>();
            boolean atLeastOneBodyPossible = false;

            for (DefaultRule rule : Sugar.<DefaultRule>listFromCollections(rules)) {
                MultiMap<DefaultRule, DefaultRule> specializations = DefaultTransformationUtils.representativeBodySpecializations(rule, this.interchangeable);
                // first, we try to add the default rule as it is (otherwise, we have to add its specializations separately)

                for (DefaultRule key : specializations.keySet()) {
                    specializationsLoop:
                    for (DefaultRule specialization : specializations.get(key)) {
                        DefaultRule groundedRepresentative = DefaultTransformationUtils.representativeSubstitution(specialization, this.interchangeable);
                        if (new ProgramSolver().solve(hardRules, groundedRepresentative.body().literals(), this.makeTyping(deterministic)) != null) {
                            atLeastOneBodyPossible = true;
                            originalsToSpecializations.put(rule, specialization);
                            specializationsToOriginals.put(specialization, rule);
                            MarkovLogic mln = buildMLN(weightedRules, hardRules);


                            for (Clause hard : DefaultTransformationUtils.clausesFromDefaults(rules)) {
                                mln.addHardRule(hard);
                            }
                            mln.addEvidence(groundedRepresentative.body().literals());
                            //mln.addEvidence(groundedRepresentative.head().literals());

                            if (mln.isConsistent()) {
                                mln.runMAPInference(Integer.MAX_VALUE);
                                BigInteger penalty = mln.penalty();
                                if (min == null) {
                                    min = penalty;
                                } else if (min.compareTo(penalty) > 0) {
                                    min = penalty;
                                }
                                scores.put(penalty, specialization);
                            } else {
                                //System.out.println("Inconsistent");
                                continue specializationsLoop;
                            }
                        } else {
                            impossible.add(specialization);
                        }
                    }
                }
            }
            if (min == null){
                if (atLeastOneBodyPossible) {
                    //System.out.println("Impossible: ");
                    for (DefaultRule r : rules){
                        System.out.println("\t"+r);
                    }
                    return null;
                } else {
                    break;
                }
            }

            Set<DefaultRule> minLevel = Sugar.setFromCollections(scores.get(min));
            //whole rules first
            middleLoop:
            for (DefaultRule rule : Sugar.listFromCollections(rules)) {
                for (DefaultRule specialization : originalsToSpecializations.get(rule)) {
                    if (!minLevel.contains(specialization) && !impossible.contains(specialization)) {
                        continue middleLoop;
                    }
                }
                weightedRules.put(min.add(BigInteger.ONE), rule);
                for (DefaultRule specialization : originalsToSpecializations.get(rule)) {
                    minLevel.remove(specialization);
                }
                rules.remove(rule);
            }

            //and then specializations not covered by the previous
            Set<DefaultRule> originals = new HashSet<DefaultRule>();
            for (DefaultRule rule : minLevel) {
                weightedRules.put(min.add(BigInteger.ONE), rule);
                originals.add(specializationsToOriginals.get(rule));
            }
            for (DefaultRule original : originals) {
                rules.remove(original);
                for (DefaultRule specializationNotInMinLevel : Sugar.setDifference(originalsToSpecializations.get(original), Sugar.union(minLevel, impossible))) {
                    rules.add(specializationNotInMinLevel);
                }
            }
        }
        Set<Clause> extendedHardRules = new HashSet<Clause>();
        extendedHardRules.addAll(hardRules);
        for (Constant c : Sugar.iterable(this.interchangeable)) {
            extendedHardRules.add(new Clause(new Literal("type", c)));
        }
        return buildMLN(weightedRules, hardRules);
    }

    private MarkovLogic buildMLN(MultiMap<BigInteger, DefaultRule> rules, Collection<Clause> hardRules) {
        MarkovLogic mln = new MarkovLogic();
        for (Map.Entry<BigInteger, Set<DefaultRule>> entry : rules.entrySet()) {
            for (DefaultRule rule : entry.getValue()) {
                mln.addRule(DefaultTransformationUtils.clauseFromDefault(rule), entry.getKey());
            }
        }
        for (Clause hardRule : hardRules) {
            mln.addHardRule(hardRule);
        }
        for (Literal deterministic : this.makeTyping(this.deterministic)){
            mln.addDeterministicLiteral(deterministic);
        }
        return mln;
    }

    public Set<Literal> makeTyping(Collection<Literal> literals) {
        final Map<Term, Term> typedConstants = new HashMap<Term, Term>();
        for (Set<Constant> set : this.interchangeable) {
            String type = DefaultTransformationUtils.min(set).name();
            Set<Constant> newSet = new HashSet<Constant>();
            for (Constant c : set) {
                Constant typedConstant = Constant.construct(c.name(), type);
                typedConstants.put(Constant.construct(c.name()), typedConstant);
                newSet.add(typedConstant);
            }
        }
        Collection<Literal> retLiterals = Sugar.funcall(literals, new Sugar.Fun<Literal, Literal>() {
            @Override
            public Literal apply(Literal literal) {
                return LogicUtils.substitute(literal, typedConstants);
            }
        });
        return Sugar.setFromCollections(retLiterals);
    }

    public void addDeterministicCWLiteral(Literal literal){
        this.deterministic.add(literal);
    }

    public static void main(String[] args) {
        DefaultRule a = new DefaultRule(Clause.parse("@neq(X,tweety), bird(X)"), Clause.parse("flies(X)"));
        DefaultRule b = new DefaultRule(Clause.parse("heavy(X), bird(X)"), Clause.parse("!flies(X)"));
        DefaultRule c = new DefaultRule(Clause.parse("bird(X), heavy(X), hasAirplane(X)"), Clause.parse("flies(X)"));
        DefaultRule d = new DefaultRule(Clause.parse("heavy(X), sameSpecies(X,Y)"), Clause.parse("heavy(Y)"));
        DefaultRule e = new DefaultRule(Clause.parse("bird(X), sameSpecies(X,Y)"), Clause.parse("bird(Y)"));


        Clause transitivity = Clause.parse("!sameSpecies(X,Y), !sameSpecies(Y,Z), sameSpecies(X,Z)");
        Clause symmetry = Clause.parse("!sameSpecies(X,Y), sameSpecies(Y,X)");

        MaxEntropyTransformation lt = new MaxEntropyTransformation();

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
