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

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 02/04/15.
 */
public class PossibilisticZRanker {

    private List<Set<Constant>> interchangeable;

    public Pair<List<Set<DefaultRule>>,Set<Clause>> zrank(Collection<DefaultRule> rules, Collection<Clause> hardRules, List<Set<Constant>> universe, Set<Literal> deterministic){
        if (interchangeable != null){
            throw new IllegalStateException("The method zrank(...) can be used only once per an object.");
        }

        rules = Sugar.<DefaultRule>setFromCollections(rules);
        this.interchangeable = DefaultTransformationUtils.partitionInterchangeableConstants(rules, hardRules);

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

        Triple<Set<DefaultRule>,Set<Clause>,List<Set<Constant>>> preprocessed = DefaultTransformationUtils.preprocessConstants(rules, hardRules, this.interchangeable);
        rules = preprocessed.r;
        hardRules = preprocessed.s;
        this.interchangeable = preprocessed.t;

        List<Set<DefaultRule>> retVal = new ArrayList<Set<DefaultRule>>();
        while (!rules.isEmpty()) {
            System.out.println("Num rules to process: "+rules.size());
            List<Clause> clauses = DefaultTransformationUtils.clausesFromDefaults(rules);
            Set<DefaultRule> deltai = new HashSet<DefaultRule>();
            boolean atLeastOneBodyPossible = false;

            for (DefaultRule rule : Sugar.<DefaultRule>listFromCollections(rules)) {
                System.out.println("Building body specializations.");
                MultiMap<DefaultRule, DefaultRule> specializations = DefaultTransformationUtils.representativeBodySpecializations(rule, this.interchangeable);
                System.out.println(specializations.size()+" body specializations built.");
                // first, we try to add the default rule as it is (otherwise, we have to add its specializations separately)
                boolean allSpecializationsTolerated = true;
                for (DefaultRule key : specializations.keySet()) {
                    for (DefaultRule specialization : specializations.get(key)) {
                        DefaultRule groundedRepresentative = DefaultTransformationUtils.representativeSubstitution(specialization, this.interchangeable);
                        if (new ProgramSolver().solve(hardRules, groundedRepresentative.body().literals(), this.makeTyping(deterministic)) != null) {
                            atLeastOneBodyPossible = true;
                            if (new ProgramSolver().solve(Sugar.union(clauses, hardRules), groundedRepresentative.body().literals(), this.makeTyping(deterministic)) == null) {
                                allSpecializationsTolerated = false;
                                break;
                            }
                        }
                    }
                }
                if (allSpecializationsTolerated){
                    //System.out.println("All specializations of "+rule+" tolerated. ");
                    deltai.add(rule);
                }
            }


            for (DefaultRule rule : Sugar.collectionDifference(rules, deltai)) {
                MultiMap<DefaultRule, DefaultRule> specializations = DefaultTransformationUtils.representativeBodySpecializations(rule, this.interchangeable);
                boolean atLeastOneSpecializationTolerated = false;

                for (DefaultRule key : specializations.keySet()){
                    for (DefaultRule specialization : specializations.get(key)) {
                        DefaultRule groundedRepresentative = DefaultTransformationUtils.representativeSubstitution(specialization, this.interchangeable);
                        if (new ProgramSolver().solve(hardRules, Sugar.union(groundedRepresentative.body().literals(), this.makeTyping(deterministic))) != null) {
                            atLeastOneBodyPossible = true;
                            if (new ProgramSolver().solve(Sugar.union(clauses, hardRules), groundedRepresentative.body().literals(), this.makeTyping(deterministic)) != null) {
                                atLeastOneSpecializationTolerated = true;
                                deltai.add(specialization);
                            }
                        }
                    }
                }
                if (atLeastOneSpecializationTolerated) {
                    Collection<DefaultRule> specialized = Sugar.flatten(specializations.values());
                    //rules.addAll(specialized);
                    for (DefaultRule r : specialized){
                        if (new ProgramSolver().solve(hardRules, DefaultTransformationUtils.representativeSubstitution(r, this.interchangeable).body().literals(), this.makeTyping(deterministic)) != null){
                            rules.add(r);
                        }
                    }
                    rules.remove(rule);
                }
            }

            if (!atLeastOneBodyPossible) {
                break;
            } else if (deltai.isEmpty()){
                return null;
            } else {
                retVal.add(deltai);
                rules.removeAll(deltai);
            }
        }
        Set<Clause> extendedHardRules = new HashSet<Clause>();
        extendedHardRules.addAll(hardRules);
        for (Constant c : Sugar.iterable(this.interchangeable)){
            extendedHardRules.add(new Clause(new Literal("type", c)));
        }
        return new Pair<List<Set<DefaultRule>>,Set<Clause>>(retVal, extendedHardRules);
    }


    public List<Set<Constant>> interchangeable(){
        return this.interchangeable;
    }

    public Set<Literal> makeTyping(Collection<Literal> literals){
        final Map<Term,Term> typedConstants = new HashMap<Term,Term>();
        for (Set<Constant> set : this.interchangeable){
            String type = DefaultTransformationUtils.min(set).name();
            Set<Constant> newSet = new HashSet<Constant>();
            for (Constant c : set){
                Constant typedConstant = Constant.construct(c.name(), type);
                typedConstants.put(Constant.construct(c.name()), typedConstant);
                newSet.add(typedConstant);
            }
        }
        Collection<Literal> retLiterals = Sugar.funcall(literals, new Sugar.Fun<Literal,Literal>(){
            @Override
            public Literal apply(Literal literal) {
                return LogicUtils.substitute(literal, typedConstants);
            }
        });
        return Sugar.setFromCollections(retLiterals);
    }
}
