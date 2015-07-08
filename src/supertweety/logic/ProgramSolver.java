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
import ida.ilp.logic.LogicUtils;
import ida.ilp.logic.Term;
import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SpecialBinaryPredicates;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import supertweety.misc.Utils;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 06/02/15.
 */
public class ProgramSolver {

    private Set<Pair<String,Integer>> deterministicPredicates = new HashSet<Pair<String,Integer>>();

    public Set<Literal> solve(Collection<Clause> rules){
        return this.solve(rules, Sugar.<Literal>set());
    }

    public Set<Literal> solve(Collection<Clause> rules, Set<Literal> evidence){
        return this.solve(rules, evidence, Sugar.<Literal>set());
    }

    public Set<Literal> solve(Collection<Clause> rules, final Set<Literal> evidence, final Set<Literal> deterministic){
        for (Literal d : deterministic){
            this.deterministicPredicates.add(new Pair<String,Integer>(d.predicate(), d.arity()));
        }

        Set<Literal> state = new HashSet<Literal>();
        Set<Clause> activeRules = new HashSet<Clause>();
        Pair<String,Integer> p = new Pair<String,Integer>();
        for (Literal e : evidence){
            p.set(e.predicate(), e.arity());
            if (deterministicPredicates.contains(p)) {
                if ((e.isNegated() && deterministic.contains(e.negation())) || (!e.isNegated() && !deterministic.contains(e))){
                    return null;
                }
            } else {
                if (!e.isNegated()) {
                    state.add(e);
                }
                activeRules.add(new Clause(Sugar.list(e)));
            }
        }
        state.addAll(deterministic);
        Set<Clause> groundRules = new HashSet<Clause>();
        for (Clause rule : rules){
            if (LogicUtils.isGround(rule)){
                groundRules.add(rule);
            }
        }
        rules = Sugar.collectionDifference(rules, groundRules);
        activeRules.addAll(groundRules);
        activeRules = Sugar.<Clause,Clause>funcallAndRemoveNulls(activeRules, new Sugar.Fun<Clause,Clause>(){
            @Override
            public Clause apply(Clause clause) {
                if (isGroundClauseVacuouslyTrue(clause, deterministic)){
                    return null;
                } else {
                    return removeSpecialAndDeterministicPredicates(clause);
                }
            }
        });
        while (true){
            GroundProgramSolver gps = new GroundProgramSolver(activeRules);
            if ((state = gps.solve()) == null){
                return null;
            }
            state.addAll(deterministic);
            int activeRulesBefore = activeRules.size();
            activeRules.addAll(findViolatedRules(rules, state));
            activeRules = Sugar.<Clause,Clause>funcallAndRemoveNulls(activeRules, new Sugar.Fun<Clause,Clause>(){
                @Override
                public Clause apply(Clause clause) {
                    if (isGroundClauseVacuouslyTrue(clause, deterministic)){
                        return null;
                    } else {
                        return removeSpecialAndDeterministicPredicates(clause);
                    }
                }
            });
            if (activeRulesBefore == activeRules.size()){
                break;
            }

        }
        return state;
    }

    public List<Clause> findViolatedRules(Collection<Clause> rules, Set<Literal> currentState){
        List<Clause> violated = new ArrayList<Clause>();
        Matching matching = new Matching(Sugar.list(new Clause(currentState)));
        for (Clause rule : rules){
            Pair<Term[], List<Term[]>> substitutions = matching.allSubstitutions(Utils.flipSigns(rule), 0, Integer.MAX_VALUE);
            for (Term[] subs : substitutions.s) {
                violated.add(Utils.substitute(rule, substitutions.r, subs));
            }
        }
        return violated;
    }

    private boolean isGroundClauseVacuouslyTrue(Clause c, Set<Literal> deterministic){
        for (Literal l : c.literals()){
            if (SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate()) || SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate())){
                return isSpecialGroundTrue(l);
            } else if (this.deterministicPredicates.contains(new Pair<String,Integer>(l.predicate(), l.arity()))){
                if ((!l.isNegated() && deterministic.contains(l)) || (l.isNegated() && !deterministic.contains(l.negation()))){
                    return true;
                }
            }
        }
        return false;
    }

    private Clause removeSpecialAndDeterministicPredicates(Clause clause){
        List<Literal> filtered = new ArrayList<Literal>();
        Set<String> specialPredicates = Sugar.setFromCollections(SpecialBinaryPredicates.SPECIAL_PREDICATES, SpecialVarargPredicates.SPECIAL_PREDICATES);
        for (Literal literal : clause.literals()){
            if (!specialPredicates.contains(literal.predicate()) &&
                    !deterministicPredicates.contains(new Pair<String,Integer>(literal.predicate(), literal.arity()))){
                filtered.add(literal);
            }
        }
        return new Clause(filtered);
    }

    private boolean isSpecialGroundTrue(Literal l){
        if (SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate())){
            return SpecialBinaryPredicates.isTrueGround(l);
        } else if (SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate())){
            return SpecialVarargPredicates.isTrueGround(l);
        }
        return false;
    }

    public static void main(String[] args){
        ProgramSolver ps = new ProgramSolver();
        System.out.println(
                ps.solve(
                        Sugar.<Clause>list(
                                Clause.parse("!@neq(X,tweety:tweety), !bird(X), flies(X)"),
                                Clause.parse("!bird(X), !antarctic(X), !flies(X)"),
                                Clause.parse("!flies(X), !parent(X,Y), flies(Y)"),
                                //Clause.parse("exists(tweety:tweety)"),
                                Clause.parse("exists(donald:donald)")
                        ),
                        Clause.parse("bird(donald:donald), antarctic(donald:donald)").literals()
                )
        );
    }
}
