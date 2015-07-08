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
import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SpecialBinaryPredicates;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.ilp.logic.subsumption.SymmetricPredicates;
import ida.utils.Combinatorics;
import ida.utils.Sugar;
import ida.utils.VectorUtils;
import ida.utils.collections.Counters;
import ida.utils.collections.MultiList;
import ida.utils.collections.MultiMap;
import ida.utils.collections.NaturalNumbersList;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;
import ida.utils.tuples.Tuple;
import supertweety.misc.Utils;

import java.util.*;

/**
 * Created by ondrejkuzelka on 13/04/15.
 */
public class DefaultTransformationUtils {

    private static Clause preprocessClause(Clause c, String prefix){
        List<Literal> newLiterals = new ArrayList<Literal>();
        int specialID = 0;
        for (Literal l : c.literals()){
            String predicate = l.predicate();
            if (predicate.equals(SpecialBinaryPredicates.NEQ) ||
                    predicate.equals(SpecialBinaryPredicates.EQ) ||
                    predicate.equals(SpecialVarargPredicates.ALLDIFF)){
                predicate = SymmetricPredicates.PREFIX + prefix + predicate;
            } else {
                predicate = prefix + predicate;
            }
            Literal newLit = new Literal(predicate, l.isNegated(), l.arity());
            for (int i = 0; i < l.arity(); i++) {
                newLit.set(l.get(i), i);
            }
            newLiterals.add(newLit);
        }
        return new Clause(newLiterals);
    }

    private static DefaultRule preprocess(DefaultRule r){
        return new DefaultRule(preprocessClause(r.body(), "body:"), preprocessClause(r.head(), "head:"));
    }

    public static boolean isomorphic(DefaultRule a, DefaultRule b){
        a = preprocess(a);
        b = preprocess(b);
        Matching m = new Matching();
        Clause ca = new Clause(Sugar.iterable(a.body().literals(), a.head().literals()));
        Clause cb = new Clause(Sugar.iterable(b.body().literals(), b.head().literals()));
        return ca.variables().size() == cb.variables().size() && ca.literals().size() == cb.literals().size() && m.isomorphism(ca, cb);
    }

    public static Set<DefaultRule> selectNonisomorphicDefaultRules(Iterable<DefaultRule> defaultRules){
        List<Clause> candidates = new ArrayList<Clause>();
        for (DefaultRule rule : defaultRules){
            DefaultRule preprocessed = preprocess(rule);
            candidates.add(new Clause(Sugar.<Literal>iterable(preprocessed.body().literals(), preprocessed.head().literals())));
        }
        Matching m = new Matching();
        Set<DefaultRule> retVal = new HashSet<DefaultRule>();
        for (Clause c : m.nonisomorphic(candidates)){
            List<Literal> head = new ArrayList<Literal>();
            List<Literal> body = new ArrayList<Literal>();
            for (Literal l : c.literals()){
                Literal newLiteral = new Literal(l.predicate().substring(l.predicate().indexOf(":")+1), l.isNegated(), l.arity());
                for (int i = 0; i < l.arity(); i++){
                    newLiteral.set(l.get(i), i);
                }
                if (l.predicate().startsWith("body:") || l.predicate().startsWith(SymmetricPredicates.PREFIX+"body:")){
                    body.add(newLiteral);
                } else {
                    head.add(newLiteral);
                }
            }
            retVal.add(new DefaultRule(new Clause(body), new Clause(head)));
        }
        return retVal;
    }


    public static DefaultRule substitute(DefaultRule rule, Term[] template, Term[] substitution){
        return new DefaultRule(LogicUtils.substitute(rule.body(), template, substitution), LogicUtils.substitute(rule.head(), template, substitution));
    }


    public static DefaultRule substitute(DefaultRule rule, Map<Term,Term> substitution){
        return new DefaultRule(LogicUtils.substitute(rule.body(), substitution), LogicUtils.substitute(rule.head(), substitution));
    }


    public static List<Set<Constant>> partitionInterchangeableConstants(Collection<DefaultRule> rules, Collection<Clause> hardRules){
        List<Set<Constant>> retVal = new ArrayList<Set<Constant>>();
        Collection<DefaultRule> dummyRules = Sugar.<Clause,DefaultRule>funcall(hardRules, new Sugar.Fun<Clause,DefaultRule>(){
            @Override
            public DefaultRule apply(Clause clause) {
                return new DefaultRule(new Clause(Sugar.<Literal>list()), clause);
            }
        });
        for (List<Set<Constant>> list : partitionExchangeable_impl(Sugar.union(rules, dummyRules)).values()) {
            retVal.addAll(list);
        }
        return retVal;
    }


    private static MultiList<Object,Set<Constant>> partitionExchangeable_impl(Iterable<DefaultRule> rules){
        MultiMap<Term,Term> partitioning = new MultiMap<Term, Term>();

        List<Term> constants = Sugar.arrayListFromCollections(constants(rules));
        Set<Term> closed = new HashSet<Term>();

        //checking interchangeability pairwise
        for (int i = 0; i < constants.size(); i++){
            if (!closed.contains(constants.get(i))){
                partitioning.put(constants.get(i), constants.get(i));
                for (int j = i+1; j < constants.size(); j++){
                    if (areExchangeable(constants.get(i), constants.get(j), rules)){
                        partitioning.put(constants.get(i), constants.get(j));
                        closed.add(constants.get(j));
                    }
                }
            }
        }
        Map<Constant,Constant> map = new HashMap<Constant,Constant>();
        for (Map.Entry<Term,Set<Term>> entry : partitioning.entrySet()){
            Constant lexmin = null;
            for (Term t : entry.getValue()){
                if (t instanceof Constant) {
                    if (lexmin == null || t.toString().compareTo(lexmin.toString()) < 0) {
                        lexmin = (Constant)t;
                    }
                }
            }
            for (Term t : entry.getValue()){
                if (t instanceof Constant) {
                    map.put((Constant)t, lexmin);
                }
            }
        }

        MultiMap<Pair<Object,Constant>,Constant> mm = new MultiMap<Pair<Object,Constant>,Constant>();
        for (Map.Entry<Constant,Constant> entry : map.entrySet()){
            mm.put(new Pair<Object,Constant>(entry.getValue().type() == null ? Sugar.NIL : entry.getValue().type(), entry.getValue()), entry.getKey());
        }

        MultiList<Object,Set<Constant>> retVal = new MultiList<Object,Set<Constant>>();
        for (Map.Entry<Pair<Object,Constant>,Set<Constant>> entry : mm.entrySet()){
            retVal.put(entry.getKey().r, entry.getValue());
        }
        return retVal;
    }


    private static boolean areExchangeable(Term a, Term b, Iterable<DefaultRule> rules){
        Map<Term,Term> substitution = new HashMap<Term,Term>();
        substitution.put(a,b);
        substitution.put(b,a);
        Counters<DefaultRule> substitutedMultiset = new Counters<DefaultRule>();
        for (DefaultRule rule : rules){
            DefaultRule defaultRule = substitute(rule, substitution);
            for (DefaultRule rule2 : rules){
                if (isomorphic(rule2, defaultRule)){
                    defaultRule = rule2;
                }
            }
            substitutedMultiset.increment(defaultRule);
        }
        for (DefaultRule rule : rules){
            if (substitutedMultiset.decrementPre(rule) < 0){
                return false;
            }
        }
//        outerLoop: for (DefaultRule rule : rules){
//            if (rule.body().terms().contains(a) || rule.head().terms().contains(a) ||
//                    rule.body().terms().contains(b) || rule.head().terms().contains(b)) {
//                DefaultRule newDefault = substitute(rule, substitution);
//                for (DefaultRule rule2 : rules) {
//                    if (isomorphic(rule2, newDefault)) {
//                        continue outerLoop;
//                    }
//                }
//                return false;
//            }
//        }
        return true;
    }


    private static Set<Term> constants(Iterable<DefaultRule> rules){
        Set<Term> retVal = new HashSet<Term>();
        for (DefaultRule rule : rules){
            for (Term t : Sugar.<Term>iterable(rule.body().terms(), rule.head().terms())){
                if (t instanceof Constant){
                    retVal.add(t);
                }
            }
        }
        return retVal;
    }


    public static void addDomainConstants(Iterable<Term> constants, MultiList<Object,Set<Term>> interchangeable){
        MultiMap<Object,Term> typed = new MultiMap<Object,Term>();
        for (Term t : constants){
            typed.put(t.type() == null ? Sugar.NIL : t.type(), t);
        }
        for (Map.Entry<Object,Set<Term>> entry : typed.entrySet()){
            interchangeable.put(entry.getKey(), entry.getValue());
        }
    }


    public static DefaultRule representativeSubstitution(DefaultRule rule, List<Set<Constant>> interchangeable){
        if (rule.body().variables().isEmpty()){
            return rule;
        } else {
            //a bit naive (but not too much), it can be improved later...
            List<Literal> auxLiteralsC = new ArrayList<Literal>();
            for (Variable v : rule.body().variables()) {
                auxLiteralsC.add(new Literal("v", v));
            }

            List<Literal> auxLiteralsE = new ArrayList<Literal>();

            int typeIndex = 0;
            for (Set<Constant> interch : interchangeable) {
                int counter = 0;
                for (Term t : interch) {
                    auxLiteralsE.add(new Literal("v", t));
                    if (++counter >= rule.body().variables().size()) {
                        break;
                    }
                }
            }
            Matching m = new Matching();
            m.setSubsumptionMode(Matching.OI_SUBSUMPTION);
            Pair<Term[], List<Term[]>> substitutions = m.allSubstitutions(new Clause(auxLiteralsC), new Clause(auxLiteralsE), 1);
            return DefaultTransformationUtils.substitute(rule, substitutions.r, substitutions.s.get(0));
        }
    }


    public static MultiMap<DefaultRule,DefaultRule> representativeBodySpecializations(DefaultRule rule, List<Set<Constant>> interchangeableConstants){
        Clause body = rule.body();
        Clause head = rule.head();
        final MultiMap<Variable,Variable> different = new MultiMap<Variable,Variable>();
        for (Literal literal : Sugar.union(
                body.getLiteralsByPredicate(SpecialBinaryPredicates.NEQ),
                body.getLiteralsByPredicate(SpecialBinaryPredicates.GT),
                body.getLiteralsByPredicate(SpecialBinaryPredicates.LT),
                body.getLiteralsByPredicate(SpecialVarargPredicates.ALLDIFF),
                head.getLiteralsByPredicate(SpecialBinaryPredicates.NEQ),
                head.getLiteralsByPredicate(SpecialBinaryPredicates.GT),
                head.getLiteralsByPredicate(SpecialBinaryPredicates.LT),
                head.getLiteralsByPredicate(SpecialVarargPredicates.ALLDIFF))){
            for (Term a : literal.terms()){
                if (a instanceof Variable){
                    Variable v1 = (Variable)a;
                    for (Term b : literal.terms()){
                        if (b instanceof  Variable){
                            Variable v2 = (Variable)b;
                            if (v1 != v2){
                                different.put(v1,v2);
                            }
                        }
                    }
                }
            }
        }


        final List<Variable> variables = Sugar.<Variable>listFromCollections(body.variables());
        List<Integer> indices = VectorUtils.toList(VectorUtils.sequence(0, variables.size() - 1));
        List<Tuple<Integer>> unifications =  Combinatorics.<Integer>cartesianPower(indices, indices.size(),
                new Sugar.Fun<Tuple<Integer>, Boolean>() {
                    @Override
                    public Boolean apply(Tuple<Integer> integerTuple) {
                        for (int i = 0; i < integerTuple.size(); i++) {
                            if (integerTuple.get(i) > i ||
                                    !integerTuple.get(i).equals(integerTuple.get(integerTuple.get(i))) ||
                                    different.get(variables.get(integerTuple.get(i))).contains(variables.get(i))
                                    || !sameType(variables.get(integerTuple.get(i)), variables.get(i))) {
                                return Boolean.FALSE;
                            }
                        }
                        return Boolean.TRUE;
                    }
                }
        );

        Set<DefaultRule> nonIsomorphicUnifications = new HashSet<DefaultRule>();
        for (Tuple<Integer> unification : unifications){
            Map<Term,Term> substitution = new HashMap<Term,Term>();
            for (int i = 0; i < unification.size(); i++){
                substitution.put(variables.get(i), variables.get(unification.get(i)));
            }
            Clause newBody = LogicUtils.substitute(rule.body(), substitution);
            Clause newHead = LogicUtils.substitute(rule.head(), substitution);
            nonIsomorphicUnifications.add(new DefaultRule(
                    newBody.variables().size() > 1 ? new Clause(Sugar.union(newBody.literals(), allDiffLiteral(newBody))) : newBody,
                    newHead));
        }

        nonIsomorphicUnifications = DefaultTransformationUtils.selectNonisomorphicDefaultRules(nonIsomorphicUnifications);

        MultiMap<DefaultRule,DefaultRule> retVal = new MultiMap<DefaultRule,DefaultRule>();

//        for (DefaultRule unifiedRule : nonIsomorphicUnifications) {
//
//            List<Literal> auxLiteralsC = new ArrayList<Literal>();
//            for (Variable v : unifiedRule.body().variables()) {
//                auxLiteralsC.add(new Literal("v", v));
//            }
//
//            List<Literal> auxLiteralsE = new ArrayList<Literal>();
//
//            int typeIndex = 0;
//            for (Set<Constant> interch : interchangeableConstants) {
//                int counter = 0;
//                for (Term t : interch) {
//                    auxLiteralsE.add(new Literal("v", t));
//                    if (++counter >= unifiedRule.body().variables().size()) {
//                        break;
//                    }
//                }
//            }
//
//            if (auxLiteralsC.isEmpty()) {
//                retVal.put(unifiedRule, unifiedRule);
//            } else {
//                Matching m = new Matching();
//                m.setSubsumptionMode(Matching.OI_SUBSUMPTION);
//                Pair<Term[], List<Term[]>> substitutions = m.allSubstitutions(new Clause(auxLiteralsC), new Clause(auxLiteralsE));
//                Set<DefaultRule> substituted = new HashSet<DefaultRule>();
//                for (Term[] substitution : substitutions.s) {
//                    Map<Term, Term> subs2 = new HashMap<Term, Term>();
//                    for (int i = 0; i < substitutions.r.length; i++) {
//                        subs2.put(substitutions.r[i], Variable.construct(substitutions.r[i].name(), substitution[i].type()));
//                    }
//                    substituted.add(DefaultTransformationUtils.substitute(unifiedRule, subs2));
//                }
//                System.out.println("::: "+rule);
//                System.out.println(unifiedRule+": ");
//                for (DefaultRule r : DefaultTransformationUtils.selectNonisomorphicDefaultRules(substituted)){
//                    System.out.println("\t"+r);
//                }
//                retVal.putAll(unifiedRule, DefaultTransformationUtils.selectNonisomorphicDefaultRules(substituted));
//            }
//        }

        //this needs to be improved... e.g. using typing information...
        MultiList<Integer,Constant> consts = new MultiList<Integer,Constant>();
        int index = 0;
        for (Set<Constant> interch : interchangeableConstants){
            consts.putAll(index++, interch);
        }
        for (DefaultRule unifiedRule : nonIsomorphicUnifications) {
            List<Variable> unifsVariables = Sugar.listFromCollections(unifiedRule.variables());
            if (unifsVariables.isEmpty()) {
                retVal.put(unifiedRule, unifiedRule);
            } else {
                Set<DefaultRule> substituted = new HashSet<DefaultRule>();
                middleLoop:
                for (Tuple<Integer> tuple : Combinatorics.cartesianPower(new NaturalNumbersList(0, interchangeableConstants.size()), unifsVariables.size())) {
                    Counters<Integer> used = new Counters<Integer>();
                    Map<Term, Term> substitution = new HashMap<Term, Term>();
                    for (int i = 0; i < unifsVariables.size(); i++) {
                        int j = used.incrementPost(tuple.get(i));
                        if (j >= consts.get(tuple.get(i)).size()) {
                            continue middleLoop;
                        } else {
                            if (unifsVariables.get(i).type() == null) {
                                substitution.put(unifsVariables.get(i), Variable.construct(unifsVariables.get(i).name(), consts.get(tuple.get(i)).get(j).type()));
                            } else {
                                if (unifsVariables.get(i).type().equals(consts.get(tuple.get(i)).get(j).type())){
                                    substitution.put(unifsVariables.get(i), Variable.construct(unifsVariables.get(i).name(), consts.get(tuple.get(i)).get(j).type()));
                                } else {
                                    continue middleLoop;
                                }
                            }
                        }
                    }
                    substituted.add(DefaultTransformationUtils.substitute(unifiedRule, substitution));
                }
                retVal.putAll(unifiedRule, DefaultTransformationUtils.selectNonisomorphicDefaultRules(substituted));
            }
        }
        return retVal;
    }

    private static boolean sameType(Term a, Term b){
        if (a.type() == null && b.type() == null){
            return true;
        } else if ((a.type() == null && b.type() != null) || (a.type() != null && b.type() == null)) {
            return false;
        } else {
            return a.type().equals(b.type());
        }
    }


    public static Literal allDiffLiteral(Clause c){
        Literal l = new Literal(SpecialVarargPredicates.ALLDIFF, c.variables().size());
        int i = 0;
        for (Variable v : c.variables()){
            l.set(v,i++);
        }
        return l;
    }

    public static Clause clauseFromDefault(DefaultRule rule){
        return new Clause(Sugar.iterable(Utils.flipSigns(rule.body().literals()), rule.head().literals()));
    }

    public static List<Clause> clausesFromDefaults(Iterable<DefaultRule> rules){
        List<Clause> retVal = new ArrayList<Clause>();
        for (DefaultRule rule : rules){
            retVal.add(clauseFromDefault(rule));
        }
        return retVal;
    }


    public static Term min(Iterable<? extends Term> iterable){
        Term min = null;
        for (Term t : iterable){
            if (min == null || t.name().compareTo(min.name()) < 0){
                min = t;
            }
        }
        return min;
    }


    public static Triple<Set<DefaultRule>,Set<Clause>,List<Set<Constant>>> preprocessConstants(Collection<DefaultRule> rules, Collection<Clause> hardRules, List<Set<Constant>> interchangeable){
        final Map<Term,Term> typedConstants = new HashMap<Term,Term>();
        List<Set<Constant>> retInterchangeable = new ArrayList<Set<Constant>>();
        for (Set<Constant> set : interchangeable){
            String type = min(set).name();
            Set<Constant> newSet = new HashSet<Constant>();
            for (Constant c : set){
                Constant typedConstant = Constant.construct(c.name(), type);
                typedConstants.put(c, typedConstant);
                newSet.add(typedConstant);
            }
            retInterchangeable.add(newSet);
        }
        Collection<DefaultRule> retDefaultRules = Sugar.funcall(rules, new Sugar.Fun<DefaultRule,DefaultRule>(){
            @Override
            public DefaultRule apply(DefaultRule defaultRule) {
                return DefaultTransformationUtils.substitute(defaultRule, typedConstants);
            }
        });
        Collection<Clause> retHardRules = Sugar.funcall(hardRules, new Sugar.Fun<Clause,Clause>(){
            @Override
            public Clause apply(Clause hardRule) {
                return LogicUtils.substitute(hardRule, typedConstants);
            }
        });
        return new Triple<Set<DefaultRule>,Set<Clause>,List<Set<Constant>>>(Sugar.setFromCollections(retDefaultRules), Sugar.setFromCollections(retHardRules), Sugar.listFromCollections(retInterchangeable));
    }

    public static void main(String[] args){
        DefaultRule a = new DefaultRule(Clause.parse("a(X)"), Clause.parse("a(Y)"));
        DefaultRule b = new DefaultRule(Clause.parse("a(A)"), Clause.parse("a(B)"));
        DefaultRule c = new DefaultRule(Clause.parse("a(A)"), Clause.parse("a(A)"));
        DefaultRule d = new DefaultRule(Clause.parse("a(A,a)"), Clause.parse("b(B,b)"));
        DefaultRule e = new DefaultRule(Clause.parse("a(A,b)"), Clause.parse("b(B,a)"));
        DefaultRule f = new DefaultRule(Clause.parse("a(A,c)"), Clause.parse("b(B,d)"));
        for (DefaultRule r : selectNonisomorphicDefaultRules(Sugar.list(a, b, c, d))){
            System.out.println(r);
        }
        System.out.println(partitionInterchangeableConstants(Sugar.list(a, b, c, d, e, f), Sugar.<Clause>set()));
    }
}
