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

import ida.ilp.logic.*;
import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.utils.Sugar;
import ida.utils.collections.Counters;
import ida.utils.collections.Heap;
import ida.utils.collections.MultiList;
import ida.utils.collections.MultiMap;
import ida.utils.tuples.Pair;
import ida.utils.tuples.Triple;
import supertweety.defaults.DefaultRule;
import supertweety.logic.ProgramSolver;
import supertweety.misc.Utils;
import supertweety.mln.MLNContradictionException;
import supertweety.mln.MarkovLogic;
import supertweety.possibilistic.PossibilisticLogic;

import java.math.BigInteger;
import java.util.*;

/**
 * Created by ondrejkuzelka on 07/02/15.
 */
public class ExhaustiveConvertor {

    public final static int RANDOM = 1, EXHAUSTIVE = 2;

    //The MLN is assumed to be consistent!
    private MarkovLogic mln;

    private Set<Term> constants = new HashSet<Term>();

    private Random random = new Random(Settings.seed);

    private static String TYPE_PREFIX = "type:";

    public int maxIters = Integer.MAX_VALUE;

    public int maxEvidenceSetSize = Integer.MAX_VALUE;

    private int mode = EXHAUSTIVE;

    private int mapInferenceIterations = Settings.mapInferenceIterations;

    private Set<Pair<String,Integer>> deterministicPredicates = new HashSet<Pair<String,Integer>>();

    private MultiMap<Pair<Clause,Double>,DefaultRule> clausesToRules = new MultiMap<Pair<Clause,Double>,DefaultRule>();

    private PossibilisticLogic possibilisticLogic = new PossibilisticLogic();

    private boolean doNotRemoveEntailedByLonger = true;

    private boolean shortDrowningEnforcingClauses = false;

    public ExhaustiveConvertor(MarkovLogic mln, Set<Term> constants){
        this.mln = mln;
        this.constants.addAll(constants);
    }

    public void convert(int iterations){
        this.maxIters = iterations;
        this.levelBased();
    }

    private void levelBased(){
        Map<Term,Pair<Term,Integer>> exchangeable = partitionExchangeable(this.mln);
        System.out.println("EXCHANGEABLE: "+exchangeable);

        PossibilisticLogic theory = new PossibilisticLogic();
        Set<Clause> hardRules = new HashSet<Clause>();
        hardRules.addAll(this.mln.hardRules());
        for (Map.Entry<Term,Pair<Term,Integer>> entry : exchangeable.entrySet()){
            if (entry.getValue().s > 1) {
                hardRules.add(new Clause(Sugar.list(makeTypeLiteral(entry.getKey(), entry.getValue().r))));
            }
        }
        System.out.println("HARD RULES: " + hardRules);

        for (Clause hardRule : hardRules){
            theory.add(hardRule, Double.POSITIVE_INFINITY);
        }

        MultiMap<Pair<Literal,Integer>,Pair<Set<Literal>,Set<Literal>>> evidenceLiterals2rules = new MultiMap<Pair<Literal,Integer>,Pair<Set<Literal>,Set<Literal>>>();
        Heap<Set<Literal>> heap = new Heap<Set<Literal>>();
        Closed closed = new Closed();
        heap.add(0.0, new HashSet<Literal>());

        int iterations = 0;
        int numPruned = 0, numUnpruned = 0, numPrunedByHardRuleEntailmentCheck = 0;
        while (heap.size() > 0 && iterations++ < maxIters){
            MarkovLogic mlnCopy1 = mln.makeCopy();
            double penalty = heap.lookAtMinKey();
            Set<Literal> evidenceSet = heap.removeMin();
            penalty -= evidenceSet.size()/1.0e3;
            double penaltyFromHeap = penalty;


            Set<Literal> consequenceSet = null;
            if (isMinimalWrt(evidenceSet, evidenceLiterals2rules, (int) penalty, hardRules)) {
                numUnpruned++;
                mlnCopy1.resetEvidence();
                mlnCopy1.resetState();
                mlnCopy1.addEvidence(evidenceSet);
                try {
                    mlnCopy1.runMAPInference(this.mapInferenceIterations);
                } catch (MLNContradictionException e){
                    System.out.println("Contradiction exception. Why?");
                }
                penalty = mlnCopy1.doublePenalty();
                consequenceSet = Sugar.<Literal,Literal>funcallAndRemoveNulls(Sugar.union(
                        findPositiveConsequence(evidenceSet, mlnCopy1.state(), penalty),
                        findNegativeConsequence(evidenceSet, mlnCopy1.state(), penalty)
                ), new Sugar.Fun<Literal,Literal>(){
                    @Override
                    public Literal apply(Literal literal) {
                        if (isDeterministic(literal)){
                            return null;
                        } else {
                            return literal;
                        }
                    }
                });


                if (!consequenceSet.isEmpty()) {
                    save(evidenceSet, consequenceSet, (int)penalty, evidenceLiterals2rules);
                    for (Literal consequenceLiteral : consequenceSet){
                        if (!isDeterministic(consequenceLiteral) && !isImpliedByHardRules(Sugar.union(hardRules, theory.getAlphaLevel(penalty)), evidenceSet, Sugar.set(consequenceLiteral))) {
                            System.out.println("CONSEQUENCE OF " + evidenceSet + " IS " + consequenceLiteral + ", PENALTY: " + penalty+", PENALTY FROM HEAP: "+penaltyFromHeap/*+", ev: "+mlnCopy1.state()*/);
                            Clause liftedClause = liftClause(new Clause(Sugar.union(Utils.flipSigns(evidenceSet), consequenceLiteral)), exchangeable);
                            theory.add(liftedClause, penalty);
                            Pair<Clause,Clause> ldr = liftDefaultRule(new Clause(evidenceSet), new Clause(consequenceLiteral), exchangeable);
                            this.clausesToRules.put(new Pair<Clause,Double>(liftedClause, penalty), new DefaultRule(ldr.r, ldr.s));
                        }
                    }
                    if (theory.levels().lower(penalty) != null){
                        Set<Literal> filteredConsequenceSet = new HashSet<Literal>();
                        for (Literal consequenceLiteral : consequenceSet) {
                            if (!isDeterministic(consequenceLiteral) && !isImpliedByHardRules(hardRules, evidenceSet, Sugar.set(consequenceLiteral))) {
                                filteredConsequenceSet.add(consequenceLiteral);
                            }
                        }
                        System.out.println("~CONSEQUENCE OF " + evidenceSet + " IS " + filteredConsequenceSet + ", PENALTY: " + penalty+", PENALTY FROM HEAP: "+penaltyFromHeap/*+", ev: "+mlnCopy1.state()*/);
                        if (shortDrowningEnforcingClauses){
                            theory.add(liftClause(new Clause(Utils.flipSigns(evidenceSet)), exchangeable), theory.levels().lower(penalty));
                        } else {
                            theory.add(liftClause(new Clause(Utils.flipSigns(Sugar.union(evidenceSet, filteredConsequenceSet))), exchangeable), theory.levels().lower(penalty));
                        }
                    }
                }
            } else {
                numPruned++;
            }

            //EXTENDING THE EVIDENCE SET
            Clause liftedEvidencePlusConsequence = null;
            if (consequenceSet != null) {
                liftedEvidencePlusConsequence = liftClause(new Clause(Sugar.union(evidenceSet, consequenceSet)), exchangeable);
            }
            //extending the evidence set
            if (evidenceSet.size() < this.maxEvidenceSetSize) {
                for (Literal stateLiteral : mlnCopy1.completeState()) {
                    for (Literal l : Sugar.list(stateLiteral, stateLiteral.negation())) {
                        Set<Literal> extendedEvidenceSet = Sugar.<Literal>union(evidenceSet, l);
                        Clause liftedExtendedEvidenceSet = liftClause(new Clause(extendedEvidenceSet), exchangeable);
                        if (!isDeterministic(l) && !evidenceSet.contains(l) && !evidenceSet.contains(l.negation()) &&
                                (consequenceSet != null && !consequenceSet.contains(l)) &&
                                (liftedEvidencePlusConsequence == null ||
                                        !subIsomorphism(liftedExtendedEvidenceSet, liftedEvidencePlusConsequence)) &&  //the same as above but with symmetry awareness
                                !isImpliedByHardRules(hardRules, evidenceSet, Sugar.set(l))) {

                            MarkovLogic mlnCopy2 = this.mln.makeCopy();

                            if (!closed.containsIsomorphic(liftedExtendedEvidenceSet)) {
                                mlnCopy2.resetEvidence();
                                mlnCopy2.addEvidence(extendedEvidenceSet);
                                if (mlnCopy2.isConsistent()) { // it would make no sense to consider evidence sets inconsistent with the hard rules iterable the MLN
                                    mlnCopy2.runMAPInference(this.mapInferenceIterations);
                                    double penaltyOfExtendedEvidenceSet = mlnCopy2.doublePenalty();
                                    heap.add(penaltyOfExtendedEvidenceSet + extendedEvidenceSet.size() / 1.0e3, extendedEvidenceSet);
                                    closed.store(liftClause(new Clause(extendedEvidenceSet), exchangeable));
                                }
                            } else {
                                //System.out.println("ISO>>> "+extendedEvidenceSet);
                            }
                        }
                    }
                }
            }
            if (iterations % 100 == 0){
                System.out.println("ITERATION: "+iterations);
            }
        }
        //System.out.println("CLOSED: "+closed.closed);

        System.out.println("Pruned: "+numPruned+", unpruned: "+numUnpruned+", pruned by hard-rule-entailment checks: "+numPrunedByHardRuleEntailmentCheck);
        //this.possibilisticLogic = theory;
        this.possibilisticLogic = postprocess(theory, exchangeable);
    }


    private static Clause liftClause(Clause clause, Map<Term, Pair<Term, Integer>> exchangeable){
        Map<Term, Term> substitution = new HashMap<Term, Term>();
        Set<Variable> freshVariables = new HashSet<Variable>();
        List<Literal> literals = new ArrayList<Literal>();
        for (Literal l : clause.literals()) {
            literals.add(l);
        }
        int index = 1;
        MultiMap<Term, Term> partitioning = new MultiMap<Term, Term>();
        for (Term t : clause.terms()) {
            if (!substitution.containsKey(t)) {
                if (exchangeable.containsKey(t) && exchangeable.get(t).s > 1) {
                    literals.add(makeTypeLiteral(t, exchangeable.get(t).r).negation());
                    Variable freshVariable = LogicUtils.freshVariable(freshVariables, index++);
                    freshVariables.add(freshVariable);
                    substitution.put(t, freshVariable);
                }
            }
            if (exchangeable.containsKey(t) && exchangeable.get(t).s > 1) {
                partitioning.put(exchangeable.get(t).r, t);
            }
        }
        for (Map.Entry<Term, Set<Term>> entry : partitioning.entrySet()) {
            Literal alldiff = new Literal(SpecialVarargPredicates.ALLDIFF, true, entry.getValue().size());
            int i = 0;
            for (Term ad : entry.getValue()) {
                alldiff.set(ad, i++);
            }
            if (alldiff.arity() > 1) {
                literals.add(alldiff);
            }
        }
        return LogicUtils.substitute(new Clause(literals), substitution);
    }

    private static Pair<Clause,Clause> liftDefaultRule(Clause body, Clause head, Map<Term, Pair<Term, Integer>> exchangeable){
        Map<Term, Term> substitution = new HashMap<Term, Term>();
        Set<Variable> freshVariables = new HashSet<Variable>();
        List<Literal> bodyLiterals = Sugar.listFromCollections(body.literals());
        List<Literal> headLiterals = Sugar.listFromCollections(head.literals());
        int index = 1;
        MultiMap<Term, Term> partitioning = new MultiMap<Term, Term>();
        for (Term t : Sugar.iterable(body.terms(), head.terms())) {
            if (!substitution.containsKey(t)) {
                if (exchangeable.containsKey(t) && exchangeable.get(t).s > 1) {
                    bodyLiterals.add(makeTypeLiteral(t, exchangeable.get(t).r));
                    Variable freshVariable = LogicUtils.freshVariable(freshVariables, index++);
                    freshVariables.add(freshVariable);
                    substitution.put(t, freshVariable);
                }
            }
            if (exchangeable.containsKey(t) && exchangeable.get(t).s > 1) {
                partitioning.put(exchangeable.get(t).r, t);
            }
        }
        for (Map.Entry<Term, Set<Term>> entry : partitioning.entrySet()) {
            Literal alldiff = new Literal(SpecialVarargPredicates.ALLDIFF, false, entry.getValue().size());
            int i = 0;
            for (Term ad : entry.getValue()) {
                alldiff.set(ad, i++);
            }
            if (alldiff.arity() > 1) {
                bodyLiterals.add(alldiff);
            }
        }
        return new Pair<Clause,Clause>(
                LogicUtils.substitute(new Clause(bodyLiterals), substitution),
                LogicUtils.substitute(new Clause(headLiterals), substitution)
                );
    }

    private static Literal makeTypeLiteral(Term term, Term type){
        return new Literal(TYPE_PREFIX+type, term);
    }

    private void save(Set<Literal> evidence, Set<Literal> consequence, int penalty, MultiMap<Pair<Literal,Integer>,Pair<Set<Literal>,Set<Literal>>> multiMap){
        for (Literal evLit : evidence){
            multiMap.put(new Pair<Literal,Integer>(evLit, penalty), new Pair(evidence, consequence));
        }
        for (Literal consLit : consequence){
            if (!isDeterministic(consLit)) {
                multiMap.put(new Pair<Literal, Integer>(consLit, penalty), new Pair(evidence, consequence));
            }
        }
    }

    private static boolean isMinimalWrt(Set<Literal> evidence, MultiMap<Pair<Literal,Integer>,Pair<Set<Literal>,Set<Literal>>> multiMap, int penalty, Collection<Clause> hardRules){
        Set<Pair<Set<Literal>,Set<Literal>>> candidates = null;
        for (Literal evLiteral : evidence){
            if (candidates == null){
                candidates = multiMap.get(new Pair<Literal,Integer>(evLiteral, penalty));
            } else {
                candidates = Sugar.intersection(candidates, multiMap.get(new Pair<Literal,Integer>(evLiteral, penalty)));
            }
        }
        if (candidates != null) {
            for (Pair<Set<Literal>, Set<Literal>> candidate : candidates) {
                if (Sugar.isSubsetOf(evidence, Sugar.union(candidate.r, candidate.s))) {
                    ProgramSolver ps = new ProgramSolver();
                    if (ps.solve(Sugar.<Clause>listFromCollections(hardRules, Sugar.list(new Clause(Utils.flipSigns(candidate.r)))), evidence) == null) {
                        //System.out.println(evidence + " => IS NOT MINIMAL BECAUSE OF "+candidate);
                        return false;
                    }
                }
            }
        }
        return true;
    }

    private static boolean isImpliedByHardRules(Collection<Clause> hardRules, Set<Literal> evidence, Set<Literal> consequence){
        List<Clause> alphaLevel = Sugar.listFromCollections(hardRules);
        for (Literal evLit : evidence){
            alphaLevel.add(new Clause(Sugar.list(evLit)));
        }
        if (consequence.size() > 0) {
            alphaLevel.add(Utils.flipSigns(new Clause(consequence)));
        }
        ProgramSolver gps = new ProgramSolver();
        return gps.solve(alphaLevel) == null;
    }

    private static boolean isImplied(Clause clause, Collection<Clause> alphaLevel, Collection<Clause> strictAlphaCut){
        Set<Clause> copyOfAlphaLevel = Sugar.setFromCollections(alphaLevel);
        copyOfAlphaLevel.remove(clause);
        for (Literal clauseLit : Utils.flipSigns(clause).literals()){
            if (!clauseLit.predicate().startsWith("@")) {
                copyOfAlphaLevel.add(new Clause(Sugar.list(clauseLit)));
            }
        }
        ProgramSolver gps = new ProgramSolver();
        return gps.solve(Sugar.union(copyOfAlphaLevel, strictAlphaCut)) == null;
    }

    private Set<Literal> findPositiveConsequence(Set<Literal> evidence, Set<Literal> state, double penaltyOfMapWorld) throws MLNContradictionException{
        MarkovLogic mlnCopy1 = mln.makeCopy();
        for (Literal l : evidence){
            mlnCopy1.addHardRule(new Clause(l));
        }
        Map<Term,Pair<Term,Integer>> partitioning = partitionExchangeable(mlnCopy1);
        Closed closedEntailed = new Closed();
        Closed closedNotEntailed = new Closed();

        Set<Literal> candidates = this.quicklyPrefilterPositiveConsequence(evidence, state, penaltyOfMapWorld);
        Set<Literal> retVal = new HashSet<Literal>();
        MarkovLogic mlnCopy2 = this.mln.makeCopy();
        mlnCopy2.resetState(state);
        mlnCopy2.addEvidence(evidence);

        mlnCopy2.runMAPInference(this.mapInferenceIterations);
        double penaltyBefore = mlnCopy2.doublePenalty();

        for (Literal l : candidates) {
            if (isDeterministic(l)) {
                retVal.add(l);
            } else {
                Clause liftedClause = liftClause(new Clause(l), partitioning);
                //System.out.println("lc: "+liftedClause+", evidence: "+evidence+", partitioning: "+partitioning+", mlnCopy1.rules: "+mlnCopy1.rules());
                if (/*false && */closedEntailed.containsIsomorphic(liftedClause)) {
                    retVal.add(l);// TODO - optimize this - one representative should actually be enough because of lifting - need to check rest of the code
                } else if (!closedNotEntailed.containsIsomorphic(liftedClause)) {
                    if (!evidence.contains(l) && !evidence.contains(l.negation())) {

                        mlnCopy2.addEvidence(l.negation());
                        if (mlnCopy2.isConsistent()) {
                            mlnCopy2.runMAPInference(this.mapInferenceIterations);
                            double penaltyAfter = mlnCopy2.doublePenalty();
                            if (penaltyAfter > penaltyBefore) {
                                retVal.add(l);
                                closedEntailed.store(liftedClause);
                            } else {
                                closedNotEntailed.store(liftedClause);
                            }
                        } else {
                            retVal.add(l);
                            closedEntailed.store(liftedClause);
                        }
                        mlnCopy2.removeEvidence(l.negation());
                    }
                }
            }
        }
        return retVal;
    }

    private Set<Literal> findNegativeConsequence(Set<Literal> evidence, Set<Literal> state, double penaltyOfMapWorld) throws MLNContradictionException {
        Set<Literal> candidates = this.quicklyPrefilterNegativeConsequence(evidence, state, penaltyOfMapWorld);
        Set<Literal> retVal = new HashSet<Literal>();
        MarkovLogic mlnCopy = this.mln.makeCopy();
        for (Literal l : candidates) {
            if (isDeterministic(l)) {
                retVal.add(l);
            } else {
                if (!evidence.contains(l) && !evidence.contains(l.negation())) {
                    mlnCopy.resetState(state);
                    mlnCopy.addEvidence(evidence);
                    mlnCopy.runMAPInference(this.mapInferenceIterations);
                    double penaltyBefore = mlnCopy.doublePenalty();
                    mlnCopy.addEvidence(l.negation());
                    if (mlnCopy.isConsistent()) {
                        mlnCopy.runMAPInference(this.mapInferenceIterations);
                        double penaltyAfter = mlnCopy.doublePenalty();
                        if (penaltyAfter > penaltyBefore) {
                            retVal.add(l);
                        }
                    } else {
                        retVal.add(l);
                    }
                    mlnCopy.removeEvidence(l.negation());
                }
            }
        }
        return retVal;
    }

    private boolean isDeterministic(Literal l){
        return this.deterministicPredicates.contains(new Pair<String,Integer>(l.predicate(), l.arity()));
    }

    private Set<Literal> quicklyPrefilterPositiveConsequence(Set<Literal> evidence, Set<Literal> state, double penaltyOfMapWorld){
        Set<Literal> retVal = new HashSet<Literal>();
        MarkovLogic mln = this.mln.makeCopy();
        mln.resetState(state);
        mln.addEvidence(evidence);
        //for (Literal l : Sugar.setFromCollections(mln.state())){
        for (Literal l : state){
            if (isDeterministic(l)){
                retVal.add(l);
            } else {
                if (!evidence.contains(l) && !evidence.contains(l.negation())) {
                    double penaltyBefore = mln.doublePenalty();
                    mln.setState(l.negation());
                    double penaltyAfter = mln.doublePenalty();
                    if (penaltyAfter > penaltyBefore) {
                        retVal.add(l);
                    }
                    mln.setState(l);
                }
            }
        }
        return retVal;
    }

    private Set<Literal> quicklyPrefilterNegativeConsequence(Set<Literal> evidence, Set<Literal> state, double penaltyOfMapWorld){
        Set<Literal> retVal = new HashSet<Literal>();
        MarkovLogic mln = this.mln.makeCopy();
        mln.resetState(state);
        mln.addEvidence(evidence);
        for (Pair<String,Integer> predicate : mln.predicates()) {
            for (Literal l : mln.allFalseStateAtoms(predicate.r, predicate.s)) {
                if (isDeterministic(l)){
                    retVal.add(l);
                } else {
                    if (!evidence.contains(l) && !evidence.contains(l.negation())) {
                        double penaltyBefore = mln.doublePenalty();
                        mln.setState(l);
                        double penaltyAfter = mln.doublePenalty();
                        if (penaltyAfter > penaltyBefore) {
                            retVal.add(l.negation());
                        }
                        mln.setState(l.negation());
                    }
                }
            }
        }
        return retVal;
    }

    private static Map<Term,Pair<Term,Integer>> partitionExchangeable(MarkovLogic mln){
        MultiMap<Term,Term> partitioning = new MultiMap<Term, Term>();
        List<Pair<Clause,BigInteger>> rules = mln.rules();
        List<Term> constants = Sugar.arrayListFromCollections(constants(rules));
        Set<Term> closed = new HashSet<Term>();
        //quick prefiltering
        MultiList<Term,Object> constants2weights = new MultiList<Term,Object>();
        for (Pair<Clause,BigInteger> rule : rules){
            for (Term t : rule.r.terms()){
                if (t instanceof Constant){
                    constants2weights.put(t, rule.s == null ? Sugar.NIL : rule.s);
                }
            }
        }
        MultiMap<List<Object>,Term> f = new MultiMap<List<Object>,Term>();
        for (Map.Entry<Term,List<Object>> entry : constants2weights.entrySet()){
            f.put(entry.getValue(), entry.getKey());
        }
        for (Map.Entry<List<Object>,Set<Term>> entry : f.entrySet()){
            if (entry.getValue().size() == 1){
                Term t = Sugar.chooseOne(entry.getValue());
                closed.add(t);
                partitioning.put(t,t);
            }
        }
        //checking exchangeability pairwise
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
        Map<Term,Pair<Term,Integer>> retVal = new HashMap<Term,Pair<Term,Integer>>();
        for (Map.Entry<Term,Set<Term>> entry : partitioning.entrySet()){
            Term lexmin = null;
            for (Term t : entry.getValue()){
                if (lexmin == null || t.toString().compareTo(lexmin.toString()) < 0){
                    lexmin = t;
                }
            }
            for (Term t : entry.getValue()){
                retVal.put(t, new Pair<Term,Integer>(lexmin, entry.getValue().size()));
            }
        }
        return retVal;
    }

    private static boolean areExchangeable(Term a, Term b, Collection<Pair<Clause,BigInteger>> rules){
        Matching matching = new Matching();
        matching.setSubsumptionMode(Matching.OI_SUBSUMPTION);
        Map<Term,Term> substitution = new HashMap<Term,Term>();
        substitution.put(a,b);
        substitution.put(b,a);
        Counters<Pair<Clause,BigInteger>> substitutedMultiset = new Counters<Pair<Clause,BigInteger>>();
        for (Pair<Clause,BigInteger> rule : rules){
            Clause newClause = LogicUtils.substitute(rule.r, substitution);
            for (Pair<Clause,BigInteger> rule2 : rules){
                if (matching.isomorphism(rule2.r, newClause)){
                    newClause = rule2.r;
                }
            }
            substitutedMultiset.increment(new Pair<Clause,BigInteger>(newClause, rule.s));
        }
        for (Pair<Clause,BigInteger> rule : rules){
            if (substitutedMultiset.decrementPre(rule) < 0){
                return false;
            }
        }
//        outerLoop: for (Pair<Clause,BigInteger> rule : rules){
//            if (rule.r.terms().contains(a) || rule.r.terms().contains(b)) {
//                Clause newClause = LogicUtils.substitute(rule.r, substitution);
//                for (Pair<Clause,BigInteger> rule2 : rules) {
//                    if ((((rule.s == null && rule2.s == null) ||
//                            (rule.s != null && rule2.s != null && rule2.s.equals(rule.s)))) &&
//                            matching.subsumption(rule2.r, newClause)) {
//                        continue outerLoop;
//                    }
//                }
//                return false;
//            }
//        }
        return true;
    }

    private static Set<Term> constants(Collection<Pair<Clause,BigInteger>> rules){
        Set<Term> retVal = new HashSet<Term>();
        for (Pair<Clause,BigInteger> rule : rules){
            for (Term t : rule.r.terms()){
                if (t instanceof Constant){
                    retVal.add(t);
                }
            }
        }
        return retVal;
    }

    private PossibilisticLogic postprocess(PossibilisticLogic possibilisticLogic, Map<Term,Pair<Term,Integer>> exchangeable){
        PossibilisticLogic filtered = new PossibilisticLogic();
        Set<Literal> rightAuxLiterals = new HashSet<Literal>();
        Collection<Clause> hardRules = possibilisticLogic.getAlphaLevel(Double.POSITIVE_INFINITY);
        for (Clause hardRule : hardRules){
            if (hardRule.countLiterals() == 1){
                Literal literal = Sugar.chooseOne(hardRule.literals());
                if (literal.predicate().startsWith(TYPE_PREFIX)){
                    rightAuxLiterals.add(literal);
                }
            }
        }
        Clause rightAuxClause = new Clause(rightAuxLiterals);

        for (double alpha : possibilisticLogic.levels()){
            Map<Clause,Integer> lengths = new HashMap<Clause,Integer>();
            Set<Clause> alphaLevel = Sugar.setFromCollections(possibilisticLogic.getAlphaLevel(alpha));
            List<Clause> strictAlphaCut = possibilisticLogic.getStrictAlphaCut(alpha);
            for (Clause c : alphaLevel){
                lengths.put(c, c.countLiterals());
            }
            for (final Clause testedClause : Sugar.sortDesc(Sugar.listFromCollections(alphaLevel), lengths)){
                //System.out.println("Tested clause: "+testedClause+" ("+alpha+")");
                if (LogicUtils.isGround(testedClause)){
                    if (isImplied(testedClause, alphaLevel, this.doNotRemoveEntailedByLonger ? selectShorter(strictAlphaCut, testedClause) : strictAlphaCut)) {
                        alphaLevel.remove(testedClause);
                    } else {
                        filtered.add(testedClause, alpha);
                    }
                } else if (alpha < possibilisticLogic.levels().last()) {
                    alphaLevel.remove(testedClause);
                    Set<Literal> leftAuxLiterals = new HashSet<Literal>();
                    for (Literal literal : testedClause.literals()){
                        if (literal.predicate().startsWith(TYPE_PREFIX) || literal.predicate().equals(SpecialVarargPredicates.ALLDIFF)){
                            leftAuxLiterals.add(literal.negation());
                        }
                    }
                    Pair<Term[],List<Term[]>> substitution = new Matching().allSubstitutions(new Clause(leftAuxLiterals), rightAuxClause, 1);
                    //System.out.println("NUM SUBSTITUTIONS: "+substitution.s.size());
                    if (!isImplied(LogicUtils.substitute(testedClause, substitution.r, substitution.s.get(0)), alphaLevel, this.doNotRemoveEntailedByLonger ? selectShorter(strictAlphaCut, testedClause) : strictAlphaCut)) {
                        filtered.add(testedClause, alpha);
                        alphaLevel.add(testedClause); //returning it back
                    }
                } else {
                    filtered.add(testedClause, alpha); //hard rule
                }
            }
            System.out.println("Level "+alpha+" done.");
        }
        return filtered;
    }

    private static List<Clause> selectShorter(List<Clause> clauses, final Clause etalon){
        return Sugar.removeNulls(Sugar.funcall(clauses,
                new Sugar.Fun<Clause,Clause>(){
                    @Override
                    public Clause apply(Clause clause) {
                        if (clause.countLiterals() <= etalon.countLiterals()){
                            return clause;
                        } else {
                            return null;
                        }
                    }
                }));
    }

    public void setMaxEvidenceSetSize(int maxEvidenceSetSize) {
        this.maxEvidenceSetSize = maxEvidenceSetSize;
    }

    private class Closed {

        private MultiMap<Counters,Clause> closed = new MultiMap<Counters,Clause>();

        private void store(Clause clause){
            Clause internalRepresentation = toInternal(clause);
            Counters fingerprint = makeFingerprint(internalRepresentation);
            closed.put(fingerprint, internalRepresentation);
        }

        private boolean containsIsomorphic(Clause clause){
            Clause internalRepresentation = toInternal(clause);
            Counters fingerprint = makeFingerprint(internalRepresentation);
            if (LogicUtils.isGround(clause)){
                return closed.get(fingerprint).contains(clause);
            } else {
                for (Clause candidate : closed.get(fingerprint)) {
                    if (isomorphic(internalRepresentation, candidate)) {
                        return true;
                    }
                }
            }
            return false;
        }

        private Counters makeFingerprint(Clause clause){
            Counters fingerprint = new Counters();
            Counters<Triple<String,Variable,Integer>> degrees = new Counters();
            for (Literal l : clause.literals()){
                fingerprint.increment(l.predicate());
                for (int i = 0; i < l.arity(); i++){
                    if (l.get(i) instanceof Constant){
                        fingerprint.increment(new Triple<String, Term, Integer>(l.predicate(), l.get(i), i));
                    } else if (l.get(i) instanceof Variable) {
                        degrees.increment(new Triple<String,Variable,Integer>(l.predicate(), (Variable)l.get(i), i));
                    }
                }
            }
            List<Triple<String,Integer,Integer>> variableContexts = new ArrayList<Triple<String,Integer,Integer>>();
            for (Map.Entry<Triple<String,Variable,Integer>,Integer> entry : degrees.toMap().entrySet()){
                fingerprint.increment(new Triple<String,Integer,Integer>(entry.getKey().r, entry.getKey().t, entry.getValue()));
            }
            return fingerprint;
        }

        private boolean isomorphic(Clause a, Clause b){
            Matching m = new Matching();
            m.setSubsumptionMode(Matching.OI_SUBSUMPTION);
            return a.countLiterals() == b.countLiterals() && a.predicates().equals(b.predicates())
                    && m.subsumption(a,b);
        }

    }

    private boolean subIsomorphism(Clause a, Clause b){
        Matching m = new Matching();
        //m.setSubsumptionMode(Matching.OI_SUBSUMPTION);
        return a.countLiterals() <= b.countLiterals()
                && m.subsumption(toInternal(a), toInternal(b));
    }

    private Clause toInternal(Clause clause){
        List<Literal> literals = new ArrayList<Literal>();
        for (Literal l : clause.literals()){
            if (l.isNegated()/* || l.predicate().startsWith("@")*/){
                Literal newLiteral = new Literal("$"+(l.isNegated() ? "!" : "")+l.predicate(), l.arity());
                for (int i = 0; i < l.arity(); i++){
                    newLiteral.set(l.get(i), i);
                }
                literals.add(newLiteral);
            } else {
                literals.add(l);
            }
        }
        //System.out.println("internal: "+literals);
        return new Clause(literals);
    }

    public PossibilisticLogic possibilisticLogic(){
        return this.possibilisticLogic;
    }

    public Set<DefaultRule> clauseToOriginalRules(Clause clause, double penalty){
        return this.clausesToRules.get(new Pair<Clause,Double>(clause, penalty));
    }

    public void setUseShortDrowningEnforcingRules(boolean useShortDrowningEnforcingRules){
        this.shortDrowningEnforcingClauses = useShortDrowningEnforcingRules;
    }

    public void declareDeterministicPredicate(String predicate, int arity){
        this.deterministicPredicates.add(new Pair<String,Integer>(predicate, arity));
    }

    public void setDoNotRemoveEntailedByLonger(boolean doNotRemoveEntailedByLonger){
        this.doNotRemoveEntailedByLonger = doNotRemoveEntailedByLonger;
    }

}
