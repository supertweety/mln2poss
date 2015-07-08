/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.mln;

import ida.ilp.logic.*;
import ida.ilp.logic.subsumption.Matching;
import ida.ilp.logic.subsumption.SpecialBinaryPredicates;
import ida.ilp.logic.subsumption.SpecialVarargPredicates;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import supertweety.logic.GroundProgramSolver;
import supertweety.logic.ProgramSolver;
import supertweety.misc.Utils;

import java.math.BigInteger;
import java.util.*;

/**
 * Created by kuzelkao_cardiff on 19/01/15.
 */
public class MarkovLogic {

    private List<Pair<Clause,BigInteger>> rules = new ArrayList<Pair<Clause,BigInteger>>();

    private Set<Literal> evidence = new HashSet<Literal>();

    private Set<Literal> state = new HashSet<Literal>();

    private Matching matching;

    private Set<Literal> deterministic = new HashSet<Literal>();

    private Set<Pair<String,Integer>> deterministicPredicates = new HashSet<Pair<String,Integer>>();

    private Set<Pair<String,Integer>> predicates = new HashSet<Pair<String,Integer>>();

    private Map<Pair<String,Integer>,String[]> typing = new HashMap<Pair<String,Integer>,String[]>();

    private int mapTimeout = Integer.MAX_VALUE;

    public MarkovLogic(){}

    public MarkovLogic(Collection<Pair<Clause,BigInteger>> rules){
        this.rules.addAll(rules);
        for (Pair<Clause,BigInteger> rule : rules){
            for (Literal l : rule.r.literals()){
                this.predicates.add(new Pair<String,Integer>(l.predicate(), l.arity()));
            }
        }
    }

    public void addEvidence(Literal l){
        Literal negL = l.negation();
        if (this.deterministic.contains(negL)){
            throw new MLNContradictionException(l+" and "+l.negation()+" cannot be deterministic literals at the same time.");
        }
        if (!this.state.contains(l) || this.state.contains(negL)) {
            this.matching = null;
        }
        if (this.state.contains(negL)){
            this.state.remove(negL);
        }
        this.state.add(l);
        this.evidence.add(l);

    }

    public void addDeterministicLiteral(Literal l){
        if (this.deterministic.contains(l.negation())){
            throw new MLNContradictionException(l+" and "+l.negation()+" cannot be deterministic literals at the same time.");
        }
        this.deterministicPredicates.add(new Pair<String,Integer>(l.predicate(), l.arity()));
        this.deterministic.add(l);
        this.state.add(l);
    }

    public void addRule(Clause rule, int weight){
        addRule(rule, BigInteger.valueOf(weight));
    }

    public void addRule(Clause rule, BigInteger weight){
        this.rules.add(new Pair<Clause,BigInteger>(rule, weight));
        for (Literal l : rule.literals()){
            this.predicates.add(new Pair<String,Integer>(l.predicate(), l.arity()));
        }
    }

    public void addHardRule(Clause rule){
        this.rules.add(new Pair<Clause, BigInteger>(rule, null));
        for (Literal l : rule.literals()){
            this.predicates.add(new Pair<String, Integer>(l.predicate(), l.arity()));
        }
    }

    public void addEvidence(Collection<Literal> c){
        for (Literal l : c){
            this.addEvidence(l);
        }
    }
    public void removeEvidence(Literal l){
        this.evidence.remove(l);
    }

    public void setState(Literal l){
        setState(l, this.state);
        this.matching = null;
    }

    public List<Pair<Clause,BigInteger>> rules(){
        return this.rules;
    }

    public List<Clause> hardRules(){
        List<Clause> retVal = new ArrayList<Clause>();
        for (Pair<Clause,BigInteger> rule : this.rules){
            if (rule.s == null){
                retVal.add(rule.r);
            }
        }
        return retVal;
    }

    public Set<Pair<String,Integer>> predicates(){
        return this.predicates;
    }

    public Set<Literal> state(){
        return this.state;
    }

    private void setState(Literal l, Set<Literal> state){
        Literal negL = l.negation();
        if (deterministic.contains(negL)){
            throw new MLNContradictionException(l+" and "+l.negation()+" cannot be deterministic literals at the same time.");
        }
        if (state.contains(negL)){
            state.remove(negL);
        }
        if (!l.isNegated()) {
            state.add(l);
        }
    }

//    private Map<Variable,Term> findSubstitution(Literal from, Literal to){
//        if (from.predicate() != to.predicate() || from.arity() != to.arity()){
//            return null;
//        }
//        Map<Variable,Term> subs = new HashMap<Variable,Term>();
//        for (int i = 0; i < from.arity(); i++){
//            if (!from.get(i).equals(to.get(i))){
//                if (from.get(i) instanceof Variable && (!subs.containsKey(from.get(i)) || subs.get(from.get(i)).equals(to.get(i)))){
//                    subs.put((Variable)from.get(i), to.get(i));
//                }
//            }
//        }
//        return subs;
//    }

    public double doublePenalty(){
        BigInteger penalty = penalty();
        return penalty == null ? Double.POSITIVE_INFINITY : penalty.doubleValue();
    }

    public BigInteger penalty(){
        return penalty(findViolatedRules());
    }

    public static BigInteger penalty(Collection<Pair<Clause,BigInteger>> violatedRules){
        BigInteger penalty = BigInteger.ZERO;
        for (Pair<Clause,BigInteger> violatedRule : violatedRules){
            if (violatedRule.s != null) {
                penalty = penalty.add(violatedRule.s);
            } else {
                return null;
            }
        }
        return penalty;
    }

    public List<Pair<Clause,BigInteger>> findViolatedRules(){
        return this.findViolatedRules(this.rules);
    }

    public List<Pair<Clause,BigInteger>> findViolatedRules(Collection<Pair<Clause,BigInteger>> rules){
        List<Pair<Clause,BigInteger>> violated = new ArrayList<Pair<Clause,BigInteger>>();
        if (matching == null) {
            matching = new Matching(Sugar.list(new Clause(state)));
        }
        for (Pair<Clause,BigInteger> rule : rules){
            if (LogicUtils.isGround(rule.r)){
                if (rule.s == null || rule.s.compareTo(BigInteger.ZERO) > 0){
                    if (matching.subsumption(Utils.flipSigns(rule.r), 0)){
                        violated.add(rule);
                    }
                } else if (rule.s.compareTo(BigInteger.ZERO) < 0){
                    for (Literal literal : rule.r.literals()){
                        if ((!literal.isNegated() && state.contains(literal)) ||
                                (literal.isNegated() && !state.contains(literal))){
                            violated.add(rule);
                            break;
                        }
                    }
                }
            } else {
                if (rule.s == null || rule.s.compareTo(BigInteger.ZERO) > 0) {
                    Pair<Term[], List<Term[]>> substitutions = matching.allSubstitutions(Utils.flipSigns(rule.r), 0, Integer.MAX_VALUE);
                    for (Term[] subs : substitutions.s) {
                        violated.add(new Pair<Clause, BigInteger>(Utils.substitute(rule.r, substitutions.r, subs), rule.s));
                    }
                } else if (rule.s.compareTo(BigInteger.ZERO) < 0) {
                    Pair<Term[], List<Term[]>> substitutions = matching.allTrueGroundings(rule.r, 0);
                    for (Term[] subs : substitutions.s) {
                        violated.add(new Pair<Clause, BigInteger>(Utils.substitute(rule.r, substitutions.r, subs), rule.s));
                    }
                }
            }
        }
        return violated;
    }

    public boolean isConsistent(){
        List<Clause> hardRules = new ArrayList<Clause>();
        for (Pair<Clause,BigInteger> rule : rules){
            if (rule.s == null){
                hardRules.add(rule.r);
                hardRules.add(rule.r);
            }
        }
        ProgramSolver ps = new ProgramSolver();
        return ps.solve(hardRules, this.evidence, this.deterministic) != null;
    }

    public void runMAPInference(int iterations) {
        Set<Pair<Clause,BigInteger>> activeRules = new HashSet<Pair<Clause,BigInteger>>();
        for (int i = 0; i < iterations; i++){
            int numActiveRulesBefore = activeRules.size();

            activeRules.addAll(findViolatedRules());
            activeRules = Sugar.<Pair<Clause,BigInteger>,Pair<Clause,BigInteger>>funcallAndRemoveNulls(activeRules, new Sugar.Fun<Pair<Clause,BigInteger>,Pair<Clause,BigInteger>>(){
                @Override
                public Pair<Clause, BigInteger> apply(Pair<Clause, BigInteger> clauseBigIntegerPair) {
                    if (isGroundClauseVacuouslyTrue(clauseBigIntegerPair.r)){
                        return null;
                    } else {
                        return new Pair<Clause,BigInteger>(removeSpecialAndDeterministicPredicates(clauseBigIntegerPair.r), clauseBigIntegerPair.s);
                    }
                }
            });

            if (numActiveRulesBefore == activeRules.size()){
                break;
            }

            GroundProgramSolver gps = new GroundProgramSolver(Sugar.funcall(this.evidence, new Sugar.Fun<Literal,Clause>(){
                @Override
                public Clause apply(Literal literal) {
                    return new Clause(literal);
                }
            }), Sugar.listFromCollections(activeRules));
            gps.setOptimizationTimeout(this.mapTimeout);
            Set<Literal> newState = gps.optimize();
            if (newState == null){
                throw new MLNContradictionException();
            }
            newState.addAll(deterministic);

            Set<Literal> literalsNoLongerTrue = Sugar.setDifference(this.state, newState);
            for (Literal newTrueLiteral : newState){
                this.setState(newTrueLiteral);
            }
            for (Literal newFalseLiteral : literalsNoLongerTrue){
                if (!this.evidence.contains(newFalseLiteral)) {
                    this.setState(newFalseLiteral.negation());
                }
            }
        }
    }

    private boolean isGroundClauseVacuouslyTrue(Clause c){
        for (Literal l : c.literals()){
            if (SpecialVarargPredicates.SPECIAL_PREDICATES.contains(l.predicate()) || SpecialBinaryPredicates.SPECIAL_PREDICATES.contains(l.predicate())){
                return isSpecialGroundTrue(l);
            } else if (this.deterministicPredicates.contains(new Pair<String,Integer>(l.predicate(), l.arity()))){
                if ((!l.isNegated() && this.deterministic.contains(l)) || (l.isNegated() && !this.deterministic.contains(l.negation()))){
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
                    !this.deterministicPredicates.contains(new Pair<String,Integer>(literal.predicate(), literal.arity()))){
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

    public MarkovLogic makeCopy(){
        MarkovLogic copy = new MarkovLogic(Sugar.listFromCollections(this.rules));
        copy.evidence = Sugar.setFromCollections(this.evidence);
        copy.state = Sugar.setFromCollections(this.state);
        copy.predicates = Sugar.setFromCollections(this.predicates);
        copy.typing = Sugar.mapFromMaps(this.typing);
        return copy;
    }

    public void resetState(){
        this.state.clear();
        this.state.addAll(this.evidence);
        this.state.addAll(this.deterministic);
    }

    public void resetState(Set<Literal> newState){
        this.resetState();
        for (Literal l : newState){
            this.setState(l);
        }
    }

    public void resetEvidence(){
        this.evidence.clear();
    }

    public Set<Literal> completeState(){
        Set<Literal> retVal = new HashSet<Literal>();
        for (Pair<String,Integer> predicate : this.predicates()){
            retVal.addAll(Sugar.funcall(allAtoms(predicate.r, predicate.s), new Sugar.Fun<Literal, Literal>() {
                @Override
                public Literal apply(Literal literal) {
                    if (state.contains(literal)){
                        return literal;
                    } else {
                        return literal.negation();
                    }
                }
            }));
        }
        return retVal;
    }

    public Set<Literal> allFalseStateAtoms(String predicate, int arity){
        return Sugar.setDifference(allAtoms(predicate, arity), this.state);
    }

    private Set<Literal> allAtoms(String predicate, int arity){
        Literal literal = new Literal(predicate, arity);
        String[] typing = null;
        if ((typing = this.typing.get(new Pair<String,Integer>(predicate, arity))) == null) {
            for (int i = 0; i < arity; i++) {
                literal.set(Variable.construct("V" + (i + 1)), i);
            }
        } else {
            for (int i = 0; i < arity; i++) {
                if (typing[i] == null) {
                    literal.set(Variable.construct("V" + (i + 1)), i);
                } else {
                    literal.set(Variable.construct("V" + (i + 1), typing[i]), i);
                }
            }
        }
        Set<Constant> constants = new HashSet<Constant>();
        for (Pair<Clause,BigInteger> rule : this.rules()){
            constants.addAll(Sugar.removeNulls(Sugar.funcall(rule.r.terms(), new Sugar.Fun<Term, Constant>() {
                @Override
                public Constant apply(Term term) {
                    if (term instanceof Constant){
                        return (Constant)term;
                    } else {
                        return null;
                    }
                }
            })));
        }
        Set<Literal> constantIntroducingliterals = Sugar.funcall(constants, new Sugar.Fun<Constant,Literal>(){
            @Override
            public Literal apply(Constant constant) {
                return new Literal("@",constant);
            }
        });
        Set<Literal> retVal = new HashSet<Literal>();
        Matching m = new Matching(Sugar.<Clause>list(new Clause(constantIntroducingliterals)));
        Pair<Term[],List<Term[]>> substitutions = m.allSubstitutions(new Clause(literal.negation()), 0, Integer.MAX_VALUE);

        for (Term[] substitution : substitutions.s){
            retVal.add(LogicUtils.substitute(literal, substitutions.r, substitution));
        }
        return retVal;
    }

    public void addTyping(Clause c){
        for (Literal l : c.literals()){
            this.addTyping(l);
        }
    }

    public void addTyping(Literal literal){
        String[] typing = new String[literal.arity()];
        for (int i = 0; i < typing.length; i++){
            typing[i] = literal.get(i).type();
        }
        this.addTyping(literal.predicate(), literal.arity(), typing);
    }

    public void addTyping(String predicate, int arity, String[] typing){
        this.typing.put(new Pair<String,Integer>(predicate, arity), typing);
    }

    void declareAsDeterministic(String predicate, int arity){
        this.deterministicPredicates.add(new Pair<String,Integer>(predicate, arity));
    }

    boolean isDeterministic(String predicate, int arity){
        return this.deterministicPredicates.contains(new Pair<String,Integer>(predicate, arity));
    }

    public String rulesToMLNString(){
        return rulesToMLNString(this.rules);
    }

    public static String rulesToMLNString(List<Pair<Clause,BigInteger>> rules){
        StringBuilder sb = new StringBuilder();
        for (Pair<Clause,BigInteger> rule : rules){
            sb.append(ruleToMLNString(rule.r, rule.s)).append("\n");
        }
        return sb.toString();
    }

    public static String ruleToMLNString(Clause c, BigInteger weight){
        StringBuilder sb = new StringBuilder();
        if (weight != null){
            sb.append(weight).append("  ");
        }
        for (Literal l : c.literals()){
            sb.append(literalToMLNString(l));
            sb.append(" v ");
        }
        if (c.countLiterals() > 0) {
            sb.delete(sb.length() - 3, sb.length());
        }
        if (weight == null){
            sb.append(".");
        }
        return sb.toString();
    }

    public static String literalToMLNString(Literal l){
        Literal newLit = new Literal(l.predicate(), l.isNegated(), l.arity());
        for (int i = 0; i < l.arity(); i++){
            if (l.get(i) instanceof Constant) {
                newLit.set(LogicUtils.toVariable(l.get(i)), i);
            } else if (l.get(i) instanceof Variable){
                newLit.set(LogicUtils.toConstant(l.get(i)), i);
            }
        }
        return newLit.toString();
    }

    public static void main(String[] args) throws Exception {
        Clause evidence = Clause.parse(
                "smokes(alice1),smokes(bob1),!smokes(celine1),smokes(dave1),smokes(emily1),!smokes(fred1),smokes(greg1),!smokes(hale1)"
//                "smokes(alice1),smokes(bob1),!smokes(celine1),smokes(dave1),smokes(emily1),!smokes(fred1),smokes(greg1),!smokes(hale1),"+
//                "smokes(alice2),smokes(bob2),!smokes(celine2),smokes(dave2),smokes(emily2),!smokes(fred2),smokes(greg2),!smokes(hale2)," +
//                "smokes(alice3),smokes(bob3),!smokes(celine3),smokes(dave3),smokes(emily3),!smokes(fred3),smokes(greg3),!smokes(hale3),"+
//                "smokes(alice4),smokes(bob4),!smokes(celine4),smokes(dave4),smokes(emily4),!smokes(fred4),smokes(greg4),!smokes(hale4)"
        );
        Clause r11 = Clause.parse("!smokes(A),!friends(A,B),smokes(B)");
        Clause r2 = Clause.parse("!friends(A,B), !friends(B,C), friends(A,C)");
        Clause r31 = Clause.parse("!friends(A,B), friends(B,A)");
        Clause r32 = Clause.parse("friends(A,B), !friends(B,A)");
        Clause r4 = Clause.parse("!friends(A,A)");
        Clause r5 = Clause.parse("friends(A,B)");

        MarkovLogic m = new MarkovLogic(Sugar.<Pair<Clause,BigInteger>>list(
                new Pair<Clause,BigInteger>(r11,BigInteger.valueOf(1000)),
                //new Pair<Clause,Integer>(r2,1),
                new Pair<Clause,BigInteger>(r31,null),
                new Pair<Clause,BigInteger>(r32,null),
                new Pair<Clause,BigInteger>(r4,null),
                new Pair<Clause,BigInteger>(r5,BigInteger.valueOf(100))
            )
        );
        m.setMAPTimeout(1000);
        m.addEvidence(evidence.literals());
        System.out.println("Penalty just with the evidence: " + m.penalty());
        System.out.println("Original state:"+m.state);
        m.runMAPInference(100);
        System.out.println("Violated rules: "+m.findViolatedRules());
        System.out.println("Penalty: "+m.penalty());
        System.out.println("MAP state: "+m.state);

    }

    public void setMAPTimeout(int mapTimeout) {
        this.mapTimeout = mapTimeout;
    }
}
