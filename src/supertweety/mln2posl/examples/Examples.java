/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.mln2posl.examples;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Constant;
import ida.ilp.logic.Literal;
import ida.ilp.logic.Term;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import supertweety.defaults.DefaultRule;
import supertweety.mln.MarkovLogic;
import supertweety.mln2posl.ExhaustiveConvertor;
import supertweety.possibilistic.PossibilisticLogic;

import java.math.BigInteger;

/**
 * Created by kuzelkao_cardiff on 03/03/15.
 */
public class Examples {


    private static boolean clausesAsRules = true;

    public static String latexClause(Clause clause){
        return latexIt(clause, "\\vee");
    }

    public static String latexRule(DefaultRule rule){
        return latexIt(rule.body(), "\\wedge")+" \\rightarrow "+latexIt(rule.head(), "\\vee");
    }

    private static String latexIt(Clause clause, String logicConnective){
        StringBuilder sb = new StringBuilder();
        for (Literal literal : clause.literals()){
            if (!literal.predicate().startsWith("type:")) {
                if (literal.predicate().startsWith("@")){
                    Literal newLit = new Literal(literal.predicate().substring(1), literal.arity());
                    for (int i = 0; i < literal.arity(); i++){
                        newLit.set(literal.get(i), i);
                    }
                }
                if (literal.isNegated()) {
                    sb.append(" \\neg ");
                }
                sb.append("\\textit{" + literal.predicate() + "}(");
                for (int i = 0; i < literal.arity(); i++) {

                    sb.append("\\textit{" + literal.get(i) + "}");
                    if (i < literal.arity() - 1) {
                        sb.append(", ");
                    }
                }
                sb.append(") "+logicConnective+" ");
            }
        }
        if (sb.toString().contains(" "+logicConnective+" ")){
            sb.delete(sb.length()-(" "+logicConnective+" ").length(), sb.length());
        }
        return sb.toString().replaceAll("_", "\\\\_");
    }

    public static void toLatex(ExhaustiveConvertor convertor){
        PossibilisticLogic pl = convertor.possibilisticLogic();
        System.out.println("\\begin{align*}");
        int i = 0;
        for (double level : pl.levels()){
            for (Clause rule : pl.getAlphaLevel(level)) {
                if (clausesAsRules) {
                    DefaultRule drule = Sugar.chooseOne(convertor.clauseToOriginalRules(rule, level));
                    if (drule == null){
                        System.out.println("(" + latexClause(rule) + ", \\lambda_{" + (i) + "}) \\\\");
                    } else {
                        System.out.println("(" + latexRule(drule) + ", \\lambda_{" + (i) + "}) \\\\");
                    }
                } else {
                    System.out.println("(" + latexClause(rule) + ", \\lambda_{" + (i) + "}) \\\\");
                }
            }
            i++;
        }
        System.out.println("\\end{align*}");
    }

    public static void toLatex(PossibilisticLogic pl){
        System.out.println("\\begin{align*}");
        int i = 0;
        for (double level : pl.levels()){
            for (Clause rule : pl.getAlphaLevel(level)) {
                System.out.println("("+latexClause(rule)+", \\lambda_{"+(i)+"}) \\\\");
            }
            i++;
        }
        System.out.println("\\end{align*}");
    }

    public static void main(String[] args) throws Exception {
        Clause r1 = Clause.parse("!bird(X), flies(X)");
        Clause r2 = Clause.parse("!antarctic(X),!flies(X)");
        Clause r3 = Clause.parse("!heavy(X), !flies(X)");
        Clause r4 = Clause.parse("!hasJetPack(X),flies(X)");
        Clause r5 = Clause.parse("exists(tweety)");
        MarkovLogic mln = new MarkovLogic(Sugar.<Pair<Clause, BigInteger>>list(
                new Pair<Clause, BigInteger>(r1, BigInteger.valueOf(10)),
                new Pair<Clause, BigInteger>(r2, BigInteger.valueOf(1)),
                new Pair<Clause, BigInteger>(r3, BigInteger.valueOf(10)),
                new Pair<Clause, BigInteger>(r4, BigInteger.valueOf(100)),
                new Pair<Clause, BigInteger>(r5, null)
        )
        );

        System.out.println("state: " + mln.state());
        System.out.println("penalty: " + mln.penalty());

        ExhaustiveConvertor exhaustiveConvertor = new ExhaustiveConvertor(mln, Sugar.<Term>set(Constant.construct("tweety")));
        exhaustiveConvertor.setDoNotRemoveEntailedByLonger(false);
        exhaustiveConvertor.convert(10000);

        for (double level : exhaustiveConvertor.possibilisticLogic().levels()) {
            System.out.println("\n---------------------\nLevel " + level);
            for (Clause clause : exhaustiveConvertor.possibilisticLogic().getAlphaLevel(level)) {
                System.out.println(clause);
            }
        }

        toLatex(exhaustiveConvertor);

        System.out.println("\n-----------------------------------------------------\n");

        Clause s1 = Clause.parse("!sm(A),!fr(A,B),sm(B)");
        Clause s2 = Clause.parse("!sm(A), ca(A)");
        Clause s4 = Clause.parse("!fr(A,B), fr(B,A)");
        Clause s6 = Clause.parse("!fr(A,A)");
        Clause s8 = Clause.parse("person(alice)");
        Clause s9 = Clause.parse("person(bob)");
        Clause s10 = Clause.parse("person(celine)");
        Clause s11 = Clause.parse("person(dave)");


        System.out.println(latexClause(s1));
        System.out.println(latexClause(s2));
        System.out.println(latexClause(s4));
        System.out.println(latexClause(s6));



        MarkovLogic mln2 = new MarkovLogic(Sugar.<Pair<Clause,BigInteger>>list(
                new Pair<Clause,BigInteger>(s1,BigInteger.valueOf(100)),
                new Pair<Clause,BigInteger>(s2,BigInteger.valueOf(100)),
                new Pair<Clause,BigInteger>(s4,null),
                new Pair<Clause,BigInteger>(s6,null),

                new Pair<Clause,BigInteger>(s8,null),
                new Pair<Clause,BigInteger>(s9,null),
                new Pair<Clause,BigInteger>(s10,null),
                new Pair<Clause,BigInteger>(s11,null)

        )
        );

        ExhaustiveConvertor exhaustiveConvertor2 = new ExhaustiveConvertor(mln2, Sugar.<Term>set());
        exhaustiveConvertor2.maxIters = 100000;
        exhaustiveConvertor2.maxEvidenceSetSize = 4;
        exhaustiveConvertor2.declareDeterministicPredicate("person", 1);


        exhaustiveConvertor2.convert(100000);

        for (double level : exhaustiveConvertor2.possibilisticLogic().levels()){
            System.out.println("\n---------------------\nLevel "+level);
            for (Clause clause : exhaustiveConvertor2.possibilisticLogic().getAlphaLevel(level)) {
                System.out.println(clause);
            }
        }

        toLatex(exhaustiveConvertor2);

        System.out.println("\n\n------\n\n");

        for (double level : exhaustiveConvertor2.possibilisticLogic().levels()) {
            System.out.println("\n---------------------\nLevel " + level);
            for (Clause clause : exhaustiveConvertor2.possibilisticLogic().getAlphaLevel(level)) {
                DefaultRule dr = Sugar.chooseOne(exhaustiveConvertor2.clauseToOriginalRules(clause, level));
                if (dr != null){
                    System.out.println(Sugar.removeNulls(Sugar.<Literal, Literal>funcall(dr.body().literals(), new Sugar.Fun<Literal, Literal>() {
                        @Override
                        public Literal apply(Literal literal) {
                            if (literal.predicate().startsWith("type:")) {
                                return literal;//null;
                            } else {
                                return literal;
                            }
                        }
                    }))+" --> "+
                            dr.head());
                } else {
                    System.out.println(Sugar.removeNulls(Sugar.<Literal, Literal>funcall(clause.literals(), new Sugar.Fun<Literal, Literal>() {
                        @Override
                        public Literal apply(Literal literal) {
                            if (literal.predicate().startsWith("type:")) {
                                return literal;//null;
                            } else {
                                return literal;
                            }
                        }
                    })));
                }
            }
        }
    }

}
