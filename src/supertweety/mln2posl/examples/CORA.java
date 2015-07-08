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
 * Created by kuzelkao_cardiff on 21/04/15.
 */
public class CORA {
//
//    *wrote(person,paper)
//    *refers(paper,paper)
//    category(paper,cat)
//    *sameCat(cat,cat)
//
//    1  !wrote(a1,a3) v !wrote(a1,a2) v category(a3,a4) v !category(a2,a4)
//    2  !refers(a1,a2) v category(a2,a3) v !category(a1,a3)
//    2  !refers(a1,a2) v category(a1,a3) v !category(a2,a3)
//    10  sameCat(a2,a3) v !category(a1,a3) v !category(a1,a2)
//    -3  category(a,Networking)
//    0.14  category(a1,Programming)
//    0.09  category(a1,Operating_Systems)
//    0.04  category(a1,Hardware_and_Architecture)
//    0.11  category(a1,Data_Structures__Algorithms_and_Theory)
//    0.04  category(a1,Encryption_and_Compression)
//    0.02  category(a1,Information_Retrieval)
//    0.05  category(a1,Databases)
//    0.39  category(a1,Artificial_Intelligence)
//    0.06  category(a1,Human_Computer_Interaction)
//    0.06  category(a,Networking)

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

    public static void main(String[] args) throws Exception {
        Clause r1 = Clause.parse("!wrote(per:A1,pap:A3), !wrote(per:A1,pap:A2), category(pap:A3,cat:A4), !category(pap:A2,cat:A4)");
        Clause r2 = Clause.parse("!refers(pap:A1,pap:A2), category(pap:A2,cat:A3), !category(pap:A1,cat:A3)");
        Clause r3 = Clause.parse("!refers(pap:A1,pap:A2), category(pap:A1,cat:A3), !category(pap:A2,cat:A3)");
        Clause r4 = Clause.parse("@eq(cat:A2,cat:A3), !category(pap:A1,cat:A3), !category(pap:A1,cat:A2)");
        Clause r5 = Clause.parse("category(pap:A,cat:net)");
        Clause r6 = Clause.parse("category(pap:A1,cat:prog)");
        Clause r7 = Clause.parse("category(pap:A1,cat:os)");
        Clause r8 = Clause.parse("category(pap:A1,cat:hw_arch)");
        Clause r9 = Clause.parse("category(pap:A1,cat:ds_alg_th)");
        Clause r10 = Clause.parse("category(pap:A1,cat:enc_comp)");
        Clause r11 = Clause.parse("category(pap:A1,cat:ir)");
        Clause r12 = Clause.parse("category(pap:A1,cat:db)");
        Clause r13 = Clause.parse("category(pap:A1,cat:ai)");
        Clause r14 = Clause.parse("category(pap:A1,cat:hci)");
        Clause r15 = Clause.parse("category(pap:A,cat:net)");


        Clause u1 = Clause.parse("person(per:steven)");
        Clause u2 = Clause.parse("person(per:jesse)");
        Clause u3 = Clause.parse("person(per:jan)");
        Clause u4 = Clause.parse("person(per:filip)");
        Clause u5 = Clause.parse("paper(pap:some_possibilistic_paper)");
        Clause u6 = Clause.parse("paper(pap:some_graph_mining_paper)");
        Clause u7 = Clause.parse("paper(pap:some_mln_paper)");
        Clause u8 = Clause.parse("paper(pap:some_ilp_paper)");

        MarkovLogic mln = new MarkovLogic(Sugar.<Pair<Clause, BigInteger>>list(
                new Pair<Clause, BigInteger>(r1, BigInteger.valueOf(100)),
                new Pair<Clause, BigInteger>(r2, BigInteger.valueOf(200)),
                new Pair<Clause, BigInteger>(r3, BigInteger.valueOf(200)),
                new Pair<Clause, BigInteger>(r4, /*BigInteger.valueOf(1000)*/null),
                new Pair<Clause, BigInteger>(r5, BigInteger.valueOf(-300)),
                new Pair<Clause, BigInteger>(r6, BigInteger.valueOf(14)),
                new Pair<Clause, BigInteger>(r7, BigInteger.valueOf(9)),
                new Pair<Clause, BigInteger>(r8, BigInteger.valueOf(4)),
                new Pair<Clause, BigInteger>(r9, BigInteger.valueOf(11)),
                new Pair<Clause, BigInteger>(r10, BigInteger.valueOf(4)),
                new Pair<Clause, BigInteger>(r11, BigInteger.valueOf(2)),
                new Pair<Clause, BigInteger>(r12, BigInteger.valueOf(5)),
                new Pair<Clause, BigInteger>(r13, BigInteger.valueOf(39)),
                new Pair<Clause, BigInteger>(r14, BigInteger.valueOf(6)),
                new Pair<Clause, BigInteger>(r15, BigInteger.valueOf(6)),

                new Pair<Clause, BigInteger>(u1, null),
                new Pair<Clause, BigInteger>(u2, null),
                new Pair<Clause, BigInteger>(u3, null),
                new Pair<Clause, BigInteger>(u4, null),
                new Pair<Clause, BigInteger>(u5, null),
                new Pair<Clause, BigInteger>(u6, null),
                new Pair<Clause, BigInteger>(u7, null),
                new Pair<Clause, BigInteger>(u8, null)
        ));


        System.out.println(mln.hardRules());

        mln.addTyping(Clause.parse("wrote(per:X,pap:Y), category(pap:X,cat:Y), refers(pap:X,pap:Y), sameCat(cat:X,cat:Y), person(per:X), paper(pap:X)"));

        System.out.println("state: " + mln.state());
        System.out.println("penalty: " + mln.penalty());

        ExhaustiveConvertor exhaustiveConvertor = new ExhaustiveConvertor(mln, Sugar.<Term>set());
        exhaustiveConvertor.maxEvidenceSetSize = 2;
        exhaustiveConvertor.declareDeterministicPredicate("person", 1);
        exhaustiveConvertor.declareDeterministicPredicate("paper", 1);
        exhaustiveConvertor.setDoNotRemoveEntailedByLonger(true);
        exhaustiveConvertor.setUseShortDrowningEnforcingRules(true);

        exhaustiveConvertor.convert(1000000);

        for (double level : exhaustiveConvertor.possibilisticLogic().levels()) {
            System.out.println("\n---------------------\nLevel " + level);
            for (Clause clause : exhaustiveConvertor.possibilisticLogic().getAlphaLevel(level)) {
                DefaultRule dr = Sugar.chooseOne(exhaustiveConvertor.clauseToOriginalRules(clause, level));
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

        toLatex(exhaustiveConvertor);

        System.out.println("\n-----------------------------------------------------\n");
    }

}
