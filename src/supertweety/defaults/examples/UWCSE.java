/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.defaults.examples;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Constant;
import ida.ilp.logic.Literal;
import ida.utils.Sugar;
import supertweety.defaults.DefaultRule;
import supertweety.defaults.LexicographicTransformation;
import supertweety.defaults.MaxEntropyTransformation;
import supertweety.mln.MarkovLogic;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Created by ondrejkuzelka on 26/04/15.
 */
public class UWCSE {


    public static void expm3(){
        int numPeople = 10;
        int numCourses = 10;
        int numTerms = 10;
        int numPubs = 10;

        List<Set<Constant>> universe = new ArrayList<Set<Constant>>();

        Set<Constant> people = new HashSet<Constant>();
        for (int i = 0; i < numPeople; i++){
            people.add(Constant.construct("person" + (1+i)));
        }
        universe.add(people);

        Set<Constant> courses = new HashSet<Constant>();
        for (int i = 0; i < numCourses; i++){
            courses.add(Constant.construct("course" + (1+i)));
        }
        universe.add(courses);

        Set<Constant> terms = new HashSet<Constant>();
        for (int i = 0; i < numTerms; i++){
            terms.add(Constant.construct("term" + (1+i)));
        }
        universe.add(terms);

        Set<Constant> publications = new HashSet<Constant>();
        for (int i = 0; i < numPubs; i++){
            publications.add(Constant.construct("pub" + (1 + i)));
        }
        universe.add(publications);


        DefaultRule a = new DefaultRule("professor(P), student(S)", "!advisedBy(S,P)");
        DefaultRule b = new DefaultRule("student(S1), student(S2)", "!advisedBy(S1,S2)");
        DefaultRule c = new DefaultRule("@neq(P1,P2), student(S), professor(P1), advisedBy(S,P1), professor(P2)", "!advisedBy(S,P2)");
        DefaultRule d = new DefaultRule("professor(P), student(S), publication(Pub,P), publication(Pub,S)", "advisedBy(S,P)");
        DefaultRule e = new DefaultRule("professor(P), student(S), publication(Pub,P), publication(Pub,S), tempAdvisedBy(S,P2)", "!advisedBy(S,P)");
        DefaultRule f = new DefaultRule("ta(C, S, T), taughtBy(C, P, T), student(S), professor(P)", "advisedBy(S, P)");
        DefaultRule g = new DefaultRule("ta(C, S, T), taughtBy(C, P1, T), student(S), professor(P1), tempAdvisedBy(S,P2)", "!advisedBy(S,P1)");
        DefaultRule h = new DefaultRule("@neq(S,P1,P2),advisedBy(S,P1),publication(Pub,S),publication(Pub,P1),!publication(Pub,P2)", "!advisedBy(S,P2)");
        DefaultRule i = new DefaultRule("@neq(S,P1,P2), professor(P1), professor(P2), student(S), publication(Pub,P1), publication(Pub,S), !publication(Pub,P2), ta(C, S, T), taughtBy(C, P2, T)", "!advisedBy(S,P2)");
        DefaultRule j = new DefaultRule("@neq(S,P), professor(P), student(S), publication(Pub,P), publication(Pub,S), ta(C, S, T), taughtBy(C, P, T)", "advisedBy(S,P)");

        String evidence = "professor(person1:person1), professor(person1:person2), student(person1:person3), student(person1:person4)";

        List<DefaultRule> rules = Sugar.list(a, b, c, d, e, f, g, h, i, j);

        List<Clause> hardRules = Sugar.list(
                Clause.parse("!student(X), person(X)"),
                Clause.parse("!professor(X), person(X)"),
                Clause.parse("!advisedBy(X,Y),person(X)"),
                Clause.parse("!advisedBy(X,Y),person(Y)"),
                Clause.parse("!advisedBy(X,X)"),
                Clause.parse("!professor(X),!student(X)"),
                Clause.parse("!taughtBy(X,Y,Z),course(X)"),
                Clause.parse("!taughtBy(X,Y,Z),person(Y)"),
                Clause.parse("!taughtBy(X,Y,Z),term(Z)"),
                Clause.parse("!ta(X,Y,Z),course(X)"),
                Clause.parse("!ta(X,Y,Z),person(Y)"),
                Clause.parse("!ta(X,Y,Z),term(Z)"),
                Clause.parse("!publication(X,Y),pub(X)"),
                Clause.parse("!publication(X,Y),person(Y)")
        );

        LexicographicTransformation lt = new LexicographicTransformation();

        for (Constant constant : people){
            lt.addDeterministicCWLiteral(new Literal("person", constant));
        }
        for (Constant constant : courses){
            lt.addDeterministicCWLiteral(new Literal("course", constant));
        }
        for (Constant constant : terms){
            lt.addDeterministicCWLiteral(new Literal("term", constant));
        }
        for (Constant constant : publications){
            lt.addDeterministicCWLiteral(new Literal("pub", constant));
        }

        MarkovLogic mln = lt.transform(rules,
                hardRules,
                universe
        );

        System.out.println(mln.rulesToMLNString());


        mln.addEvidence(Clause.parse(evidence).literals());
        mln.setMAPTimeout(Integer.MAX_VALUE);
        mln.runMAPInference(100);
        List<Literal> filteredState = Sugar.listFromCollections(mln.state());
        filteredState.<Literal>removeIf(new Predicate<Literal>() {
            @Override
            public boolean test(Literal literal) {
                return literal.predicate().equals("declare") || literal.predicate().equals("person") ||
                        literal.predicate().equals("term") || literal.predicate().equals("course") ||
                        literal.predicate().equals("publication");
            }
        });
        System.out.println("MAP: "+filteredState);


        System.out.println("\n\n\n\n---------------------\n\n\n\n\n");

        MaxEntropyTransformation met = new MaxEntropyTransformation();

        for (Constant constant : people){
            met.addDeterministicCWLiteral(new Literal("person", constant));
        }
        for (Constant constant : courses){
            met.addDeterministicCWLiteral(new Literal("course", constant));
        }
        for (Constant constant : terms) {
            met.addDeterministicCWLiteral(new Literal("term", constant));
        }
        for (Constant constant : publications){
            met.addDeterministicCWLiteral(new Literal("pub", constant));
        }

        mln = met.transform(rules,
                hardRules,
                universe
        );

        System.out.println(mln.rulesToMLNString());


        mln.addEvidence(Clause.parse(evidence).literals());
        mln.setMAPTimeout(Integer.MAX_VALUE);
        mln.runMAPInference(100);
        filteredState = Sugar.listFromCollections(mln.state());
        filteredState.<Literal>removeIf(new Predicate<Literal>() {
            @Override
            public boolean test(Literal literal) {
                return literal.predicate().equals("declare") || literal.predicate().equals("person") ||
                        literal.predicate().equals("term") || literal.predicate().equals("course") ||
                        literal.predicate().equals("publication");
            }
        });
        System.out.println("MAP: "+filteredState);

    }

    public static void expm2(){
        int numPeople = 10;
        int numCourses = 10;
        int numTerms = 10;
        int numPubs = 10;

        List<Set<Constant>> universe = new ArrayList<Set<Constant>>();

        Set<Constant> people = new HashSet<Constant>();
        for (int i = 0; i < numPeople; i++){
            people.add(Constant.construct("person" + (1+i)));
        }
        universe.add(people);

        Set<Constant> courses = new HashSet<Constant>();
        for (int i = 0; i < numCourses; i++){
            courses.add(Constant.construct("course" + (1+i)));
        }
        universe.add(courses);

        Set<Constant> terms = new HashSet<Constant>();
        for (int i = 0; i < numTerms; i++){
            terms.add(Constant.construct("term" + (1+i)));
        }
        universe.add(terms);

        Set<Constant> publications = new HashSet<Constant>();
        for (int i = 0; i < numPubs; i++){
            publications.add(Constant.construct("pub" + (1 + i)));
        }
        universe.add(publications);


        DefaultRule a = new DefaultRule("advisedBy(S,P1), person(P2)", "!tempAdvisedBy(S,P2)");
        DefaultRule b = new DefaultRule("advisedBy(S,P), publication(Pub,S)", "publication(Pub,P)");
//        DefaultRule c = new DefaultRule("@neq(P1,P2), advisedBy(S,P1), publication(Pub,S), publication(Pub,P1), advisedBy(S,P2)", "publication(Pub,P2)");
//        DefaultRule d = new DefaultRule("@neq(P1,P2), advisedBy(S,P1)", "!tempAdvisedBy(S,P2)");
        DefaultRule e = new DefaultRule("@neq(P1,P2), advisedBy(S,P1)", "!advisedBy(S,P2)");
        DefaultRule f = new DefaultRule("advisedBy(S,P), ta(C,S,T)", "taughtBy(C,P,T)");
        DefaultRule g = new DefaultRule("professor(P), student(S), publication(Pub,P), publication(Pub,S)", "advisedBy(S,P)");
        DefaultRule h = new DefaultRule("professor(P), student(S), publication(Pub,P), publication(Pub,S), tempAdvisedBy(S,P2)", "!advisedBy(S,P)");
        DefaultRule i = new DefaultRule("@alldiff(S1,S2,P,C,T), advisedBy(S2,P), ta(C,S2,T), ta(C, S1, T), taughtBy(C, P, T), student(S1), professor(P)", "advisedBy(S1,P)");
        DefaultRule j = new DefaultRule("@alldiff(S1,S2,P,C,T,P2), advisedBy(S2,P), ta(C,S2,T), ta(C, S1, T), taughtBy(C, P, T), student(S1), professor(P), tempAdvisedBy(S1,P2)", "!advisedBy(S1,P)");
        DefaultRule k = new DefaultRule("", "!advisedBy(S,P)");

        for (DefaultRule dr : Sugar.list(a, b, /*c, d,*/ e, f, g, h, i, j, k)){
            System.out.println(defaultToLatex(dr));
        }


        String evidence = "professor(person1:person1), professor(person1:person2), student(person1:person3), student(person1:person4)";

        List<DefaultRule> rules = Sugar.list(a, b, /*c, d,*/ e, f, g, h, i, j, k);

        List<Clause> hardRules = Sugar.list(
                Clause.parse("!student(X), person(X)"),
                Clause.parse("!professor(X), person(X)"),
                Clause.parse("!advisedBy(X,Y),student(X)"),
                Clause.parse("!advisedBy(X,Y),professor(Y)"),
                Clause.parse("!advisedBy(X,X)"),
                Clause.parse("!professor(X),!student(X)"),
                Clause.parse("!taughtBy(X,Y,Z),course(X)"),
                Clause.parse("!taughtBy(X,Y,Z),person(Y)"),
                Clause.parse("!taughtBy(X,Y,Z),term(Z)"),
                Clause.parse("!ta(X,Y,Z),course(X)"),
                Clause.parse("!ta(X,Y,Z),person(Y)"),
                Clause.parse("!ta(X,Y,Z),term(Z)"),
                Clause.parse("!publication(X,Y),pub(X)"),
                Clause.parse("!publication(X,Y),person(Y)"),
                Clause.parse("!course(X),!person(X)"),
                Clause.parse("!term(X),!person(X)"),
                Clause.parse("!term(X),!course(X)")
        );

        LexicographicTransformation lt = new LexicographicTransformation();

        for (Constant constant : people){
            lt.addDeterministicCWLiteral(new Literal("person", constant));
        }
        for (Constant constant : courses){
            lt.addDeterministicCWLiteral(new Literal("course", constant));
        }
        for (Constant constant : terms){
            lt.addDeterministicCWLiteral(new Literal("term", constant));
        }
        for (Constant constant : publications){
            lt.addDeterministicCWLiteral(new Literal("pub", constant));
        }

        MarkovLogic mln = lt.transform(rules,
                hardRules,
                universe
        );

        System.out.println(mln.rulesToMLNString());


        mln.addEvidence(Clause.parse(evidence).literals());
        mln.setMAPTimeout(Integer.MAX_VALUE);
        mln.runMAPInference(100);
        List<Literal> filteredState = Sugar.listFromCollections(mln.state());
        filteredState.<Literal>removeIf(new Predicate<Literal>() {
            @Override
            public boolean test(Literal literal) {
                return literal.predicate().equals("declare") || literal.predicate().equals("person") ||
                        literal.predicate().equals("term") || literal.predicate().equals("course") ||
                        literal.predicate().equals("publication");
            }
        });
        System.out.println("MAP: "+filteredState);


        System.out.println("\n\n\n\n---------------------\n\n\n\n\n");

        MaxEntropyTransformation met = new MaxEntropyTransformation();

        for (Constant constant : people){
            met.addDeterministicCWLiteral(new Literal("person", constant));
        }
        for (Constant constant : courses){
            met.addDeterministicCWLiteral(new Literal("course", constant));
        }
        for (Constant constant : terms) {
            met.addDeterministicCWLiteral(new Literal("term", constant));
        }
        for (Constant constant : publications){
            met.addDeterministicCWLiteral(new Literal("pub", constant));
        }

        mln = met.transform(rules,
                hardRules,
                universe
        );

        System.out.println(mln.rulesToMLNString());


        mln.addEvidence(Clause.parse(evidence).literals());
        mln.setMAPTimeout(Integer.MAX_VALUE);
        mln.runMAPInference(100);
        filteredState = Sugar.listFromCollections(mln.state());
        filteredState.<Literal>removeIf(new Predicate<Literal>() {
            @Override
            public boolean test(Literal literal) {
                return literal.predicate().equals("declare") || literal.predicate().equals("person") ||
                        literal.predicate().equals("term") || literal.predicate().equals("course") ||
                        literal.predicate().equals("publication");
            }
        });
        System.out.println("MAP: "+filteredState);



    }

    private static String defaultToLatex(DefaultRule dr){
        StringBuilder sb = new StringBuilder();
        sb.append(" & ");
        for (Literal literal : dr.body().literals()){
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
            sb.append(") \\wedge ");
        }
        if (sb.toString().contains(" \\wedge ")){
            sb.delete(sb.length()-" \\wedge ".length(), sb.length());
        }
        sb.append("\\snake");
        for (Literal literal : dr.head().literals()){
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
            sb.append(") \\wedge ");
        }
        if (sb.toString().contains(" \\wedge ")){
            sb.delete(sb.length()-" \\wedge ".length(), sb.length());
        }
        sb.append("\\\\");
        return sb.toString();
    }

    public static void main(String[] args) {

        expm2();

    }

}
