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
import ida.utils.Sugar;
import ida.utils.tuples.Pair;
import supertweety.defaults.DefaultRule;
import supertweety.defaults.LexicographicTransformation;
import supertweety.defaults.MaxEntropyTransformation;
import supertweety.mln.MarkovLogic;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * Created by kuzelkao_cardiff on 30/04/15.
 */
public class Tweety {

    public static void main(String[] args) {
        List<Set<Constant>> universe = new ArrayList<Set<Constant>>();

        universe.add(Sugar.set(Constant.construct("tweety"), Constant.construct("donald"), Constant.construct("beeper"),
                Constant.construct("huey")));

        DefaultRule a = new DefaultRule("@neq(X,tweety), bird(X)", "flies(X)");
        //DefaultRule a = new DefaultRule("bird(X)", "flies(X)");
        DefaultRule b = new DefaultRule("bird(X), antarctic(X)", "!flies(X)");
        DefaultRule c = new DefaultRule("@neq(X,Y), bird(X), bird(Y), antarctic(X), sameSpecies(X,Y)", "antarctic(Y)");

        String evidence = "bird(tweety), antarctic(tweety), bird(donald), bird(beeper), sameSpecies(tweety,beeper)";

        List<DefaultRule> rules = Sugar.list(a, b, c);

        List<Clause> hardRules = Sugar.list(
        );

        LexicographicTransformation lt = new LexicographicTransformation();

        MarkovLogic mln = lt.transform(rules,
                hardRules,
                universe
        );

        for (Pair<Clause, BigInteger> rule : mln.rules()) {
            System.out.println(rule.s + " " + rule.r);
        }


        mln.addEvidence(Clause.parse(evidence).literals());
        mln.setMAPTimeout(Integer.MAX_VALUE);
        mln.runMAPInference(100);
        System.out.println("MAP: " + mln.state());


        System.out.println("\n\n\n\n---------------------\n\n\n\n\n");

        MaxEntropyTransformation met = new MaxEntropyTransformation();

        mln = met.transform(rules,
                hardRules,
                universe
        );

        for (Pair<Clause, BigInteger> rule : mln.rules()) {
            System.out.println(rule.s + " " + rule.r);
        }


        mln.addEvidence(Clause.parse(evidence).literals());
        mln.setMAPTimeout(Integer.MAX_VALUE);
        mln.runMAPInference(100);
        System.out.println("MAP: " + mln.state());
    }
}
