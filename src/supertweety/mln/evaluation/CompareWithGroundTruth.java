/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.mln.evaluation;

import ida.ilp.logic.Literal;
import ida.ilp.logic.LogicUtils;
import ida.utils.Sugar;

import java.io.FileReader;
import java.io.Reader;
import java.util.Set;

/**
 * Created by ondrejkuzelka on 03/05/15.
 */
public class CompareWithGroundTruth {

    public static Results evaluate(Reader predicted, Reader groundTruth) throws Exception {
        Set<Literal> pred = Sugar.<String,Literal>funcall(Sugar.<String>setFromCollections(Sugar.readLines(predicted)),
                new Sugar.Fun<String, Literal>() {
                    @Override
                    public Literal apply(String s) {
                        Literal l = Literal.parseLiteral(s.replaceAll("\"", ""));
                        for (int i = 0; i < l.arity(); i++) {
                            l.set(LogicUtils.unquote(l.get(i)), i);
                        }
                        return l;
                    }
                });
        Set<Literal> truth = Sugar.<String,Literal>funcall(Sugar.<String>setFromCollections(Sugar.readLines(groundTruth)),
                new Sugar.Fun<String, Literal>() {
                    @Override
                    public Literal apply(String s) {
                        Literal l = Literal.parseLiteral(s.replaceAll("\"", ""));
                        for (int i = 0; i < l.arity(); i++) {
                            l.set(LogicUtils.unquote(l.get(i)), i);
                        }
                        return l;
                    }
                });
        int tp = Sugar.intersection(pred, truth).size();
        int fp = pred.size()-tp;
        int fn = truth.size()-tp;
        int tn = Integer.MAX_VALUE;
        return new Results(fp, tp, fn, tn);
    }

    public static class Results {

        public int fp, tp, fn, tn;

        public Results(int fp, int tp, int fn, int tn){
            this.fp = fp;
            this.tp = tp;
            this.fn = fn;
            this.tn = tn;
        }

        public String toString(){
            return "fp = "+fp+", tp = "+tp+", fn = "+fn+", tn = "+tn;
        }
    }

    public static void main(String[] args) throws Exception{
        System.out.println("AI:");
        System.out.println("\tME: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/ai_out_me.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/ai_ground_truth.txt")));
        System.out.println("\tLEX: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/ai_out_lex.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/ai_ground_truth.txt")));
        System.out.println("\tUNIFORM: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/ai_out_all_ones.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/ai_ground_truth.txt")));
        System.out.println("\tTUFFY TRAINED: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/ai_out_learned.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/ai_ground_truth.txt")));

        System.out.println("SYSTEMS: ");
        System.out.println("\tME: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/systems_out_me.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/systems_ground_truth.txt")));
        System.out.println("\tLEX: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/systems_out_lex.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/systems_ground_truth.txt")));
        System.out.println("\tUNIFORM: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/systems_out_all_ones.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/systems_ground_truth.txt")));
        System.out.println("\tTUFFY TRAINED: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/systems_out_learned.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/systems_ground_truth.txt")));

        System.out.println("GRAPHICS:");
        System.out.println("\tME: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/graphics_out_me.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/graphics_ground_truth.txt")));
        System.out.println("\tLEX: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/graphics_out_lex.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/graphics_ground_truth.txt")));
        System.out.println("\tUNIFORM: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/graphics_out_all_ones.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/graphics_ground_truth.txt")));
        System.out.println("\tTUFFY TRAINED: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/graphics_out_learned.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/graphics_ground_truth.txt")));

        System.out.println("THEORY:");
        System.out.println("\tME: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_out_me.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_ground_truth.txt")));
        System.out.println("\tLEX: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_out_lex.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_ground_truth.txt")));
        System.out.println("\tUNIFORM: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_out_all_ones.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_ground_truth.txt")));
        System.out.println("\tTUFFY TRAINED: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_out_learned.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_ground_truth.txt")));

        System.out.println("LANGUAGE:");
        System.out.println("\tME: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/language_out_me.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/language_ground_truth.txt")));
        System.out.println("\tLEX: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/language_out_lex.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/language_ground_truth.txt")));
        System.out.println("\tUNIFORM: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/language_out_all_ones.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/language_ground_truth.txt")));
        System.out.println("\tTUFFY TRAINED: "+evaluate(
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_out_learned.txt"),
                new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/theory_ground_truth.txt")));
    }
}
