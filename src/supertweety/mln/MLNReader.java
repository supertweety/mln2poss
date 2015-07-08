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

import ida.ilp.logic.Clause;
import ida.ilp.logic.Constant;
import ida.ilp.logic.Literal;
import ida.utils.StringUtils;
import ida.utils.Sugar;
import ida.utils.tuples.Pair;

import java.io.FileReader;
import java.io.Reader;
import java.math.BigInteger;
import java.util.*;

/**
 * Created by ondrejkuzelka on 02/05/15.
 */
public class MLNReader {

    private int ruleMultiplication = 1000;

    public MarkovLogic readMLN(Reader reader) throws Exception {
        Set<Literal> deterministicPredicates = new HashSet<Literal>();
        Set<Literal> queryPredicates = new HashSet<Literal>();
        List<Pair<Clause,BigInteger>> rules = new ArrayList<Pair<Clause,BigInteger>>();
        for (String line : Sugar.readLines(reader)){
            if (line.contains("//")){
                line = line.substring(0, line.indexOf("//"));
            }
            line = line.trim();
            if (line.length() > 0) {
                String prefix = line.contains(" ") ? line.substring(0, line.indexOf(" ")).trim() : line;
                if (StringUtils.isNumeric(prefix)){
                    String rest = line.substring(line.indexOf(" "));
                    Clause rule = Clause.parse(rest, 'v');
                    if (StringUtils.isInteger(prefix)){
                        rules.add(new Pair<Clause, BigInteger>(rule, new BigInteger(prefix.trim()).multiply(BigInteger.valueOf(ruleMultiplication))));
                    } else {
                        double weight = Double.parseDouble(prefix)*ruleMultiplication;
                        rules.add(new Pair<Clause,BigInteger>(rule, BigInteger.valueOf((long)weight)));
                    }
                } else {
                    Clause rule = Clause.parse(line);
                    if (line.endsWith(".")){ //hard rule
                        rules.add(new Pair<Clause,BigInteger>(rule, null));
                    } else {
                        Literal l = Sugar.chooseOne(rule.literals());
                        if (l.predicate().startsWith("*")){
                            Literal newLit = new Literal(l.predicate().substring(1), l.arity());
                            for (int i = 0; i < l.arity(); i++){
                                newLit.set(l.get(i), i);
                            }
                            deterministicPredicates.add(newLit);
                        } else {
                            queryPredicates.add(l);
                        }
                    }
                }
            }
        }
        MarkovLogic mln = new MarkovLogic(typing(rules, deterministicPredicates, queryPredicates));
        for (Literal deterministic : deterministicPredicates){
            mln.declareAsDeterministic(deterministic.predicate(), deterministic.arity());
            mln.addTyping(deterministic);
        }
        for (Literal query : queryPredicates){
            mln.addTyping(query);
        }
        return mln;
    }

    private static List<Pair<Clause,BigInteger>> typing(List<Pair<Clause,BigInteger>> rules, Set<Literal> deterministicPredicates, Set<Literal> queryPredicates){
        Map<Pair<String,Integer>,Literal> typing = new HashMap<Pair<String,Integer>,Literal>();
        for (Literal l : Sugar.iterable(deterministicPredicates, queryPredicates)){
            typing.put(new Pair<String, Integer>(l.predicate(), l.arity()), l);
        }
        List<Pair<Clause,BigInteger>> retVal = new ArrayList<Pair<Clause,BigInteger>>();
        for (Pair<Clause,BigInteger> rule : rules){
            retVal.add(new Pair<Clause,BigInteger>(typing(rule.r, typing), rule.s));
        }
        return retVal;
    }

    private static Clause typing(Clause rule, Map<Pair<String,Integer>,Literal> typing){
        List<Literal> literals = new ArrayList<Literal>();
        Pair<String,Integer> query = new Pair<String,Integer>();
        for (Literal l : rule.literals()){
            query.set(l.predicate(), l.arity());
            Literal types = typing.get(query);
            Literal newLit = new Literal(l.predicate(), l.arity());
            for (int i = 0; i < l.arity(); i++){
                newLit.set(Constant.construct(l.get(i).name(), types.get(i).name()), i);
            }
            literals.add(newLit);
        }
        return new Clause(literals);
    }

    public static void main(String[] args) throws Exception {
        MLNReader r = new MLNReader();
        MarkovLogic mln = r.readMLN(new FileReader("/Users/ondrejkuzelka/Misc/Tuffy/tuffy-0-2.3-jun2014/samples/cse/prog.mln"));
        int i = 0;
    }
}
