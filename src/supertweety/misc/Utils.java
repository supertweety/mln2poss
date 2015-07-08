/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package supertweety.misc;

import ida.ilp.logic.Clause;
import ida.ilp.logic.Literal;
import ida.ilp.logic.Term;

import java.util.*;

/**
 * Created by kuzelkao_cardiff on 05/02/15.
 */
public class Utils {

    public static Clause flipSigns(Clause c){
        List<Literal> literals = new ArrayList<Literal>();
        for (Literal l : c.literals()){
            literals.add(l.negation());
        }
        return new Clause(literals);
    }

    public static List<Literal> flipSigns(Collection<Literal> literals){
        List<Literal> retVal = new ArrayList<Literal>();
        for (Literal l : literals){
            retVal.add(l.negation());
        }
        return retVal;
    }

    public static Clause substitute(Clause c, Term[] variables, Term[] terms){
        Map<Term,Term> subs = new HashMap<Term,Term>();
        for (int i = 0; i < variables.length; i++){
            subs.put(variables[i], terms[i]);
        }
        return substitute(c, subs);
    }

    public static Clause substitute(Clause c, Map<? extends Term,? extends Term> substitution){
        Set<Literal> literals = new HashSet<Literal>();
        for (Literal l : c.literals()){
            Literal cl = ((Literal)l).copy();
            for (int j = 0; j < l.arity(); j++){
                if (substitution.containsKey(l.get(j))){
                    cl.set(substitution.get(l.get(j)), j);
                }
            }
            literals.add(cl);
        }
        return new Clause(literals);
    }

}
