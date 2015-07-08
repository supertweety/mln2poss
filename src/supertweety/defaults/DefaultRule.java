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

import ida.ilp.logic.Clause;
import ida.ilp.logic.Term;
import ida.ilp.logic.Variable;
import ida.utils.Sugar;

import java.util.Arrays;
import java.util.Set;

/**
 * Created by kuzelkao_cardiff on 19/01/15.
 */
public class DefaultRule {

    private int hashCode;

    private Clause body, head;

    private Set<Variable> variables;

    public DefaultRule(String body, String head){
        this(Clause.parse(body), Clause.parse(head));
    }

    public DefaultRule(Clause body, Clause head){
        this.body = body;
        this.head = head;
        this.hashCode = Arrays.deepHashCode(new Clause[]{body,head});
    }

    public Clause body(){
        return this.body;
    }

    public Clause head(){
        return this.head;
    }

    public String toString(){
        return this.body+" -> "+this.head;
    }

    public boolean equals(Object o){
        if (o instanceof DefaultRule){
            DefaultRule d  = (DefaultRule)o;
            return d.head.equals(this.head) && d.body.equals(this.body);
        }
        return false;
    }

    public int hashCode(){
        return this.hashCode;
    }

    public Set<Variable> variables(){
        //return Sugar.iterable(body.variables(), head.variables());
        return (this.variables == null) ? (this.variables = Sugar.union(body.variables(), head.variables())) : this.variables;
    }

    public Iterable<Term> terms(){
        return Sugar.<Term>iterable(body.terms(), head.terms());
    }

}
