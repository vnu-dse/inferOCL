/*
 * Alloy Analyzer 4 -- Copyright (c) 2006-2008, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.List;
import java.util.LinkedHashMap;
import java.util.Map;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Type;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.SubsetSig;

/**
 * Immutable; this class assigns each sig and field to some Kodkod relation or expression, then set the bounds.
 */

final class BoundsComputer {

    // It calls these A4Solution methods...
    // getFactory(), query(), a2k(), addRel(), addSig(), addField(), addFormula()

    /** Stores the reporter that will receive diagnostic messages. */
    private final A4Reporter rep;

    /** Stores the scope, bounds, and other settings necessary for performing a solve. */
    private final A4Solution sol;

    /** Stores the factory. */
    private final TupleFactory factory;

    /** Stores the computed scope for each sig. */
    private final ScopeComputer sc;

    /** Stores the upperbound for each sig. */
    private final Map<Sig,TupleSet> ub = new LinkedHashMap<Sig,TupleSet>();

    /** Stores the lowerbound for each sig. */
    private final Map<Sig,TupleSet> lb = new LinkedHashMap<Sig,TupleSet>();

    //==============================================================================================================//

    /**
     * Computes the lowerbound from bottom-up; it will also set a suitable initial value for each sig's upperbound.
     * Precondition: sig is not a builtin sig
     */
    private TupleSet computeLowerBound(List<Tuple> atoms, final PrimSig sig) throws Err {
        int n = sc.sig2scope(sig);
        TupleSet lower = factory.noneOf(1);
        for(PrimSig c:sig.children()) lower.addAll(computeLowerBound(atoms, c));
        TupleSet upper = lower.clone();
        boolean isExact = sc.isExact(sig);
        if (isExact || sig.isTopLevel()) for(n=n-upper.size(); n>0; n--) {
           Tuple atom = atoms.remove(atoms.size()-1);
           // If MUST<SCOPE and s is exact, then add fresh atoms to both LOWERBOUND and UPPERBOUND.
           // If MUST<SCOPE and s is inexact but toplevel, then add fresh atoms to the UPPERBOUND.
           if (isExact) lower.add(atom);
           upper.add(atom);
        }
        lb.put(sig, lower);
        ub.put(sig, upper);
        return lower;
    }

    //==============================================================================================================//

    /**
     * Computes the upperbound from top-down, then allocate a relation for it.
     * Precondition: sig is not a builtin sig
     */
    private void computeUpperBound(PrimSig sig) throws Err {
        // Sig's upperbound is fully computed. We recursively compute the upperbound for children...
        TupleSet x = ub.get(sig).clone();
        // We remove atoms that MUST be in a subsig
        for(PrimSig c: sig.children()) x.removeAll(lb.get(c));
        // So now X is the set of atoms that MIGHT be in this sig, but MIGHT NOT be in any particular subsig.
        // For each subsig that may need more atom, we say it could potentionally get any of the atom from X.
        for(PrimSig c: sig.children()) {
           if (sc.sig2scope(c) > lb.get(c).size()) ub.get(c).addAll(x);
           computeUpperBound(c);
        }
    }

    //==============================================================================================================//

    /** Allocate relations for nonbuiltin PrimSigs bottom-up. */
    private Expression allocatePrimSig(PrimSig sig) throws Err {
        // Recursively allocate all children expressions, and form the union of them
        Expression sum = null;
        for(PrimSig child:sig.children()) {
           Expression childexpr=allocatePrimSig(child);
           if (sum==null) { sum=childexpr; continue; }
           // subsigs are disjoint
           sol.addFormula(sum.intersection(childexpr).no(), child.isSubsig);
           sum = sum.union(childexpr);
        }
        TupleSet lower = lb.get(sig).clone(), upper = ub.get(sig).clone();
        if (sum == null) {
           // If sig doesn't have children, then sig should make a fresh relation for itself
           sum = sol.addRel(sig.label, lower, upper);
        } else if (sig.isAbstract == null) {
           // If sig has children, and sig is not abstract, then create a new relation to act as the remainder.
           for(PrimSig child:sig.children()) {
              // Remove atoms that are KNOWN to be in a subsig;
              // it's okay to mistakenly leave some atoms in, since we will never solve for the "remainder" relation directly;
              // instead, we union the remainder with the children, then solve for the combined solution.
              // (Thus, the more we can remove, the more efficient it gets, but it is not crucial for correctness)
              TupleSet childTS = sol.query(false, sol.a2k(child), false);
              lower.removeAll(childTS);
              upper.removeAll(childTS);
           }
           sum = sum.union(sol.addRel(sig.label+" remainder", lower, upper));
        }
        sol.addSig(sig, sum);
        return sum;
    }

    //==============================================================================================================//

    /** Allocate relations for SubsetSig top-down. */
    private Expression allocateSubsetSig(SubsetSig sig) throws Err {
        // We must not visit the same SubsetSig more than once, so if we've been here already, then return the old value right away
        Expression sum = sol.a2k(sig);
        if (sum!=null && sum!=Expression.NONE) return sum;
        // Recursively form the union of all parent expressions
        TupleSet ts = factory.noneOf(1);
        for(Sig parent:sig.parents) {
           Expression p = (parent instanceof PrimSig) ? sol.a2k(parent) : allocateSubsetSig((SubsetSig)parent);
           ts.addAll(sol.query(true, p, false));
           if (sum==null) sum=p; else sum=sum.union(p);
        }
        // If subset is exact, then just use the "sum" as is
        if (sig.exact) { sol.addSig(sig, sum); return sum; }
        // Allocate a relation for this subset sig, then bound it
        rep.bound("Sig "+sig+" in "+ts+"\n");
        Relation r = sol.addRel(sig.label, null, ts);
        sol.addSig(sig, r);
        // Add a constraint that it is INDEED a subset of the union of its parents
        sol.addFormula(r.in(sum), sig.isSubset);
        return r;
    }

    //==============================================================================================================//

    /** Helper method that returns the constraint that the sig has exactly "n" elements, or at most "n" elements */
    private Formula size(Sig sig, int n, boolean exact) {
        Expression a = sol.a2k(sig);
        if (n<=0) return a.no();
        if (n==1) return exact ? a.one() : a.lone();
        Formula f = exact ? Formula.TRUE : null;
        Decls d = null;
        Expression sum = null;
        while(n>0) {
           n--;
           Variable v = Variable.unary("");
           Decl dd = v.oneOf(a);
           if (d==null) d=dd; else d=dd.and(d);
           if (sum==null) sum=v; else { if (f!=null) f=v.intersection(sum).no().and(f); sum=v.union(sum); }
        }
        if (f!=null) return sum.eq(a).and(f).forSome(d); else return a.no().or(sum.eq(a).forSome(d));
    }

    //==============================================================================================================//

    /** Computes the bounds for sigs/fields, then construct a BoundsComputer object that you can query. */
    private BoundsComputer(A4Reporter rep, A4Solution sol, ScopeComputer sc, Iterable<Sig> sigs) throws Err {
        this.sc = sc;
        this.factory = sol.getFactory();
        this.rep = rep;
        this.sol = sol;
        // Figure out the sig bounds
        final Universe universe = factory.universe();
        final int atomN = universe.size();
        final List<Tuple> atoms = new ArrayList<Tuple>(atomN);
        for(int i=atomN-1; i>=0; i--) atoms.add(factory.tuple(universe.atom(i)));
        for(Sig s:sigs) if (!s.builtin && s.isTopLevel()) computeLowerBound(atoms, (PrimSig)s);
        for(Sig s:sigs) if (!s.builtin && s.isTopLevel()) computeUpperBound((PrimSig)s);
        // Bound the sigs
        for(Sig s:sigs) if (!s.builtin && s.isTopLevel()) allocatePrimSig((PrimSig)s);
        for(Sig s:sigs) if (s instanceof SubsetSig) allocateSubsetSig((SubsetSig)s);
        // Bound the fields
        for(Sig s:sigs) for(Field f:s.getFields()) if (f.definition==null) {
            boolean isOne = s.isOne!=null;
            Type t = isOne ? Sig.UNIV.type.join(f.type) : f.type;
            TupleSet ub = factory.noneOf(t.arity());
            for(List<PrimSig> p:t.fold()) {
                TupleSet upper=null;
                for(PrimSig b:p) {
                    TupleSet tmp = sol.query(true, sol.a2k(b), false);
                    if (upper==null) upper=tmp; else upper=upper.product(tmp);
                }
                ub.addAll(upper);
            }
            Relation r = sol.addRel(s.label+"."+f.label, null, ub);
            sol.addField(f, isOne ? sol.a2k(s).product(r) : r);
        }
        for(Sig s:sigs) for(Field f:s.getFields()) if (f.definition!=null) {
            Expression r = sol.a2k(f.definition);
            sol.addField(f, r);
        }
        // Add any additional SIZE constraints
        for(Sig s:sigs) if (!s.builtin) {
            Expression exp = sol.a2k(s);
            TupleSet upper = sol.query(true,exp,false), lower=sol.query(false,exp,false);
            final int n = sc.sig2scope(s);
            if (s.isOne!=null && (lower.size()!=1 || upper.size()!=1)) {
                rep.bound("Sig "+s+" in "+upper+" with size==1\n");
                sol.addFormula(exp.one(), s.isOne);
                continue;
            }
            if (s.isSome!=null && lower.size()<1) sol.addFormula(exp.some(), s.isSome);
            if (s.isLone!=null && upper.size()>1) sol.addFormula(exp.lone(), s.isLone);
            if (n<0) continue; // This means no scope was specified
            if (lower.size()==n && upper.size()==n && sc.isExact(s)) {
                rep.bound("Sig "+s+" == "+upper+"\n");
            }
            else if (sc.isExact(s)) {
                rep.bound("Sig "+s+" in "+upper+" with size=="+n+"\n");
                sol.addFormula(size(s,n,true), Pos.UNKNOWN);
            }
            else if (upper.size()<=n){
                rep.bound("Sig "+s+" in "+upper+"\n");
            }
            else {
                rep.bound("Sig "+s+" in "+upper+" with size<="+n+"\n");
                sol.addFormula(size(s,n,false), Pos.UNKNOWN);
            }
        }
    }

    //==============================================================================================================//

    /** Assign each sig and field to some Kodkod relation or expression, then set the bounds. */
    static void compute (A4Reporter rep, A4Solution sol, ScopeComputer sc, Iterable<Sig> sigs) throws Err {
        new BoundsComputer(rep, sol, sc, sigs);
    }
}
