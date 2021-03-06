/* 
 * Kodkod -- Copyright (c) 2005-2007, Emina Torlak
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
package kodkod.ast;

import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;



/** 
 * A formula that compares two expressions, e.g. x = y
 * 
 * @specfield left: Expression
 * @specfield right: Expression
 * @specfield op: Operator
 * @invariant children = left + right
 * @author Emina Torlak 
 */
public final class ComparisonFormula extends Formula{
    private final Expression left;
    private final Expression right;
    private final Operator op;
    
    /**  
     * Constructs a new comparison formula: left op  right
     * 
     * @effects this.left' = left && this.right' = right && this.op' = op
     * * @throws NullPointerException - left = null || right = null || op = null
     * @throws IllegalArgumentException - left.arity != right.arity
     */
    ComparisonFormula(Expression left, Operator op, Expression right) {
        if (!op.applicable(left.arity(), right.arity())) {
            throw new IllegalArgumentException(
            		"Arity mismatch: " + left + "::" + left.arity() + 
                    " and " + right + "::" + right.arity());
        }
        this.left = left;
        this.right = right;
        this.op = op;
    }

    /**
     * Returns the left child of this.
     * @return this.left
     */
    public Expression left() {return left;}
    
    /**
     * Returns the right child of this.
     * @return this.right
     */
    public Expression right() {return right;}
    
    /**
     * Returns the operator of this.
     * @return this.op
     */
    public Operator op() {return op;}
    
    /**
     * Accepts the given visitor and returns the result.
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.ReturnVisitor)
     */
    public <E, F, D, I> F accept(ReturnVisitor<E, F, D, I> visitor) {
        return visitor.visit(this);
    }
  
    
    /**
     * Accepts the given visitor.
     * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
     */
    public void accept(VoidVisitor visitor) {
        visitor.visit(this);
    }

    /**
	 * Returns the string representation of this formula.
	 * @return string representation of this formula
	 */
    public String toString() {
        return "(" + left + " " + op + " " + right + ")";
    }
    
    /**
     * Represents a comparison operator; e.g. "in" or "=".
     */
    public static enum Operator implements BinaryOperator<Expression,Formula>{
    	/** Subset operator (in). */
        SUBSET { 
        	public String toString() { return "in"; }
        	/** 
			 * Returns false.
			 * @return false
			 **/
			public boolean commutative() { return false; }
			
        },
        /** Equality operator (=). */
        EQUALS { 
        	public String toString() { return "="; }
        	/** 
			 * Returns true.
			 * @return true
			 **/
			public boolean commutative() { return true; }
        };
        
        /**
         * @return true if two expressions with the given arities
         * can be compared using  this operator; otherwise returns false.  This
         * method assumes that leftArity and rightArity are positive integers.
         */
        boolean applicable(int leftArity, int rightArity) { return leftArity==rightArity; }
        
        /** 
		 * Returns false.
		 * @return false
		 **/
		public final boolean associative() { return false; }
		
        /**
         * {@inheritDoc}
         * @see kodkod.ast.BinaryOperator#apply(java.lang.Object, java.lang.Object)
         */
        public final Formula apply(Expression left, Expression right) { 
        	return new ComparisonFormula(left, this, right);
        }
    }

}
