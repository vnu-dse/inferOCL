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
package kodkod.engine.fol2sat;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import kodkod.ast.ConstantFormula;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Variable;
import kodkod.engine.bool.BooleanMatrix;
import kodkod.engine.bool.BooleanValue;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.util.collections.Containers;
import kodkod.util.collections.FixedMap;
import kodkod.util.ints.Ints;
import kodkod.util.nodes.AnnotatedNode;
import kodkod.util.nodes.Nodes;

/**
 * A file-based translation logger that logs translation events
 * to a temporary file.
 * @specfield formula: Formula
 * @specfield transforms: formula.*children lone-> Formula
 * @specfield bounds: Bounds
 * @specfield records: (iden ++ transforms).Formula -> BooleanValue -> Environment<BooleanMatrix>
 * @author Emina Torlak
 */
final class FileLogger extends TranslationLogger {
	
	private final FixedMap<Formula, Variable[]> logMap;
	private final AnnotatedNode<Formula> annotated;
	private final File file;
	private DataOutputStream out;
	private final TupleFactory factory;
	
	/**
	 * Constructs a new file logger from the given annotated formula.
	 * @requires broken in annotated.source[annotated.node].*children
	 * @effects this.formula' = annotated.source[annotated.node]  
	 * @effects this.transforms' = ~(annotated.source) 
	 * @effects this.bounds' = bounds
	 * @effects no this.records' 
	 */
	@SuppressWarnings("unchecked")
	FileLogger(final AnnotatedNode<Formula> annotated, Bounds bounds) {
		this.annotated = annotated;
		this.factory = bounds.universe().factory();
		try {
			this.file = File.createTempFile("kodkod", ".log");
			this.out = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(file)));
		} catch (IOException e1) {
			throw new RuntimeException(e1);
		}
		
		final Map<Formula,Set<Variable>> freeVarMap = freeVars(annotated);
		final Variable[] empty = new Variable[0];
	
		this.logMap = new FixedMap<Formula, Variable[]>(freeVarMap.keySet());	
		
		int index = 0;
		for(Map.Entry<Formula, Variable[]> e : logMap.entrySet()) {
			Set<Variable> vars = freeVarMap.get(e.getKey());
			int size = vars.size();
			if (size==0) {
				e.setValue(empty);
			} else {
				e.setValue(Containers.identitySort(vars.toArray(new Variable[size])));
			}
			index++;
		}
	}
	
	/**
	 * Returns a map from all formulas in the given annotated node to their free variables. 
	 * @return a map from all formulas in the given annotated node to their free variables.
	 */
	@SuppressWarnings("unchecked")
	private static Map<Formula,Set<Variable>> freeVars(final AnnotatedNode<Formula> annotated) {
		final Map<Formula,Set<Variable>> freeVarMap = new IdentityHashMap<Formula,Set<Variable>>();
		final FreeVariableCollector collector = new FreeVariableCollector(annotated.sharedNodes()) {
			protected Set<Variable> cache(Node node, Set<Variable> freeVars) {
				if (node instanceof Formula) {
					freeVarMap.put((Formula)node, freeVars);
				}
				return super.cache(node, freeVars);
			}
			public Set<Variable> visit(ConstantFormula constant) {
				return cache(constant, Collections.EMPTY_SET);
			}

		};
		annotated.node().accept(collector);
		return freeVarMap;
	}
	
	/**
	 * @see kodkod.engine.fol2sat.TranslationLogger#close()
	 */
	@Override
	void close() {
		try {
			if (out!=null) { out.close();  }
		} catch (IOException e1) { 	
			/* unused */
		} finally { out = null; }
	}
		
	/**
	 * Records the translation of the source of the 
	 * given transformed formula to the given boolean value 
	 * in the specified environment.
	 * @requires some this.transforms.f
	 * @effects this.records' = this.records + this.transforms.f -> translation -> freeVariables(f)<:env
	 * @throws IllegalArgumentException - no this.transforms.f
	 * @throws IllegalStateException - this log has been closed
	 */
	@Override
	void log(Formula f, BooleanValue v, Environment<BooleanMatrix> env) {
		if (out==null) throw new IllegalStateException();
	
		final int index = logMap.indexOf(f);
		if (index < 0) throw new IllegalArgumentException();
		
		final Variable[] vars = logMap.get(index);
		
		try {
			out.writeInt(index);
			out.writeInt(v.label());
			for(Variable var : vars) {
				out.writeInt(env.lookup(var).denseIndices().min());
			}
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * @see kodkod.engine.fol2sat.TranslationLogger#log()
	 */
	@Override
	TranslationLog log() {
		return new FileLog(annotated, logMap, file, factory);
	}
	
	/**
	 * @see java.lang.Object#finalize()
	 */
	protected final void finalize() {
		close();
	}

	/**
	 * A file-based translation log, written by a FileLogger.
	 * @author Emina Torlak
	 */
	private static final class FileLog extends TranslationLog {
	    private final Set<Formula> roots;
		private final Node[] indexedNodes;
	    private final Variable[][] indexedVars;
	    private final File file;
	    private final TupleFactory factory;
	   
	    /**
	     * Constructs a new file log for the sources of the given annotated formula,
	     * using the provided fixed map, file, and tuplefactory.
	     * @requires all f: annotated.node.*children & Formula | logMap.get(f) = freeVariables(f)
	     * @requires the file was written by a FileLogger using the given map
	     */
	    FileLog(AnnotatedNode<Formula> annotated, FixedMap<Formula, Variable[]> logMap, File file, TupleFactory factory) {
	    	this.file = file;
	    	this.factory = factory;
	    	this.roots = Nodes.roots((Formula) annotated.sourceOf(annotated.node()));
	    	assert roots.size() == annotated.sourceSensitiveRoots().size() ;
	    	
	    	final int size = logMap.entrySet().size();
	    	this.indexedNodes = new Node[size];
	    	this.indexedVars = new Variable[size][];
	    	int index = 0;
	    	for(Map.Entry<Formula, Variable[]> e : logMap.entrySet()) {
	    		indexedNodes[index] = annotated.sourceOf(e.getKey());
	    		indexedVars[index] = e.getValue();
	    		index++;
	    	}
	    }
	    
	    /**
	     * Deletes the log file.
	     * @see java.lang.Object#finalize()
	     */
	    protected final void finalize() {
	    	file.delete();
	    }
	    
	    /**
		 * {@inheritDoc}
		 * @see kodkod.engine.fol2sat.TranslationLog#roots()
		 */
	    public Set<Formula> roots() { return roots; } 
	    	
		/**
		 * {@inheritDoc}
		 * @see kodkod.engine.fol2sat.TranslationLog#replay(kodkod.engine.fol2sat.RecordFilter)
		 */
		public Iterator<TranslationRecord> replay(final RecordFilter filter) {
			try {	
				return new Iterator<TranslationRecord>() {
					final DataInputStream in = new DataInputStream(new BufferedInputStream(new FileInputStream(file)));
					final MutableRecord current = new MutableRecord(), next = new MutableRecord();
					long remaining = file.length();
								
					public boolean hasNext() {
						while(remaining > 0 && next.node == null) {
							try {
								final long indexLiteral = in.readLong();
								final int literal = (int) (indexLiteral);
								final int index = (int) (indexLiteral>>>32);
								final Variable[] freeVars = indexedVars[index];
								final Map<Variable,TupleSet> env;
								if (freeVars.length==0) {
									env = Collections.emptyMap();
								} else {
									env = new FixedMap<Variable,TupleSet>(freeVars);
									for(int i = 0; i < freeVars.length; i++) {
										env.put(freeVars[i], factory.setOf(1, Ints.singleton(in.readInt())));
									}
								}
								if (filter.accept(indexedNodes[index], literal, env)) {
									next.setAll(indexedNodes[index], literal, env);
								}
								remaining -= (8 + (freeVars.length << 2));
								
							} catch (IOException e) {
								throw new RuntimeException(e);
							}
						}
						return next.node != null;
					}

					public TranslationRecord next() {
						if (!hasNext()) throw new NoSuchElementException();
						return current.setAll(next);
					}

					public void remove() {	throw new UnsupportedOperationException(); }
					
					protected final void finalize() {
						try { in.close(); } catch (IOException e) { /* unused */ }
					}
				};
			} catch (FileNotFoundException e) {
				throw new RuntimeException(e);
			}	
		}		
	}
	
	/**
	 * A mutable translation record.
	 * @author Emina Torlak
	 */
	private static final class MutableRecord extends TranslationRecord {
		Node node = null; 
		int literal = 0;
		Map<Variable,TupleSet> env = null;
		
		public Map<Variable, TupleSet> env() { return env;	}
		public int literal() { return literal;	}
		public Node node() { return node; }
		void setAll(Node node, int literal, Map<Variable,TupleSet> env) {
			this.node = node;
			this.literal = literal;
			this.env = env;
		}
		TranslationRecord setAll(MutableRecord other) {
			setAll(other.node, other.literal, other.env);
			other.setAll(null,0,null);
			return this;
		}
	}

}
