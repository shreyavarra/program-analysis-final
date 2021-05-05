package hw5;

import common.ErrorMessage;
import common.Utils;
import soot.Local;
import soot.Unit;
import soot.ValueBox;
import soot.Value;
import soot.jimple.*;
import soot.toolkits.graph.DominatorsFinder;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class IntraSignAnalysis extends ForwardFlowAnalysis {
    // Maps Units to sigmas;
    Map<Unit, Sigma> sigmaAt;

    // Holds the set of local variables
    private Set<Local> locals = new HashSet<>();
    private Set<DefinitionStmt> defs = new HashSet<>();
    // The calling context for the analysis
    // Null if no context (e.g., when only running intraprocedurally)
    private Context ctx;

    // The input sigma for this analysis
    private Sigma sigma_i;

    /**
     * Constructor with no context. This is useful for testing the intraprocedural
     * analysis on its own.
     */
    IntraSignAnalysis(UnitGraph graph) {
        this(graph, null, null);
    }

    /**
     * Allows creating an intra analysis with just the context and the input sigma,
     * since the unit graph can be grabbed from the function in the context.
     */
    IntraSignAnalysis(Context ctx, Sigma sigma_i) {
        this(new ExceptionalUnitGraph(ctx.fn.getActiveBody()), ctx, sigma_i);
    }

    IntraSignAnalysis(UnitGraph graph, Context ctx, Sigma sigma_i) {
        super(graph);
        this.ctx = ctx;
        sigmaAt = new HashMap<>(graph.size() * 2 + 1);

        // Collect locals
        DominatorsFinder<Unit> df = new MHGDominatorsFinder<>(graph);
        for (Unit s : graph) {
            for (Object d : df.getDominators(s)) {
                Unit dominator = (Unit) d;
                for (ValueBox box : dominator.getDefBoxes()) {
                    if (box.getValue() instanceof Local) {
                        locals.add((Local) box.getValue());
                    }
                }
            }
        }

        for (Unit s : graph) {
            if (s instanceof DefinitionStmt) {
                defs.add((DefinitionStmt) s);
            }
        }

        // TODO: Initialize all locals at all program points to ???
        for (Unit s : graph) {
            Sigma sigma = new Sigma(locals, Sigma.L.Bottom);
            // TODO: You'll need to initialize sigma with some values before adding it
            sigmaAt.put(s, sigma);
        }

        if (sigma_i == null) {
            // TODO: Initialize sigma_i if one isn't passed in
            sigma_i = new Sigma(locals, Sigma.L.Top);
        } else {
            this.sigma_i = sigma_i;
        }


        // Collect the analysis information
        doAnalysis();

        // Report warnings after analyzing
        reportWarnings();
    }

    private static Sigma.L alpha(int i) {
        if (i == 0) {
            return Sigma.L.Z;
        } 
        if (i < 0) {
            return Sigma.L.N;
        }
        return Sigma.L.P;
    }

    /**
     * Report warnings. This will use the analysis results collected by the constructor.
     */
    private void reportWarnings() {
        System.out.println("Report warnings");
        // TODO: Implement this (raise warnings)!
        // TODO: This implementation is incorrect, but it shows how to report a warning
        for (Unit u : sigmaAt.keySet()) {
            // Reports an error for a definite negative index
            for (ValueBox b : u.getUseAndDefBoxes()) {
                Value b_val = b.getValue();
                if (b_val instanceof ArrayRef) {
                    ArrayRef b_ar = (ArrayRef) b_val;
                    Value ix_v = b_ar.getIndex();
                    if (ix_v instanceof IntConstant) {
                        int ix = ((IntConstant) ix_v).value;
                        if (ix < 0) {
                            Utils.reportWarning(u, ErrorMessage.NEGATIVE_INDEX_ERROR);
                        }
                    }

                    if (ix_v instanceof Local) {
                        Local ix_l = (Local) ix_v;
                        Sigma state = sigmaAt.get(u);
                        Sigma.L abs = state.getL(ix_l);
                        if (abs == Sigma.L.N) {
                            Utils.reportWarning(u, ErrorMessage.NEGATIVE_INDEX_ERROR);
                        }
                        if (abs == Sigma.L.Top || abs == Sigma.L.Bottom) {
                            Utils.reportWarning(u, ErrorMessage.POSSIBLE_NEGATIVE_INDEX_WARNING);
                        }
                    }
                }
            }
        }
    }

    private static Sigma.L joinOp(Sigma state, BinopExpr op) {
        Value v1 = op.getOp1();
        Value v2 = op.getOp2();
        Sigma.L v1_abs = Sigma.L.Top;
        Sigma.L v2_abs = Sigma.L.Top;
        if (v1 instanceof IntConstant) {
            int v1_int = ((IntConstant) v1).value;
            v1_abs = alpha(v1_int);
        }
        if (v2 instanceof IntConstant) {
            int v2_int = ((IntConstant) v2).value;
            v2_abs = alpha(v2_int);
        }
        if (v1 instanceof Local) {
            v1_abs = state.getL((Local) v1);
        }
        if (v2 instanceof Local) {
            v2_abs = state.getL((Local) v2);
        }

        if (v1_abs == Sigma.L.Bottom) {
            return v2_abs;
        }
        if (v2_abs == Sigma.L.Bottom) {
            return v1_abs;
        }
        if (op instanceof AddExpr) {
            if (v1_abs == Sigma.L.P && v2_abs == Sigma.L.P) {
                return Sigma.L.P;
            }
            if (v1_abs == Sigma.L.N && v2_abs == Sigma.L.N) {
                return Sigma.L.N;
            }
            if (v1_abs == Sigma.L.Z) {
                return v2_abs;
            }
            if (v2_abs == Sigma.L.Z) {
                return v1_abs;
            }
        }
        if (op instanceof SubExpr) {
            if (v1_abs == Sigma.L.P && v2_abs == Sigma.L.N) {
                return Sigma.L.P;
            }
            if (v1_abs == Sigma.L.N && v2_abs == Sigma.L.P) {
                return Sigma.L.N;
            }
            if (v1_abs == Sigma.L.Z && v2_abs == Sigma.L.P) {
                return Sigma.L.N;
            }
            if (v1_abs == Sigma.L.Z && v2_abs == Sigma.L.N) {
                return Sigma.L.P;
            }
            if (v2_abs == Sigma.L.Z) {
                return v1_abs;
            }
        }
        if (op instanceof MulExpr) {
            if (v1_abs == Sigma.L.Z || v2_abs == Sigma.L.Z) {
                return Sigma.L.Z;
            }
            if (v1_abs == Sigma.L.P && v2_abs == Sigma.L.P) {
                return Sigma.L.P;
            }
            if (v1_abs == Sigma.L.N && v2_abs == Sigma.L.N) {
                return Sigma.L.P;
            }
            if (v1_abs == Sigma.L.P && v2_abs == Sigma.L.N) {
                return Sigma.L.N;
            }
            if (v1_abs == Sigma.L.N && v2_abs == Sigma.L.P) {
                return Sigma.L.N;
            }
        }
        if (op instanceof DivExpr) {
            if (v1_abs == Sigma.L.Z) {
                return Sigma.L.Z;
            }
            if (v1_abs == Sigma.L.P && v2_abs == Sigma.L.P) {
                return Sigma.L.Top;
            }
            if (v1_abs == Sigma.L.N && v2_abs == Sigma.L.N) {
                return Sigma.L.Top;
            }
            if (v1_abs == Sigma.L.P && v2_abs == Sigma.L.N) {
                return Sigma.L.N;
            }
            if (v1_abs == Sigma.L.N && v2_abs == Sigma.L.P) {
                return Sigma.L.N;
            }
        }
        return Sigma.L.Top;
    }

    //private Static Sigma.L joinCond()

    /**
     * Run flow function for this unit
     *
     * @param inValue  The initial Sigma at this point
     * @param unit     The current Unit
     * @param outValue The updated Sigma after the flow function
     */
    @Override
    protected void flowThrough(Object inValue, Object unit, Object outValue) {
        System.out.println("Flowthrough");
        // TODO: Implement me!
        Sigma in = (Sigma) inValue;
        Sigma out = (Sigma) outValue;
        Unit node = (Unit) unit;
        copy(in, out);
        if (node instanceof DefinitionStmt) {
            DefinitionStmt dstmt = (DefinitionStmt) node;
            Value var = dstmt.getLeftOp();
            Value expr = dstmt.getRightOp();
            if (var instanceof Local && expr instanceof IntConstant) {
                Sigma.L new_abs = alpha(((IntConstant) expr).value);
                in.kill.add((Local) var);
                out.setL((Local) var, new_abs);
            }

            if (var instanceof Local && expr instanceof Local) {
                Sigma.L new_abs = in.getL((Local) expr);
                in.gen.add((Local) expr);
                in.kill.add((Local) var);
                out.setL((Local) var, new_abs);
            }
                
            if (var instanceof Local && expr instanceof BinopExpr) {
                Sigma.L new_abs = joinOp(in, (BinopExpr) expr);
                out.setL((Local) var, new_abs);
            }

            
        }
        sigmaAt.put(node, out);
    }

    /**
     * Initial flow information at the start of a method
     */
    @Override
    protected Object entryInitialFlow() {
        // TODO: Implement me!
        return new Sigma(locals, Sigma.L.Top);
    }

    /**
     * Initial flow information at each other program point
     */
    @Override
    protected Object newInitialFlow() {
        // TODO: Implement me!
        return new Sigma(locals, Sigma.L.Bottom);
    }

    /**
     * Join at a program point lifted to sets
     */
    @Override
    protected void merge(Object in1, Object in2, Object out) {
        System.out.println("Merge");
        // TODO: Implement me!
        Sigma si1 = (Sigma) in1;
        Sigma si2 = (Sigma) in2;
        Sigma sout = (Sigma) out;
        for (Local v : si1.map.keySet()) {
            Sigma.L v1_abs = si1.getL(v);
            Sigma.L v2_abs = si2.getL(v);
            Sigma.L new_abs = Sigma.join(v1_abs, v2_abs);
            sout.setL(v, new_abs);
        }
    }

    /**
     * Copy for sets
     */
    @Override
    protected void copy(Object source, Object dest) {
        // TODO: Implement me!
        Sigma source_si = (Sigma) source;
        Sigma dest_si = (Sigma) dest;
        source_si.copy(dest_si);
    }
}
