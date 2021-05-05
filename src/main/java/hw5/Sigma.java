package hw5;

import soot.Local;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * A class to represent sets (tuples) of abstract values at a program point.
 */
public class Sigma {
    /**
     * Abstract values
     */
    enum L {
        Top, Bottom, N, P, Z;
    }

    // Maps locals to abstract values
    public Map<Local, L> map;
    public Set<Local> kill;
    public Set<Local> gen;

    /**
     * An empty sigma
     */
    public Sigma() {
        this.map = new HashMap<Local, L>();
    }

    /**
     * An initialized sigma
     * @param locals the locals at this point
     * @param initialVal initial value to use
     */
    public Sigma(Iterable<Local> locals, L initialVal) {
        this.map = new HashMap<>();
        for (Local l : locals) {
            this.map.put(l, initialVal);
        }
    }

    public L getL(Local var) {
        return this.map.get(var);
    }

    public void setL(Local var, L abs) {
        this.map.put(var, abs);
    }

    /**
     * Join for two abstract values
     */
    public static L join(L v1, L v2) {
        // TODO: Implement union
        if (v1 == L.P && v2 == L.P) {
            return L.P;
        } 
        if (v1 == L.N && v2 == L.N) {
            return L.N;
        }
        if (v1 == L.Z && v2 == L.Z) {
            return L.Z;
        }
        if (v1 == L.Bottom) {
            return v2; 
        }
        if (v2 == L.Bottom) {
            return v1;
        }
        return L.Top;
    }

    public String toString() {
        Set<Local> keys = map.keySet();
        StringBuilder str = new StringBuilder("[ ");
        for (Local key : keys) {
            str.append(key.getName()).append(": ").append(map.get(key)).append("; ");
        }
        return str + " ]";
    }

    public void copy(Sigma destSet) {
        destSet.map = new HashMap<>(map);
    }

    @Override
    public boolean equals(Object obj) {
        // TODO: Implement me!
        if (obj == null) {
            return false;
        } 
        if (this == obj) {
            return true;
        }

        return (obj instanceof Sigma) && (this.map.equals(((Sigma) obj).map));
    }

    @Override
    public int hashCode() {
        // TODO: Implement me!
        return this.map.hashCode();
    }
}