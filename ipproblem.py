#!/usr/bin/env /Users/soto/Scripts/sage -python
# encoding: utf-8

"""
Algorithms for computing test sets of Integer Programming problems.

# =========================================================
# = This is ongoing work by J. García, J. Soto y JM Ucha. =
# =========================================================

This file implements the algorithms found in the following paper:

    @article{urbaniak1997variant,
      title={A variant of the Buchberger algorithm for integer programming},
      author={Urbaniak, Regina and Weismantel, Robert and Ziegler, G{\"u}nter M},
      journal={SIAM Journal on Discrete Mathematics},
      volume={10},
      number={1},
      pages={96--108},
      year={1997},
      publisher={SIAM}
    }

You define an IP problem, such as

    P=IPProblem(c=[1,3,2], A=[[1,2,3]], b=[3], u=[1,1,1])
    print P

and then you can call functions on P. Specifically,

* `P.test_set()` computes a test set for problem `P`, using the “plain” algorithm 2.1
* `P.minimal_set()` computes the unique minimal test set for `P`, following algorithm 2.7, using reductions.
* `P.test_set_non_reducibles()` computes a test set, which might not be minimal, but better in general than the one you get with `P.test_set()`.

"""

from sage.all import *
import itertools

class IPProblem(object):
    r"""Store data from PI problem $\max\{ c^T x : Ax\leq b, 0\leq x\leq u, x intgeral \}$, and methods for computing groebner basis.

    All data, `c`, `A`, `b` and `u` are converted to vectors or matrices over Z.

    """
    def __init__(self, c, A, b, u=None):
        """Store matrix/vector versions of c, A, b and u.  Compute default bounds if `u` not given."""
        super(IPProblem, self).__init__()
        self.A = matrix(ZZ,A)
        self.b = vector(ZZ,b)
        self.c = vector(ZZ,c)
        self.minimal=None
        self.best=None
        self.non_reducible=None
        self.rows=self.A.nrows()
        self.cols=self.A.ncols()
        

        assert(len(self.b)==self.A.nrows())

        if u:
            assert(len(u)==self.A.ncols())
            self.u=vector(ZZ,u)
        else:
            l=self.A.ncols()
            self.u=vector(ZZ,l*[0])
            for i in range(l):
                # I THINK PAPER'S MISTAKEN.
                self.u[i]=min([ceil(self.b[j]/self.A[j,i])
                                for j in range(self.A.nrows())
                                   if self.A[j,i]!=0] or [0])
                                   
        self.zero=vector(ZZ, len(self.u)*[0])
        self.zerorow=vector(ZZ, self.rows*[0])
        

    def cost(self, v):
        """Compute the cost of some vector `v`"""
        return self.c*v

    def order(self, v, w):
        """
        Return `1` if `v>w`, `0` if `v==w`, and `-1`  if `v<w`.
        Both `v` and `w` are assumed to be vectors.
        """
        t=self.cost(v)-self.cost(w)
        if t==0:
            # assert(len(v)==len(w)) # remove this when stable.
            for v_i,w_i in zip(v,w):
                if v_i>w_i:
                    return 1
                elif v_i<w_i:
                    return -1
            # If we get here, they are equal.
            return 0
        else:
            return int(sign(t)) # needs to be int, so that works for cmp=order.

    def getz(self, v):
        """Check if v is greater or equal than zero, component-wise."""
        # return all(vi>=0 for vi in v)
        for vi in v:
            if vi<0: return False
        return True

    def is_feasible(self, y):
        """Return `True` if `y` is feasible for this problem"""
        x=vector(ZZ,y)
        return (self.getz(x) and self.getz(self.u-x) 
                and self.getz(self.b-self.A*x))
                
    def is_improvement(self, v):
        """Check if `v` is an improvement vector."""
        if self.order(v, self.zero)>0:
            v_p,v_m=self.pm_split(v)
            return (self.is_feasible(v_p) and self.is_feasible(v_m))
        else:
            return False

    def succ(self,v):
        """Return $v^\succ$. `v` is assumed to be a vector, so that `-v` works."""
        if self.order(v, self.zero)>=0:
            return v
        else:
            return -v

    def standard_basis(self):
        n=self.A.ncols()
        l=[]
        for i in range(n):
            e=copy(self.zero)
            e[i]=1
            l.append(e)
        # This is a mistake in the paper, I believe.
        return [e for e in l if self.is_feasible(e)]

    def pm_split(self, v):
        """Split a vector `v` into its positive and negative part, so that $v=v^+-v^-$."""
        l=len(v)
        if l==self.cols:
            p=copy(self.zero)
            m=copy(self.zero)
        else:
            p=copy(self.zerorow)
            m=copy(self.zerorow)
        for i in range(l):
            if v[i]>=0:
                p[i]=v[i]
            else:
                m[i]=-v[i]
        return p,m

    def test_set(self):
        P=prod(2*ui+1 for ui in self.u)
        verbose("Bound: %s"% P,1)
        B=self.standard_basis()
        pairs=[(i,j) for i in range(len(B)) for j in range(i+1,len(B))]
        while pairs:
            verbose("|Pairs|: %s"% len(pairs), 2)
            i,j=pairs[0]
            v,w=B[i],B[j]
            # Make sure, w is bigger than v.
            if self.order(v,w)>0:
                v,w=w,v
            w=w-v
            p,m=self.pm_split(w)
            if self.is_feasible(p) and self.is_feasible(m):
                if w not in B:
                    B.append(w)
                    verbose("|B|: %s" % len(B), 1)
                    l=len(B)-1
                    pairs+=[(i,l) for i in range(l)]
            pairs.pop(0)
        return B

    def can_reduce_by(self, v, w):
        """
        Return ±1 if `±w` can be reduced by `v`, else return None. Here, `v` is assumed
        to be an “improvement vector”.
        """
        # assert(not w.is_zero())
        vp,vm=self.pm_split(v)
        wp,wm=self.pm_split(w)
        if (self.getz(wp-vp) and
            self.getz(wm-vm)):
            Avp,Avm=self.pm_split(self.A*v)
            Awp,Awm=self.pm_split(self.A*w)
            if self.getz(Awp-Avp):
                return 1
            # # Just return a None
            # else:
            #     return False
        elif (self.getz(wm-vp) and 
                    self.getz(wp-vm)):
            Avp,Avm=self.pm_split(self.A*v)
            Awp,Awm=self.pm_split(self.A*w)                    
            if self.getz(Awm-Avp):
                return -1
        # # Just return None
        #     else:
        #         return False
        # else:
        #     return False

    def can_reduce_by_set(self, w, B):
        """
        Return a pair (index, sign) of set `B` such that `sign*w` can be reduced by
        `B[i]` or False if it isn't possible to reduce neither `w` nor `-w` by any
        vector of `B`
        """
        for (i,v) in enumerate(B):
            c=self.can_reduce_by(v,w)
            if c:
                return (i,c)
        return False


    def reduce_by(self, v, w):
        """Do the reduction. You have to check yourself if  `w` is reducible by `v`"""
        return self.succ(w-v)

    def reduce_by_set(self, w, B):
        """Reduce the vector `w` by the set of improvement vectors `B`.
        I DON'T KNOW IF, ONCE YOU REDUCE AT POSITION i, IT IS POSSIBLE
        TO HAVE REDUCTIONS IN A PREVIOUS POSITION. IF THAT'S THE CASE,
        IT SHOULD BE POSSIBLE TO REDUCE TIME ON THIS.
        """
        r=w
        reducible=True
        while reducible:
            P=self.can_reduce_by_set(r,B)
            if P:
                # verbose("->reduced by index %s" % P[0], 2)
                r=P[1]*r-B[P[0]]
                reducible=not r.is_zero()
            else:
                reducible=False
        return self.succ(r)


    def minimal_test_set(self):
        """
        Compute a minimal test set using 'reduction'.
        (Update: it now caches the result in self.minimal)

        I HAVE ELIMINATED THE POSSIBILITY OF INCLUDING THE
        ZERO VECTOR IN THE GROEBNER BASIS. I DON'T KNOW IF THIS
        DETAIL IS MISSING IN THE PAPER OR IF YOU HAVE TO
        ALLOW FOR ZERO VECTORS IN THE BASIS.

     """
        if self.minimal:
            return self.minimal
        B=self.standard_basis()
        pairs=[(i,j) for i in range(len(B)) for j in range(i+1,len(B))]
        while pairs:
            # verbose("Size of pairs: %s" % len(pairs), 2)
            # verbose("Size of set  : %s" % len(B), 2)
            i,j=pairs.pop(0)
            v,w=B[i],B[j]
            # Make sure, w is bigger than v.
            if self.order(v,w)>0:
                v,w=w,v
            w=w-v
            p,m=self.pm_split(w)
            if self.is_feasible(p) and self.is_feasible(m):
                w=self.reduce_by_set(w, B)
                # Include w, if it's not zero.
                if not w.is_zero() and w not in B:
                    B.append(w)
                    l=len(B)-1
                    pairs+=[(i,l) for i in range(l)]
                    verbose("Added %s, now %s pairs" % (w, len(pairs)), level=1)

        self.minimal=B
        return B


    def inter_reduce(self,G):
        """Compute a self-reduction of test set B"""
        B=G[:] # fast copy
        i=0
        while i<len(B) and len(B)>1:
            w=B[i]
            B2=[B[j] for j in range(len(B)) if j!=i]
            P=self.can_reduce_by_set(w,B2)
            if P:
                if P[1]>0:
                    verbose("Dropping element: %s" % B[i], 2)
                    del B[i]
                    # don't step i, we already deleted something
                else:
                    verbose("Reducing %s" % w , 2)
                    B[i]=self.reduce_by_set(w,B2)
                    verbose("Reduced to %s" % B[i])
                    if B[i].is_zero():
                        verbose("Dropping element: %s" %  B[i], 2)
                        del B[i]
                        # Don't step i
                    else:
                        i+=1 # step i, we already worked with it.
            else:
                i+=1 # step i
        return B

    def reduced_test_set(self):
        """Compute a test set, and then reduce it."""
        return self.inter_reduce(self.test_set())


    def test_set_non_reducibles(self):
        """Compute a test, following 2.10"""
        E=self.standard_basis()
        B=E[:] # fast copy
        l=0
        while l<len(B):
            verbose("Running through %s of %s" % (l, len(B)), level=1)
            w=B[l]
            for ei in E:
                if ei==w:
                    continue
                v=self.succ(w-ei)
                v_p,v_m=self.pm_split(v)
                # f=lambda vp:  self.getz(v-vp) and self.can_reduce_by(vp,v)
                if (self.is_feasible(v_p)
                    and self.is_feasible(v_m)
                    and not #any(map(f, B))
                        any(self.getz(v-vp) and self.can_reduce_by(vp,v) for vp in B)
                    ):
                    B.append(v)
                    verbose("Added %s" % v, 1)
            l+=1
        self.non_reducible=B
        return B

    def walk_to_best(self,s, path=False):
        """Given a feasible solution $s$, walk from  $s$ to the optimum. Return the optimum, or, if `path` is `True`, the full path from `s` to the optimum.
        """
        if self.best:
            return self.best
        s_0=vector(ZZ,s)
        if not self.is_feasible(s_0):
            return False
        T=self.minimal or self.non_reducible
        if not T:
            self.minimal()
        T=self.minimal
        F=[self.is_feasible(s_0+t) for t in T]
        path_l=[s_0]
        # verbose("Test set=%s"% T, 2)
        cont=True
        while cont:
            candidates=sorted(itertools.compress(T,F), cmp=self.order)
            verbose("Path so far: %s" % path_l, 1)
            verbose("Candidates : %s" % candidates,1)
            verbose("Costs      : %s" % [self.c*e for e in candidates], 1)
            if not candidates: # we already got the best...
                cont=False
                break
            best=candidates[-1]
            improved=s_0+best
            if self.order(improved,s_0)>0:
                s_0=improved
                path_l.append(s_0)
                F=[self.is_feasible(s_0+t) for t in T]
                cont=any(F)
            else:
                cont=False
        self.best=s_0
        if path:
            return path_l
        else:
            return s_0
            
    def get_feasible(self):
        """If you have computed a test set, hand out a feasible vector"""
        T=self.minimal or self.non_reducible or []
        l=0
        while l<len(T):
            vp,vm=self.pm_split(T[l])
            if not vp.is_zero():
                return vp
            if not vm.is_zero():
                return vm
        return None

    def __repr__(self):
        s= """Integer programming problem
    max\{c.x : A x <= b,  0<=x<=u\}
with
c=%s,
A=
%s,
b=%s,
u=%s."""
        return s % (self.c, self.A, self.b, self.u)


    def walkback(self, region=lambda x: True):
        """
        Start a walk back from the optimus of the regular problem
        to an optimus which is also within the region determined by
        the function `region` (Might be non-linear).
        
        >>> P=IPProblem(c=[3, 4, 3, 6, 3],A=[[3, 2, 1, 5, 7]], b=[4], u=[1,1,1,1,1] )
        >>> P.minimal_test_set()
        [(1, 0, 0, 0, 0), (0, 1, 0, 0, 0), (0, 0, 1, 0, 0), (-1, 1, 0, 0, 0), (1, 0, -1, 0, 0), (0, 1, -1, 0, 0)]
        >>> P.walk_to_best(P.get_feasible())
        (0, 1, 1, 0, 0)
        >>> P.walkback(region=lambda x: x[0]**2+x[1]**2<2)
        """
        # Sort a minimal test set by increasing cost.
        T=sorted(self.minimal_test_set(), key=self.cost)
        first_point=self.walk_to_best(self.get_feasible(), False)
        visited=[]
        current_best=False
        current_cost=False
        S=[first_point] # the first point is always feasible.
        while S:
            v=S.pop(0) # Get first in queue
            c=self.cost(v)
            
            # Cross out from future examinations
            if not v in visited:
                visited.append(v)
            # see if it's better than what we have so far
            # if self.is_feasible(v) and region(v):
            if  region(v): # we can skip feasibility, since we only include feasibles.
                if not current_cost or c<current_cost:
                    current_best,current_cost=v,c
            # Now, look at sons.
            for d in T:
                w = v-d # You'll be worsening things here.
                new_c = self.cost(w)
                if (self.is_feasible(w) and
                    not w in visited and
                    (not current_cost or new_c > current_cost)):
                    verbose("appending %s"%w, level=2)
                    S.append(w)
                    
            verbose("|S|=%d"%len(S), level=1)
        if current_cost:
            return current_best, current_cost
        else:
            return None
        
        
if __name__ == '__main__':
    import doctest
    doctest.testmod()
    
    
    