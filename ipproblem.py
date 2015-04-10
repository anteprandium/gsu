# coding=utf-8

"""
Algorithms for computing test sets of Integer Programming problems.


Ongoing work by J. García, J. Soto y JM Ucha.

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
        self.lex=TermOrder('lex').compare_tuples_lex
        # self.order = self.cost_order(c)
        # self.order=self.norder
        self.minimal=None
        self.non_reducible=None

        assert(len(self.b)==self.A.nrows())

        if u:
            assert(len(u)==self.A.ncols())
            self.u=vector(ZZ,u)
        else:
            l=self.A.ncols()
            self.u=vector(ZZ,l*[0])
            for i in range(l):
                # I THINK PAPER'S MISTAKEN.
                self.u[i]=min([ ceil(self.b[j]/self.A[j,i])
                                   for j in range(self.A.nrows())
                                   if self.A[j,i]!=0] or [0])



    def order(self, v, w):
        """Return 1 if v1>=v2, -1 in other case."""
        t1=add(c_i*v_i for c_i,v_i in zip(self.c, v))
        t2=add(c_i*v_i for c_i,v_i in zip(self.c, w))
        if t1==t2:
            return self.lex(v,w)
        else:
            return int(sign(t1-t2))

    def is_feasible(self, y):
        """Return `True` if `y` is feasible for this problem"""
        x=vector(ZZ,y)
        return (all(i>=0 for i in x) and
                all(i>=0 for i in (self.u-x)) and
                all(i>=0 for i in self.b-(self.A)*x))

    def succ(self,v):
        """Return $v^\succ$. `v` is assumed to be a vector, so that `-v` works."""
        if self.order(v, len(v)*[0])>0:
            return v
        else:
            return -v

    def standard_basis(self):
        n=self.A.ncols()
        l=[]
        for i in range(n):
            e=n*[0]
            e[i]=1
            l.append(vector(ZZ,e))
        return l

    def pm_split(self, v):
        """Split a vector `v` into its positive and negative part, so that $v=v^+-v^-$. """
        l=len(v)
        p=l*[0]
        m=l*[0]
        for i in range(l):
            if v[i]>0:
                p[i]=v[i]
            else:
                m[i]=-v[i]
        return vector(ZZ,p), vector(ZZ,m)

    def test_set(self):
        B=self.standard_basis()
        pairs=[(i,j) for i in range(len(B)) for j in range(i+1,len(B))]
        while pairs:
            verbose("pairs=%s"%pairs, 3)
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
                    l=len(B)-1
                    pairs+=[(i,l) for i in range(l)]
            pairs.pop(0)
        return B

    def can_reduce_by(self, v, w):
        """Return true if `w` can be reduced by `v`. Here, `v` is assumed
            to be an “improvement vector”.
            """
        vp,vm=self.pm_split(v)
        wp,wm=self.pm_split(w)
        if (all(xi>=0 for xi in wp-vp) and
            all(xi>=0 for xi in wm-vm)):
            Avp,Avm=self.pm_split(self.A*v)
            Awp,Avm=self.pm_split(self.A*w)
            return all(xi>=0 for xi in Awp-Avp)
        else:
            return False

    def can_reduce_by_set(self, w, B):
        """Return a pair (index, sign) of set `B` such that `sign*w` can be reduced by
         `B[i]` or False if it isn't possible to reduce neither `w` nor `-w` by any
         vector of `B`
        """
        for (i,v) in enumerate(B):
            if self.can_reduce_by(v,w):
                return (i,1)
            elif self.can_reduce_by(v,-w):
                return (i,-1)
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
                r=P[1]*r-B[P[0]]
            else:
                reducible=False
        return self.succ(r)


    def minimal_test_set(self):
        """Compute a minimal test set using 'reduction'.

        I HAVE ELIMINATED THE POSSIBILITY OF INCLUDING THE
        ZERO VECTOR IN THE GROEBNER BASIS. I DON'T KNOW IF THIS
        DETAIL IS MISSING IN THE PAPER OR IF YOU HAVE TO
        ALLOW FOR ZERO VECTORS IN THE BASIS.

     """
        B=self.standard_basis()
        pairs=[(i,j) for i in range(len(B)) for j in range(i+1,len(B))]
        while pairs and len(B)<300:
            # verbose("Size of pairs: %s" % len(pairs), 2)
            # verbose("Size of set  : %s" % len(B), 2)
            i,j=pairs[0]
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
                    verbose("Added %s" % w, 2)
                    l=len(B)-1
                    pairs+=[(i,l) for i in range(l)]
            pairs.pop(0)

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
        while l<len(B) and l<50:
            verbose("Running through %s of %s" % (l, len(B)), level=1)
            w=B[l]
            for ei in E:
                if ei==w:
                    continue
                v=self.succ(w-ei)
                v_p,v_m=self.pm_split(v)
                f=lambda vp:  all(xi>=0 for xi in v-vp) and self.can_reduce_by(vp,vp)
                if (self.is_feasible(v_p)
                    and self.is_feasible(v_m)
                    and not any(map(f, B))):
                    B.append(v)
                    verbose("Added %s" % v, 1)
            l+=1
        self.non_reducible=B
        return B

    def walk_to_best(self,s, path=False):
        """Given a feasible solution $s$, walk from  $s$ to the optimum. Return the optimum, or, if `path` is `True`, the full path from `s` to the optimum.
        """
        s_0=vector(ZZ,s)
        if not self.is_feasible(s_0):
            return False
        if not self.non_reducible:
            self.test_set_non_reducibles()
        if path:
            path_l=[s_0]
        G=self.non_reducible
        F=[self.is_feasible(s_0+g) for g in G]
        verbose("G=%s\nF=%s"% (G,F), 2)
        while any(F):
            best=sorted(itertools.compress(G,F), cmp=self.order)[-1]
            verbose("best=%s"%best)
            assert(self.order(s_0+best,s_0)>=0)
            s_0=s_0+best
            if path:
                path_l.append(s_0)
            F=[self.is_feasible(s_0+g) for g in G]
        if path:
            return path_l
        else:
            return s_0

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
