#!/usr/bin/env python

from collections import deque
from itertools import izip, imap
import pdb


def matprod(A,b):
    return [sum(ai*bi for ai,bi in izip(row, b)) for row in A]

def dotprod(u,v):
    return sum(ui*vi for (ui,vi) in izip(u,v))


def getz(v):
        """Check if v is greater or equal than zero, component-wise."""
        # return all(vi>=0 for vi in v) #(Slower by a factor of 2)
        for vi in v:
            if vi<0: return False
        return True

def isz(v):
        """Check if v is zero. Slightly faster than .is_zero()"""
        # # # return all(vi>=0 for vi in v) #(Slower by a factor of 2)
        for vi in v:
            if vi!=0: return False
        return True
        # return v.is_zero()


def let(a,b):
    "True if and only if a is less or equal than b. Faster than zipping lists"
    for i in xrange(len(a)):
        if a[i]>b[i]:
            return False
    return True

def let_pp(a,b):
    "True if and only if a^+ is less than or equal b^+."
    for i in xrange(len(a)):
        if a[i]>0 and a[i]>max(b[i], 0):
            return False
    return True


def let_pm(a,b):
    "True if and only if a^+ is less or equal than b^-."
    for i in xrange(len(a)):
        if a[i]>0 and a[i]>max(-b[i], 0):
            return False
    return True

def let_mp(a,b):
    "True if and only if a^- is less or equal than b^+."
    for i in xrange(len(a)):
        if a[i]<0 and -a[i]>max(b[i], 0):
            return False
    return True

def let_mm(a,b):
    "True if and only if a^- is less or equal than b^-."
    for i in xrange(len(a)):
        if a[i]<0 and -a[i]>max(-b[i], 0):
            return False
    return True

def disjoint_pp(v, w):
    """true if v^+ and w^+ have disjoint support."""
    return not set(i for i in xrange(len(v)) if v[i]>0).intersection(
        j for j in xrange(len(w)) if w[j]>0)

def disjoint_mm(v, w):
    """true if v^- and w^- have disjoint support."""
    # return not set(i for i in xrange(len(v)) if v[i]<0).intersection(
    #     j for j in xrange(len(w)) if w[j]<0)
    return  not bool(set(i for (i,vi) in enumerate(v) if vi<0).intersection(
        j for (j,wi) in enumerate(w) if wi<0))

def max_ppp(z, u, w):
    """check that z^+ ≤ u^+ ∨ v^+"""
    for l in xrange(len(z)):
        if z[l]>0 and z[l]>max(u[l],w[l],0):
            return False
    return True
    #
    # for (l,v) in enumerate(z):
    #     if v>0 and v>max(u[l],w[l],0):
    #         return False
    # return True

def max_mmm(z, u, w):
    """check that z^- ≤ u^- ∨ v^-"""
    for l in xrange(len(z)):
        if z[l]<0 and  -z[l]>max(-u[l],-w[l],0):
            return False
    return True

def ne_max_max(z, u, w):
    """check that z^+ ∨ u^+ ≠ u^+ ∨ w^+"""
    for l in xrange(len(z)):
        if max(z[l], u[l],0) != max(u[l], w[l],0):
            return True
    return False

def ne_max_max_minus(z, u, w):
    """check that z^- ∨ u^- ≠ u^- ∨ w^-"""
    for l in xrange(len(z)):
        if max(-z[l], -u[l],0) != max(-u[l], -w[l],0):
            return True
    return False



def pm_split(v):
    """ slightly faster than pm_split2"""
    l = len(v)
    up = l*[0]
    um = l*[0]
    for i,a in enumerate(v):
        if a>0:
            up[i]=a
        else:
            um[i]=-a
    return vector(ZZ,up), vector(ZZ,um)


class PartialBasis(object):
    """docstring for PartialBasis"""
    def __init__(self, A, c, b, u):
        super(PartialBasis, self).__init__()
        self.d, self.n = A.dimensions()
        self.A = A
        self.c = c
        self.b = b
        self.u = u
        self.vectors = []
        self.cv = []
        self.Av = []
        self.pairs = []
        #
        self.vectors_p = []
        self.vectors_m = []
        self.Av_p = []
        self.Av_m = []
        #
        self.zerox = vector(ZZ,self.n*[0])
        self.zerob = vector(ZZ, self.d*[0])
        for e in identity_matrix(ZZ,self.n).rows():
            self.add_element(copy(e))



    def supports(self, v):
        p, n = [], []
        for (i,c) in enumerate(v):
            if c>0:
                p.append(i)
            elif c<0:
                n.append(i)
        return (set(p),set(n))

    def binomial_order(self, b):
        """docstring for binomial_order"""
        c = b*self.c
        minux = False
        if c<0:
            minux = True
        elif c == 0:
            for k in xrange(self.n):
                l = self.n-k-1
                if b[l]>0:
                    minux = True
                    break
                elif b[l]<0:
                    minux = False
                    break
            else:
                raise RuntimeError("Sorting the zero vector!! %s" % v)
        if minux:
            for (i,v) in enumerate(b):
                b[i] = -v
        return abs(c)



    def add_element(self, e, pos=None, pairs=True):
        """
        add element e to partial basis, update critical pairs to be computed,
        and precompute as much stuff as possible for reduction.
        """
        c = self.binomial_order(e)
        l = len(self.vectors)
        Av = self.A*e
        p,m = self.supports(e)
        Ap,Am = self.supports(Av)

        if pos is None:
            self.vectors.append(e)
            self.cv.append(c)
            self.Av.append(Av)
            self.vectors_p.append(p)
            self.vectors_m.append(m)
            self.Av_p.append(Ap)
            self.Av_m.append(Am)
        else:
            i = pos
            self.vectors[i]=e
            self.cv[i]=c
            self.Av[i]=Av
            self.vectors_p[i]=set(p)
            self.vectors_m[i]=set(m)
            self.Av_p[i]=Ap
            self.Av_m[i]=Am



        if pairs and l: # true if this is not the first vector
            for i in xrange(l):
                self.pairs.append([i,l])


    def pop_element(self, i, pairs=False):
        self.vectors.pop(i)
        self.cv.pop(i)
        self.Av.pop(i)
        self.vectors_p.pop(i)
        self.vectors_m.pop(i)
        self.Av_m.pop(i)
        self.Av_p.pop(i)
        if pairs:
            j = 0
            l = len(self.pairs)
            while j<l:
                p = self.pairs[j]
                if i==p[0] or i==p[1]:
                    self.pairs.pop(j)
                    # print "popped %s %s %s" % (j,p,i)
                    l -= 1
                elif i<p[0]:
                    self.pairs[j] = [p[0]-1, p[1]-1]
                    # print "displa %s %s %s new=%s" % (j,p,i, self.pairs[j])
                    # if self.pairs[j][1]>=len(self.vectors):print 30*"-", "problem: %s at %s %s (len=%s)" % (i,j,p, len(self.vectors))

                    j += 1
                elif p[0]<i and i<p[1]:
                    self.pairs[j] = [p[0], p[1]-1]
                    # print "contra %s %s %s new=%s" % (j,p,i, self.pairs[j])
                    # if self.pairs[j][1]>=len(self.vectors):print 30*"-", "problem: %s at %s %s (len=%s)" % (i,j,p, len(self.vectors))

                    j += 1
                else:
                    # print "nothing at %s, %s, %s" % (j,p,i)
                    j += 1


        # print len(self.vectors)
        # print self.pairs




    def criterion_1(self, i, j):
        """True if (i,j) is skipabble:
        The S-poly of the pair (i,j) is skippable if
        its leading terms are disjoint.
        """
        return not (
            bool(self.Av_p[i].intersection(self.Av_p[j])) or
            bool(self.vectors_p[i].intersection(self.vectors_p[j])) or
            bool(self.vectors_m[i].intersection(self.vectors_m[j]))
        )

    def criterion_3(self, i, j):
        """Malkin's criterion."""
        return (
            bool(self.Av_m[i].intersection(self.Av_m[j])) or
            bool(self.vectors_p[i].intersection(self.vectors_p[j])) or
            bool(self.vectors_m[i].intersection(self.vectors_m[j]))
        )


    def criterion_2(self, i, j):
        """Gebauer and Möller"""
        # it is assumed i<j
        Av = self.Av
        v = self.vectors
        for k in xrange(i):
            if  max_ppp(Av[k], Av[i], Av[j]) and max_ppp(v[k], v[i], v[j]) and max_mmm(v[k], v[i], v[j]):
                return True
        #
        for k in xrange(i+1,j):
            if  (
            max_ppp(Av[k], Av[i], Av[j]) and max_ppp(v[k], v[i], v[j]) and max_mmm(v[k], v[i], v[j])
            and
            ne_max_max(Av[k], Av[i], Av[j]) and  ne_max_max(v[k],v[i],v[j]) and ne_max_max_minus(v[k], v[i], v[j])
            ):
                return True
        #
        for k in xrange(j+1,len(self.vectors)):
            if  (
            max_ppp(Av[k], Av[i], Av[j]) and max_ppp(v[k], v[i], v[j]) and max_mmm(v[k], v[i], v[j])
            and
            ne_max_max(Av[k], Av[i], Av[j]) and  ne_max_max(v[k],v[i],v[j]) and ne_max_max_minus(v[k], v[i], v[j])
            and
            ne_max_max(Av[k], Av[j], Av[i]) and  ne_max_max(v[k],v[j],v[i]) and ne_max_max_minus(v[k], v[j], v[i])
            ):

                return True

        return False


    def reduce_by_ith(self, w, Aw, i):
        """
        It modifies s and As in place!!!

        If ±s is not reducible by vectors[i], return False.
        Else, if s is reducible by vectors[i], return ±s reduced
        as many times as possible by vectors[i].

        Note that the return value might be the zero vector, so
        test reduce_by_ith(i,j) is False for non reducibility.

        """
        round = 0
        v = self.vectors[i]
        Av = self.Av[i]

        # if isz(w): return w, Aw

        while True:
            if let_pp(Av, Aw) and let_pp(v,w) and let_mm(v,w) :
                # w is reducible
                round += 1
                # w = w-v, but modify in place.
                for k in xrange(self.n):
                    w[k]-=v[k]
                # Aw = Aw-Av
                for k in xrange(self.d):
                    Aw[k] -= Av[k]
                # # slower alternative:
                # w -= v
                # Aw -= Av
            elif let_pm(Av, Aw) and let_pm(v,w) and let_mp(v,w) :
                # -w is reducible
                round += 1
                # w = -w-v
                for k in xrange(self.n):
                    w[k]=-w[k]-v[k]
                # Aw = -A*w-A*v
                for k in xrange(self.d):
                    Aw[k] = -Aw[k]-Av[k]
                # # slower:
                # w *= -1
                # w -=v
                # Aw *= -1
                # Av -= Av
            else:
                # no reducibility
                break

        if round == 0:
            return False, False
        else:
            return w, Aw

    def reduce(self, v, by=None):
        """reduce"""
        l = len(self.vectors)
        if by is None:
            indices = deque(range(l))
        else:
            indices = deque(by)
        l = len(indices)
        i = 0
        w = v
        Aw = self.A*w
        # Aw = copy(self.zerob)
        # for k in xrange(self.d):
        #     Aw[k] = sum(self.A[k,l]*w[l] for l in xrange(self.n))
        # while i<l and not isz(w): #### TODO: Check this is ok.
        while i<l :
            r, Ar = self.reduce_by_ith(w, Aw ,indices[i])
            if r is False:
                i += 1
            else:
                # i.e, if r is a true reduction.
                # rotate the list and start over
                indices.rotate(i+1)
                i = 0
                w = r
                Aw = Ar
        return w


    def self_reduce(self):
        """self_reduce the basis."""
        b = len(self.vectors)
        i = 0
        while i<b:
            l = range(b)
            l.pop(i)
            l = deque(l)
            l.rotate(-i)
            # print i, l
            w = self.reduce(self.vectors[i], by=l)
            if isz(w):
                # remove this element
                self.pop_element(i, pairs=True) # remove the corresponding pairs
                b -= 1
            else:
                self.add_element(w,pos=i,pairs=False) # don't update the pairs
                i +=1

    def clean(self, pairs=True):
        b = len(self.vectors)
        i = 0
        while i<b:
            l = deque(xrange(b))
            l.rotate(-i)
            l.popleft()
            for (pos,k) in enumerate(l):
                if ( # self.vectors[i] is reducible
                    let_pp(self.vectors[k],self.vectors[i]) and
                    let_mm(self.vectors[k],self.vectors[i]) and
                    let_pp(self.Av[k], self.Av[i])
                ):
                    self.pop_element(i, pairs=True)
                    b -= 1
                    break
                elif (# -self.vectors[i] is reducible
                    let_pm(self.vectors[k],self.vectors[i]) and
                    let_mp(self.vectors[k],self.vectors[i]) and
                    let_pm(self.Av[k], self.Av[i])
                ):
                    w = self.reduce(self.vectors[i],by=l)
                    if isz(w):
                        self.pop_element(i, pairs=pairs)
                        b -= 1
                        break
                    else:
                        self.add_element(w,pos=i, pairs=False)
                        i +=1
                        break
            else: #for exhausted
                i += 1


    def next_pair(self):
        return self.pairs.pop()

    def pm_split(self, v):
        """ slightly faster than pm_split2"""
        up = copy(self.zerox)
        um = copy(self.zerox)
        for i,a in enumerate(v):
            if a>0:
                up[i]=a
            elif a<0:
                um[i]=-a
        return up, um

    def feasible(self, v):
        """docstring for feasible"""
        if let_pp(v,self.u) and let_mp(v,self.u):
            avp, avm = self.pm_split(v)
            return let(self.A*avp, self.b) and let(self.A*avm, self.b)
        return False


def bubu(A,b,c,u, interval=1000):
    A = matrix(ZZ,A)
    b = vector(ZZ, b)
    c = vector(ZZ,c)
    u = vector(ZZ,u)
    m, n = A.dimensions()
    conditions = [m == len(b), n == len(c), n == len(u) ]

    if not all(conditions):
        raise ValueError("Not all conditions met %s" %conditions)

    # pdb.set_trace()
    g = PartialBasis(A, c, b, u)
    c1 = 0
    c2 = 0
    c3 = 0
    rx = 0
    elig = 0
    z = 0


    while g.pairs: # or unfinished?
        # if len(g.vectors)%interval==0:
        #     print "cleaning (%s):" % len(g.vectors),
        #     g.clean()
        #     print "%s" % len(g.vectors)
    
    
        if len(g.vectors)>2000: break
        i, j = g.next_pair()

        if g.criterion_1(i,j):
            c1 += 1
            continue

        if g.criterion_3(i,j):
            c3 += 1
            continue

        # if g.criterion_2(i,j): # Gebauer and Möller criterion
        #     c2 += 1
        #     continue



        # consider u[i]-u[j]
        r = copy(g.zerox)
        for l in xrange(g.n):
            r[l] = g.vectors[j][l]-g.vectors[i][l]
        g.binomial_order(r)


        if g.feasible(r):
            rx +=1
            if (rx%interval) == 0:
                print "reduction: %s, basis: %s." % (rx, len(g.vectors))
                # g.clean()
                # g.self_reduce()
            c = g.reduce(r)
            if not isz(c):
                g.add_element(c)
            else:
                z += 1
        else:
            # print r
            elig += 1
            continue

    print "%s criterion 1, %s criterion 2, %s criterion 3, %s non feasible,  %s reductions, of which %s to zero" % (c1, c2, c3, elig, rx, z)
    return g.vectors, g




A1 = matrix(ZZ, [[3,1,11,2,3,5,3], [4, 5, 0, 1, 7,4, 6], [5,6,1,9,2,3,3]])
c1 = vector(ZZ, [23,15,6,7,1,53,4])
b1 = vector(ZZ, [31,27,38])
u1 = vector(ZZ, 7*[38])


B = matrix(ZZ, [
[9, 6, 6, 8, 3, 6, 2, 4, 6, 3, 9, 4, 4, 8, 6, 9, 4, 2, 8, 8],
[8, 8, 0, 5, 4, 4, 7, 0, 2, 3, 0, 6, 7, 7, 0, 6, 7, 8, 6, 0],
[0, 9, 4, 1, 2, 0, 6, 5, 8, 5, 5, 5, 0, 0, 9, 3, 1, 8, 4, 8],
[5, 0, 1, 6, 0, 7, 7, 5, 8, 0, 2, 7, 3, 9, 0, 6, 9, 8, 7, 3],
[3, 0, 2, 7, 5, 8, 1, 2, 1, 5, 7, 8, 3, 8, 4, 3, 6, 2, 9, 3],
])
c2 = vector(ZZ,[3, 2, 9, 1, 7, 5, 6, 2, 7, 8, 6, 9, 2, 6, 8, 7, 6, 2, 2, 1])
b2 = vector(ZZ, 5*[20])
u2 = vector(ZZ, 20*[1])

