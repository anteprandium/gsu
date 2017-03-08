#!/usr/bin/env python

from collections import deque


def getz(v):
        """Check if v is greater or equal than zero, component-wise."""
        # return all(vi>=0 for vi in v) #(Slower by a factor of 2)
        for vi in v:
            if vi<0: return False
        return True

def isz(v):
        """Check if v is zero. Slightly faster than .is_zero()"""
        # return all(vi>=0 for vi in v) #(Slower by a factor of 2)
        for vi in v:
            if vi!=0: return False
        return True


def let(a,b):
    "True if and only if a is less or equal than b. Faster than zipping lists by a factor of 100"
    for i in xrange(len(a)):
        if a[i]>b[i]:
            return False
    return True



def standard_basis(n):
    return identity_matrix(ZZ,n).rows()



# def pm_split3(v):
#     "Split a vector `v` into its positive and negative part, so that $v=v^-v^-$."
#     up = []
#     um = []
#     for a in v:
#         if a>=0:
#             up.append(a)
#             um.append(0)
#         else:
#             up.append(0)
#             um.append(-a)
#     return vector(ZZ,up), vector(ZZ,um)
#
#
# def pm_split2(v):
#     """ slightly faster than pm_split3"""
#     l = len(v)
#     up = [0]*l
#     um = [0]*l
#     for i in xrange(l):
#         if v[i]>0:
#             up[i]=v[i]
#         else:
#             um[i]=-v[i]
#     return vector(ZZ,up), vector(ZZ,um)
#
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
        self.n = A.dimensions()[1] 
        self.A = A
        self.c = c
        self.b = b
        self.u = u
        self.vectors = []
        self.cv = []
        self.vecp = []
        self.vecn = []
        self.pairs = []
        self.psupp = []
        self.Avp = []
        self.Avm = []
        self.eligible = []
        for e in identity_matrix(ZZ,self.n).rows():
            self.add_element(e)
    
    def add_element(self, v, check=True):
        """
        add element e to partial basis, update critical pairs to be computed, 
        and precompute as much stuff as possible for reduction.
        """
        cv = self.c*v
        e = v if cv>0 else -v  # this makes sure that e^+ >_c e^-.
        l = len(self.vectors)
        self.vectors.append(e)
        if l: # true if this is not the first vector
            for i in xrange(l):
                self.pairs.append((i,l))
        ep, em = pm_split(e)
        self.vecp.append(ep)
        self.vecn.append(em)
        self.psupp.append(set(e.support()))
        Avp, Avm = pm_split(A*e)
        self.Avp.append(Avp)
        self.Avm.append(Avm)
        self.cv.append(abs(cv))
        self.eligible.append(let(ep,self.u) and let(em,self.u) and let(A*ep,self.b) and let(A*em,self.b) )
        
        
    def criterion_1(self, i, j):
        """True if (i,j) is skipabble."""
        t = len(self.psupp[i].intersection(self.psupp[j]))==0
        return t
        
    def max(self, i, j):
        """docstring for max"""
        return vector(ZZ, [max(self.vecp[i][k],self.vecp[j][k]) for k in xrange(self.n)])
        
    def criterion_2(self, i, j):
        """Gebauer and Möller"""
        # it is assumed i<j
        t = self.max(i,j)
        indices = [k for k in range(len(self.vectors)) if k!=i and k!=j]
        for k in indices:
            if let(self.vecp[k], t):
                if k<i:
                    return True
                else:
                    y = self.max(k,i) != t
                    if i<k<j and y:
                        return True
                    elif k<j and y:
                        if self.max(k,j)!= t:
                            return True
        return False
                        
        
        
    def reduce_by_ith(self, s, i):
        """
        z is assumed to be an s-polynomial
        
        If s is not reducible by vectors[i], return False.
        Else, if s is reducible by vectors[i], return z reduced
        as many times as possible by vectors[i].
        
        Note that the return value might be the zero vector, so that
        
        
        
        """
        round = 0
        v = self.vectors[i]
        vp = self.vecp[i]
        vm = self.vecn[i]
        Avp = self.Avp[i]
        Avm = self.Avm[i]
        
        w = s
        
        # if w == v or w == -v: return vector(ZZ,self.n*[0])
    
        while True and not isz(w):
            wp, wm = pm_split(w)
            Awp, Awm = pm_split(A*w)
            if let(vp, wp) and let(vm,wm) and let(Avp, Awp): 
                # w is reducible
                round += 1
                w = w-v
            elif let(vp,wm) and let(vm,wp) and let(Avp,Awm):
                # -w is reducible
                round += 1
                w = -w-v
            else:
                # no reducibility
                break
    
        if round == 0:
            return False
        else:
            # print "%s rounds !" % round
            return w
        
    def reduce(self, v):
        """reduce"""
        # for i in range(len(self.vectors)):
        #     r = self.reduce_by_ith(v, i)
        #     if not (r is False):
        #         return r
        # return False
        l = len(self.vectors)
        vectors = deque(range(l))
        i = 0
        w = v
        while i<l and not isz(w):
            r = self.reduce_by_ith(w,vectors[i])
            if not (r is False):
                # rotate the list and start over
                vectors.rotate(i+1)
                i = 0
                w = r
            else:
                i += 1
        return w
        
        
    def unfinished(self):
        """ """
        return len(self.pairs)
        
        
    def pop(self):
        """docstring for pop"""
        return self.pairs.pop()
            
    
def bubu(A,b,c,u):
    A = matrix(ZZ,A)
    b = vector(ZZ, b)
    c = vector(ZZ,c)
    u = vector(ZZ,u) 
    m, n = A.dimensions()
    conditions = [m == len(b), n == len(c), n == len(u) ]
    
    if not all(conditions):
        raise ValueError("Not all conditions met %s" %conditions)
    
    g = PartialBasis(A, c, b, u)
    c1 = 0
    c2 = 0
    rx = 0
    elig = 0
    equ = 0
    
    while g.unfinished():
        if len(g.vectors)>200: break
        i, j = g.pop()
        if g.criterion_1(i,j): 
            c1 += 1
            next
        # if g.criterion_2(i,j):
        #     c2 += 1
        #     next
        
        
        cv = g.cv[i]
        cw = g.cv[j]
        if cv == cw:
            equ +=1
            next
        elif cw < cv:
            i, j = j, i
        # At this point, cv < cw.
        # 2.2.1
        #if g.eligible[i]:
        r = g.vectors[j]-g.vectors[i]
        rp,rm = pm_split(r)
        if let(rp,u) and let(rm,u) and let(A*rp,b) and let(A*rm,b) :
            rx +=1
            # r = g.vectors[j]-g.vectors[i]
            c = g.reduce(r)
            if not isz(c):
                g.add_element(c)
        else:
            elig += 1
            next
            
    print "%s criterion 1, %s criterion 2, %s reductions, %s non eligible, %s equalities" % (c1, c2, rx, elig, equ)
    return g.vectors, g
    
    
    
    
A = matrix(ZZ, [[3,1,11,2,3,5,3], [4, 5, 0, 1, 7,4, 6], [5,6,1,9,2,3,3]])
c = vector(ZZ, [23,15,6,7,1,53,4])
b = vector(ZZ, [31,27,38])
u = vector(ZZ, 7*[38])
    