#!/usr/bin/env python


class BinomialBasis(object):
    """

    Fastest way to compute cost: c*v


    """
    def __init__(self, A, b,c, u):
        super(BinomialBasis, self).__init__()
        self.d, self.n = A.dimensions()
        self.A = A
        self.c = c
        self.b = b
        self.u = u
        self.bins = [] # binomials
        self.Abins = [] # A*v for v in binomials
        self.bins_psupp = [] # positive support of binomial
        self.bins_nsupp = [] # negative support of binomials
        self.Abins_psupp = [] # positive support of Av
        self.Abins_nsupp = [] # negative support of Av
        self.cbins = [] # c*v for v in binomials
        self.pairs = [] # pairs still to go.
        self.zerox = vector(ZZ,self.n*[0]) # for fast copying.
        self.zerob = vector(ZZ, self.d*[0]) # for fast copying.

        #
        #
        for e in identity_matrix(ZZ,self.n).rows():
            self.push_binomial(e)
            
    def supports(self, v):
        """
        Compute the positive and negative support of v
        """
        psupp = []
        nsupp = []
        for (k, c) in enumerate(v):
            if c>0:
                psupp.append(k)
            elif c<0:
                nsupp.append(k)
        return psupp, nsupp
    

    def push_binomial(self, v, Av=None):
        """
        Add binomial v and associated data into place.

        May change sign of v and Av in place.

        """
        cost = self.c*v
        if Av is None:
            av = self.A*v
        else:
            av = av

        if cost<0:
            # modify v and av in place.
            for k in xrange(self.n):
                v[k] = -v[k]
            for k in xrange(self.d):
                av[k] = -av[k]

        if cost == 0:
            raise RuntimeError("zero cost vector %s. Deal with this." %v)

        p, n = self.supports(v)
        ap, an = self.supports(av)
        l = len(self.bins)
        
        self.bins.append(v)
        self.cbins.append(abs(cost))
        self.Abins.append(av)
        self.bins_psupp.append(p)
        self.bins_nsupp.append(n)
        self.Abins_psupp.append(ap)
        self.Abins_nsupp.append(an)

        if l: # true if this is not the first vector
            for i in xrange(l):
                self.pairs.append((i,l))

    def pop_binomials(i, pairs=True):
        self.bins.pop(i)
        self.cbins.pop(i)
        self.Abins.pop(i)
        self.bins_psupp.pop(i)
        self.bins_nsupp.pop(i)
        self.Abins_psupp.pop(i)
        self.Abins_nsupp.pop(i)
        if pairs:
            for (k,p) in enumerate(self.pairs):
                if i in p:
                    self.pairs.pop(k)

    def next_pair(self):
        return self.pairs.pop[-1]

    def order(self, i,j):
        """
        Set i, j in gr-rev-lex order:

        vi > vj if c*vi > c*vj or
                    equality and the last nonzero coordinate of vi-vj is negative.

        We sort indices and not vectors so that we don't have to compute
        c*v and c*v more than once.
        """
        if self.cbins[i]>self.cbins[j]:
            return (i,j)
        elif self.cbins[i]<self.cbins[j]:
            return (j,i)
        else: # equal cost :(
            for k in xrange(self.n):
                l = self.n-k
                if self.bins[l] > self.bins[l] :
                    return (j,i)
                elif self.bins[l] < self.bins[l] :
                    return (i,j)
            # The vectors are equal. This should never happen:
            raise RuntimeError("Vectors %s and %s are equal (%s)" % (i,j,self.bins[i]))


    def criterion_1(self, i,j):
        if  (
            bool(set.intersect(self.Abins_psupp[i], self.Abins_psupp[j])) or
            bool(set.intersect(self.bins_nsupp[i], self.bins_nsupp[j])) or
            bool(set.intersect(self.bins_psupp[i], self.bins_psupp[j]))
            ): 
            return False
        else: 
            return True
    
    def feasible(self, v):
        """docstring for feasible"""
        if self.less_or_equal_pp(v,self.b) and self.less_or_equal_mp(v,self.b):
            avp, avm = pm_split(v)
            return self.less_or_equal_pp(self.A*avp, self.b) and self.less_or_equal_pp(self.A*avm, self.b)
        return False
            
    def pm_split(v):
        """ slightly faster than pm_split2"""
        up = copy(self.zerox)
        um = copy(self.zerox)
        for i,a in enumerate(v):
            if a>0:
                up[i]=a
            elif a<0:
                um[i]=-a
        return up, um

    
        
        
    def less_or_equal(self, a,b):
        "True if and only if a is less or equal than b."
        for (i,ai) in enumerate(a):
            if ai>b[i]:
                return False
        return True
    
    def less_or_equal_pp(self, a,b):
        "True if and only if a^+ is less or equal than b^+."
        for (i,ai) in enumerate(a):
            if ai>0 and ai>b[i]:
                return False
        return True
        
    def less_or_equal_mp(self, a,b):
        "True if and only if a^+ is less or equal than b^+."
        for (i,ai) in enumerate(a):
            if ai<0 and -ai>b[i]:
                return False
        return True
    
    
    
    


    def bu_buch(self):
        """docstring for fname"""
        skip_c1 = 0
        

        while self.pairs:
            i,j = self.next_pair()
            if criterion_1(i,j):
                skip_c1 +=1
                continue
            
            i,j = self.order(i,j)
            # fast r = ui-uj
            r = copy(g.zerox)
            for l in xrange(g.n):
                r[l] = self.bins[i][l]-self.bins[j][l]
            # end of fast r=ui-uj
            if self.feasible(v):




