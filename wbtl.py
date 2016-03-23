#!/usr/bin/env sage -python
# encoding: utf-8

"""
Algorithms for computing test sets of Integer Programming problems.

# ==============================================
# = This is ongoing work by J. Soto y JM Ucha. =
# ==============================================

This file implements the algorithm “walk back, then look”.

"""

# import operator # not needed anymore
# import itertools # not needed anymore
from sage.all import *




def fast_add(l,m):
    """
    Fast addition of two lists. First versions used ideas in 
    
        http://stackoverflow.com/questions/18713321/element-wise-addition-of-2-lists-in-python
    
    using, essentially,
    
        return map(operator.add, l,m)
        
    Slower alternatives:
    
        return [a+b for a,b in zip(l,m)]
        return list(itertools.imap(operator.add, l,m))
        
    Turns out, fastest is just to wrap Sage's addition. Can't reinvent the wheel, after all.
    
    >>> fast_add([],[])
    ()
    
    >>> fast_add([1,2],[1])
    Traceback (most recent call last):
    ...
    TypeError: unsupported operand parent(s) for '+': 'Ambient free module of rank 2 over the principal ideal domain Integer Ring' and 'Ambient free module of rank 1 over the principal ideal domain Integer Ring'
    
    
    Caveat: returns a `vector`; not a `list`.
    
    >>> fast_add(10000*[1],10000*[3]) == vector(ZZ,10000*[4])
    True
    
    
    """
    return vector(ZZ,l)+vector(ZZ,m)
    
# def isgtz(l):
#     """Check whether l[i]>0 for all i."""
#     return all(li>0 for li in l)

def isgetz(l):
    """
    Given a list or vector `l`, return `True` if all its components are greater or equal than 0. Uses a generator and `all` for speed.
    
    >>> isgetz(1000*[1])
    True
    >>> isgetz(1000*[1]+[-1])
    False
    
    
    On the empty list it returns `True`.
    >>> isgetz([])
    True

    """
    return all(li>=0 for li in l)

def fast_dot(c,x):
    """
    Quickly compute the scalar product `c*x`.
    
    First versions used some iterators ideas:
    
        return add(itertools.imap(operator.mul, c,x))
        return add(map(operator.mul, c,x))
        return add(ci*xi for ci,xi in zip(c,x))
        
    but it turns out the fastest is to use Sage's vectors.
    """
    return vector(ZZ,c)*vector(ZZ,x)
    
    
def worthy_children(P, T, cost, Oc=infinity):
    """
    Find all children of point P from test set T, such that
    1. They are positive.
    2. Their cost is strictly less than the cost at the optimum so far, Oc. (Oc is the Optimum cost, not the optimum point itself.)
    3. Are feasible?
    """
    for t in T:
        candidate = fast_add(P,t)
        if isgetz(candidate) and fast_dot(cost, candidate)<=Oc:
            yield candidate
            
def only_new(New, Cache):
    """
    Check for each element of New whether it already belongs to cache. 
    Return a generator of elements not in the Cache, and update Cache.

    """
    for P in New:
        if P not in Cache:
            Cache.append(P)
            yield P
    
def add_to_V(current, T, c, best_cost_Omega, V, cached):
    for v in worthy_children(current, T, c, best_cost_Omega):
        if v not in cached:
            cached.append(v)
            V.append(v)
    

def walk_back_and_look_behind(P, T, Omega, c, A, b):
    """
    Implement the walk back and look behind algorithm for the problem
        min cx
        st  Ax=b
            x in RegionOmega
    with the given test set T, optimal point P for the linear problem, and non-linear region function indicator Omega. That is, x in RegionOmega == True if and only if Omega(x)==True
    """
    best_cost_Omega = infinity
    V = list()
    S = list()
    
    if Omega(P):
        S = [P]
    else:
        V = list(worthy_children(P, T, c))
        
    cached = V[:] # shallow copy
    while V:
        current = V.pop() # 0 = first, nothing = last.
        current_cost = fast_dot(c, current)
        if Omega(current):
            if current_cost < best_cost_Omega:
                S = [current]
                best_cost_Omega = current_cost
            # elif  current_cost == best_cost_Omega:
            else: # worthy_children() only gives points with cost <= thatn best_cost_Omega
                S.append(current)
                enlarge = True
        else:
            enlarge = True
        if enlarge:    
            # V += list(only_new(worthy_children(current, T, c, best_cost_Omega), cached))
            add_to_V(current, T, c, best_cost_Omega, V, cached)
            enlarge = False
    return S
    
if __name__ == '__main__':
    import doctest
    doctest.testmod()