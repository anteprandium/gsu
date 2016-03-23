#!/usr/bin/env sage -python
# encoding: utf-8

"""
Algorithms for computing test sets of Integer Programming problems.

# ==============================================
# = This is ongoing work by J. Soto y JM Ucha. =
# ==============================================

This file implements the algorithm walk back, then look.

"""

import operator
import itertools
from sage.all import *




def fast_add(l,m):
    """
    Fast addition of two lists, as per 
    
    http://stackoverflow.com/questions/18713321/element-wise-addition-of-2-lists-in-python
    """
    # assert(len(l)==len(m))
    return map(operator.add, l,m)
    # Slower alternatives:
    # return [a+b for a,b in zip(l,m)]
    # return list(itertools.imap(operator.add, l,m))
    
def isgtz(l):
    """Check whether l[i]>0 for all i."""
    return all((li>0 for li in l))

def isgetz(l):
    """Check whether l[i]>=0 for all i."""
    return all(li>=0 for li in l)

def fast_dot(c,x):
    """Quickly compute the scalar product c*x"""
    # assert(len(c)==len(x))
    return add(itertools.imap(operator.mul, c,x))
    # To test:
    # return add(map(operator.mul, c,x))
    # Slower alternative
    # return add(ci*xi for ci,xi in zip(c,x))
    
    
def worthy_children(P, T, cost, Oc=infinity):
    """
    Find all children of point P from test set T, such that
    1. They are positive.
    2. Their cost is strictly less than the cost at the optimun so far, Oc. (Oc is the Optimum cost, not the optimum point itself.)
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
    

def walk_back_and_look_behing(P, T, Omega, c, A, b):
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
    

