"""Exact real rational bosonic planar V0 few-body and relative-block algebra.

Basis creators x_j = sqrt(j!) a_j^dagger and canonical derivatives
d_j = a_j/sqrt(j!).  The names x,d do not denote physical adjoints:
d_j^* = x_j/j!, x_j^* = j! d_j.  Basis metric is
g_A = prod_j n_j! (j!)**n_j.  All operator matrices below are coordinates
in this nonorthonormal basis; positivity is tested on G times the operator.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, comb
from dataclasses import dataclass

@dataclass
class Mat:
    a: list
    cols: int
    @property
    def rows(self): return len(self.a)
    @property
    def shape(self): return self.rows,self.cols
    def T(self):
        return Mat([[self.a[i][j] for i in range(self.rows)] for j in range(self.cols)],self.rows)
    def __add__(self,o):
        assert self.shape==o.shape
        return Mat([[x+y for x,y in zip(r,s)] for r,s in zip(self.a,o.a)],self.cols)
    def __sub__(self,o): return self+o.scale(-1)
    def scale(self,s): return Mat([[F(s)*x for x in r] for r in self.a],self.cols)
    def __matmul__(self,o):
        assert self.cols==o.rows
        out=zeros(self.rows,o.cols)
        for i,row in enumerate(self.a):
            for k,x in enumerate(row):
                if x:
                    for j,y in enumerate(o.a[k]):
                        if y: out.a[i][j]+=x*y
        return out

def zeros(n,m): return Mat([[F(0) for _ in range(m)] for _ in range(n)],m)
def eye(n):
    A=zeros(n,n)
    for i in range(n): A.a[i][i]=F(1)
    return A

@lru_cache(None)
def parts(n,D):
    if n<0 or D<0: return ()
    if n==0: return ((),) if D==0 else ()
    out=[]
    def rec(pre,k,left,lo):
        if k==1:
            if left>=lo: out.append(tuple(pre+[left]))
            return
        for i in range(lo,left//k+1): rec(pre+[i],k-1,left-i,i)
    rec([],n,D,0)
    return tuple(out)

def g(A):
    out=1
    for j in set(A): out*=factorial(A.count(j))*factorial(j)**A.count(j)
    return F(out)

def metric(n,D): return [g(A) for A in parts(n,D)]

def weighted_rows(A,weights):
    assert len(weights)==A.rows
    return Mat([[w*x for x in row] for w,row in zip(weights,A.a)],A.cols)

def adj(A,source_metric,target_metric):
    assert A.shape==(len(target_metric),len(source_metric))
    out=A.T()
    return Mat([[out.a[i][j]*target_metric[j]/source_metric[i]
                 for j in range(out.cols)] for i in range(out.rows)],out.cols)

def quadratic(A,source_metric):
    assert A.rows==A.cols==len(source_metric)
    Q=weighted_rows(A,source_metric)
    assert Q.a==Q.T().a
    return Q

def ann(A,labels):
    a=list(A); weight=1
    for j in labels:
        count=a.count(j)
        if not count: return None,0
        weight*=count; a.remove(j)
    return tuple(a),weight

@lru_cache(None)
def bhat(n,D,p):
    src=parts(n,D); dst=parts(n-2,D-p); ix={A:k for k,A in enumerate(dst)}
    out=zeros(len(dst),len(src))
    for c,A in enumerate(src):
        for i in range(p+1):
            B,w=ann(A,(i,p-i))
            if w: out.a[ix[B]][c]+=w
    return out

def kappa2(p): return F(factorial(p),2**(p+1))

def foperator(n,D,t,y):
    """y maps None->lambda*kappa_t, (p,j)->alpha*kappa_p*sqrt(j!/i!)."""
    src=parts(n,D); dst=parts(n-2,D-t); ix={A:k for k,A in enumerate(dst)}
    out=zeros(len(dst),len(src))
    for term,coef in y.items():
        coef=F(coef)
        if term is None:
            out=out+bhat(n,D,t).scale(coef)
            continue
        p,j=term; i=p+j-t
        assert i>=0
        for c,A in enumerate(src):
            for a in range(p+1):
                B,w=ann(A,(a,p-a,j))
                if w:
                    B=tuple(sorted(B+(i,)))
                    out.a[ix[B]][c]+=coef*w
    return out

def gram_operator(A,n,D,out_n,out_D):
    return adj(A,metric(n,D),metric(out_n,out_D))@A

def lift(R,r,body_D,n,total_D):
    """Coordinate k-body lift; columns carry integer occupation binomials."""
    body=parts(r,body_D); target=parts(n,total_D)
    assert R.shape==(len(body),len(body))
    out=zeros(len(target),len(target)); ix={A:k for k,A in enumerate(target)}
    for S in parts(n-r,total_D-body_D):
        combined=[tuple(sorted(A+S)) for A in body]
        for b,B in enumerate(body):
            w=1
            for j in set(B): w*=comb(B.count(j)+S.count(j),B.count(j))
            if w:
                for a in range(len(body)):
                    if R.a[a][b]: out.a[ix[combined[a]]][ix[combined[b]]]+=R.a[a][b]*w
    return out

@lru_cache(None)
def hamiltonian(n,D):
    out=zeros(len(parts(n,D)),len(parts(n,D)))
    for p in range(D+1):
        A=bhat(n,D,p)
        out=out+gram_operator(A,n,D,n-2,D-p).scale(kappa2(p))
    quadratic(out,metric(n,D))
    return out

@lru_cache(None)
def s3(D):
    H=hamiltonian(3,D)
    return H@H-H

@lru_cache(None)
def s4(D):
    out=zeros(len(parts(4,D)),len(parts(4,D)))
    for p in range(D+1):
        q=D-p; A=bhat(2,D-p,q)@bhat(4,D,p)
        out=out+gram_operator(A,4,D,0,0).scale(kappa2(p)*kappa2(q))
    quadratic(out,metric(4,D))
    return out

@lru_cache(None)
def cm_lower(n,D):
    src=parts(n,D); dst=parts(n,D-1); ix={A:k for k,A in enumerate(dst)}
    out=zeros(len(dst),len(src))
    for c,A in enumerate(src):
        for j in set(A):
            if j:
                B,w=ann(A,(j,)); B=tuple(sorted(B+(j-1,)))
                out.a[ix[B]][c]+=j*w
    return out

@lru_cache(None)
def cm_raise(n,D):
    src=parts(n,D); dst=parts(n,D+1); ix={A:k for k,A in enumerate(dst)}
    out=zeros(len(dst),len(src))
    for c,A in enumerate(src):
        for j in set(A):
            B,w=ann(A,(j,)); B=tuple(sorted(B+(j+1,)))
            out.a[ix[B]][c]+=w
    assert adj(out,metric(n,D),metric(n,D+1)).a==cm_lower(n,D+1).a
    return out

def nullspace(A):
    """Rational RREF kernel; columns give an independent basis."""
    a=[list(row) for row in A.a]; piv=[]; r=0
    for j in range(A.cols):
        k=next((k for k in range(r,A.rows) if a[k][j]),None)
        if k is None: continue
        a[r],a[k]=a[k],a[r]; d=a[r][j]; a[r]=[x/d for x in a[r]]
        for k in range(A.rows):
            if k!=r and a[k][j]:
                d=a[k][j]; a[k]=[x-d*y for x,y in zip(a[k],a[r])]
        piv.append(j); r+=1
        if r==A.rows: break
    free=[j for j in range(A.cols) if j not in piv]
    out=zeros(A.cols,len(free))
    for c,j in enumerate(free):
        out.a[j][c]=F(1)
        for k,p in enumerate(piv): out.a[p][c]=-a[k][j]
    return out

@lru_cache(None)
def relative_basis(n,d): return nullspace(cm_lower(n,d))

@lru_cache(None)
def descendant(n,d,D):
    assert D>=d
    if D==d: return relative_basis(n,d)
    return cm_raise(n,D-1)@descendant(n,d,D-1)

def rel_quadratic(R,n,d,D):
    U=descendant(n,d,D); k=D-d
    return (U.T()@quadratic(R,metric(n,D))@U).scale(F(1,n**k*factorial(k)))

def relative_metric(n,d):
    U=relative_basis(n,d)
    return U.T()@weighted_rows(U,metric(n,d))

def body_terms(t,maxT,y):
    """Normal-ordered K2,K3,K4 coordinate matrices for one rational row."""
    B=bhat(2,t,t); K2=gram_operator(B,2,t,0,0).scale(F(y.get(None,0))**2)
    K3={}; K4={}
    for D in range(maxT+1):
        A=foperator(3,D,t,y)
        K3[D]=gram_operator(A,3,D,1,D-t)-lift(K2,2,t,3,D)
        quadratic(K3[D],metric(3,D))
    for D in range(2*maxT-t+1):
        A=foperator(4,D,t,y)
        R=gram_operator(A,4,D,2,D-t)-lift(K2,2,t,4,D)
        for U in range(min(maxT,D)+1): R=R-lift(K3[U],3,U,4,D)
        K4[D]=R; quadratic(R,metric(4,D))
    return K2,K3,K4

def cm_average_quadratics(body,n):
    maxD=max(body); out={}
    for d in range(maxD+1):
        dim=relative_basis(n,d).cols; Q=zeros(dim,dim)
        for D in range(d,maxD+1): Q=Q+rel_quadratic(body[D],n,d,D)
        out[d]=Q.scale(F(2,n))
    return out

def exact_psd(Q):
    """Rational symmetric elimination; works for singular PSD matrices.

    No floating eigenvalues enter. Positive pivots give a congruent Schur
    complement. A zero diagonal with nonzero off-diagonal is indefinite.
    """
    assert Q.rows==Q.cols and Q.a==Q.T().a
    a=[list(row) for row in Q.a]; rank=0; piv=[]
    while a:
        if any(a[i][i]<0 for i in range(len(a))):
            return {'psd':False,'positive_pivots':rank,'reason':'negative diagonal after exact congruence'}
        k=next((i for i in range(len(a)) if a[i][i]>0),None)
        if k is None:
            if any(x for row in a for x in row):
                return {'psd':False,'positive_pivots':rank,'reason':'zero diagonal with nonzero offdiagonal'}
            return {'psd':True,'rank':rank,'nullity':Q.rows-rank,'pivots':[str(x) for x in piv]}
        order=[k]+[i for i in range(len(a)) if i!=k]
        a=[[a[i][j] for j in order] for i in order]
        p=a[0][0]; piv.append(p); rank+=1
        a=[[a[i][j]-a[i][0]*a[0][j]/p for j in range(1,len(a))]
           for i in range(1,len(a))]
    return {'psd':True,'rank':rank,'nullity':0,'pivots':[str(x) for x in piv]}
