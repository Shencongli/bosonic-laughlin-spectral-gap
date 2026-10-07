"""Rigorous fixed-point interval Taylor proof for all Q >= Qmin.

Only Python standard-library arithmetic is used. The parameter is x=1/Q.
Each Jet represents f(x)=sum(c_i*x^i)+x^(ORDER+1)*r(x) on
0<=x<=1/Qmin, with rigorous dyadic intervals for all coefficients and r. Positivity is tested on a fixed complement of
the exact common pair-annihilation kernel. This script does not infer an
all-Q result from sampled fluxes.
"""
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path
from functools import lru_cache
from decimal import Decimal, localcontext
import argparse, json, time
import exact_relative_blocks as E

BASE=Path(__file__).parent
BITS=192
ORDER=3
UNIT=1<<BITS

def ceildiv(a,b): return -((-a)//b)

class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None): self.lo=lo; self.hi=lo if hi is None else hi
    @staticmethod
    def point(q):
        q=F(q); v=q.numerator*UNIT
        return I(v//q.denominator,ceildiv(v,q.denominator))
    def zero(self): return self.lo==self.hi==0
    def __neg__(self): return I(-self.hi,-self.lo)
    def __add__(self,o):
        if not isinstance(o,I): o=I.point(o)
        return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __sub__(self,o): return self+-o
    def __mul__(self,o):
        if not isinstance(o,I): return self.scale(o)
        if self.zero() or o.zero(): return IZ
        vals=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(vals)//UNIT,ceildiv(max(vals),UNIT))
    __rmul__=__mul__
    def scale(self,q):
        if not q: return IZ
        if isinstance(q,int):
            if q>0: return I(self.lo*q,self.hi*q)
            return I(self.hi*q,self.lo*q)
        q=F(q); a,b=q.numerator,q.denominator
        lo,hi=(self.lo*a,self.hi*a) if a>0 else (self.hi*a,self.lo*a)
        return I(lo//b,ceildiv(hi,b))
    def inv(self):
        if self.lo<=0<=self.hi: raise ZeroDivisionError('interval contains zero')
        return I(UNIT*UNIT//self.hi,ceildiv(UNIT*UNIT,self.lo))
    def __truediv__(self,o):
        if not isinstance(o,I): o=I.point(o)
        return self*o.inv()
    def sqrt(self):
        assert self.lo>=0
        lo=isqrt(self.lo*UNIT); upper=self.hi*UNIT; hi=isqrt(upper)
        if hi*hi<upper: hi+=1
        return I(lo,hi)
    def absupper(self): return max(abs(self.lo),abs(self.hi))
    def report(self): return [str(F(self.lo,UNIT)),str(F(self.hi,UNIT))]
    def approx(self): return [float(F(self.lo,UNIT)),float(F(self.hi,UNIT))]

IZ=I(0); IO=I(UNIT)
XR=IZ; XR2=IZ

class J:
    __slots__=('c','r')
    def __init__(self,a=IZ,b=IZ,r=IZ): self.c=(a,b)+(IZ,)*(ORDER-1); self.r=r
    @staticmethod
    def make(c,r=IZ):
        out=object.__new__(J); out.c=tuple(c); out.r=r; return out
    @property
    def a(self): return self.c[0]
    @property
    def b(self): return self.c[1]
    @staticmethod
    def const(q): return J(I.point(q)) if q else JZ
    def zero(self): return all(a.zero() for a in self.c) and self.r.zero()
    def __neg__(self): return J.make([-a for a in self.c],-self.r)
    def __add__(self,o):
        if not isinstance(o,J): o=J.const(o)
        return J.make([a+b for a,b in zip(self.c,o.c)],self.r+o.r)
    __radd__=__add__
    def __sub__(self,o): return self+-o
    def scale(self,q):
        if not q: return JZ
        return J.make([a.scale(q) for a in self.c],self.r.scale(q))
    def __mul__(self,o):
        if not isinstance(o,J): return self.scale(o)
        if self.zero() or o.zero(): return JZ
        c=[IZ]*(2*ORDER+1)
        for i,a in enumerate(self.c):
            if a.zero(): continue
            for j,b in enumerate(o.c):
                if not b.zero(): c[i+j]=c[i+j]+a*b
        r=IZ
        for v in reversed(c[ORDER+1:]): r=v+XR*r
        cross=self.r*o.r
        for a,b in reversed(list(zip(self.c,o.c))):
            cross=a*o.r+self.r*b+XR*cross
        return J.make(c[:ORDER+1],r+cross)
    __rmul__=__mul__
    def range(self):
        out=self.r
        for a in reversed(self.c): out=a+XR*out
        return out
    def inv(self):
        ai=self.a.inv(); c=[ai]
        for k in range(1,ORDER+1):
            c.append(-ai*sum((self.c[i]*c[k-i] for i in range(1,k+1)),IZ))
        polynomial=J.make(c)
        remainder=-(self*polynomial).r/self.range()
        return J.make(c,remainder)
    def __truediv__(self,o):
        if not isinstance(o,J): o=J.const(o)
        return self*o.inv()
    def sqrt(self):
        a=self.a.sqrt(); c=[a]
        for k in range(1,ORDER+1):
            c.append((self.c[k]-sum((c[i]*c[k-i] for i in range(1,k)),IZ))/a.scale(2))
        polynomial=J.make(c)
        remainder=(self.r-(polynomial*polynomial).r)/(self.range().sqrt()+polynomial.range())
        return J.make(c,remainder)

JZ=J(); JO=J(IO); X=J(IZ,IO)

def zeros(n,m): return [[JZ for _ in range(m)] for _ in range(n)]
def jmatrix(A): return [[J.const(v) for v in row] for row in A]
def transpose(A): return list(map(list,zip(*A))) if A else []
def matmul(A,B):
    if not A: return []
    nr=len(A); mid=len(B); nc=len(B[0]) if B else 0
    C=zeros(nr,nc)
    for i,row in enumerate(A):
        for k,a in enumerate(row):
            if a.zero(): continue
            for j,b in enumerate(B[k]):
                if not b.zero(): C[i][j]=C[i][j]+a*b
    return C
def quad(K,U): return matmul(transpose(U),matmul(K,U))
def matadd(A,B,scale=1):
    return [[a+b.scale(scale) for a,b in zip(row,col)] for row,col in zip(A,B)]
def matscale(A,c): return [[a*c for a in row] for row in A]
def outer_add(A,l,r,c):
    for i,a in l.items():
        for j,b in r.items(): A[i][j]=A[i][j]+c.scale(a*b)

@lru_cache(None)
def annihilation_row(n,p,labels):
    M=p+sum(labels); ix={a:i for i,a in enumerate(E.parts(n,M))}; out={}
    for a in range(p+1):
        state=tuple(sorted((a,p-a)+labels))
        rest,w=E.ann(state,(a,p-a)+labels)
        assert rest==()
        q=ix[state]; out[q]=out.get(q,0)+w
    return out

def active_frame(r,z):
    """Exact complement, with an arbitrary rational approximate H whitening."""
    U=E.relative_basis(r,z)
    H=E.rel_quadratic(E.hamiltonian(r,z),r,z,z)
    a=[row[:] for row in H.a]; remaining=list(range(H.rows)); selected=[]
    while a:
        assert all(a[i][i]>=0 for i in range(len(a)))
        k=next((i for i in range(len(a)) if a[i][i]),None)
        if k is None:
            assert not any(v for row in a for v in row)
            break
        order=[k]+[i for i in range(len(a)) if i!=k]
        a=[[a[i][j] for j in order] for i in order]
        remaining=[remaining[i] for i in order]
        selected.append(remaining.pop(0)); p=a[0][0]
        a=[[a[i][j]-a[i][0]*a[0][j]/p for j in range(1,len(a))]
           for i in range(1,len(a))]
    k=len(selected)
    if not k: return [],{'relative_dimension':U.cols,'rank':0,'selected':[]}
    hs=[[H.a[i][j] for j in selected] for i in selected]
    assert E.exact_psd(E.Mat(hs,k))['rank']==k
    with localcontext() as ctx:
        ctx.prec=100
        hd=[[Decimal(q.numerator)/Decimal(q.denominator) for q in row] for row in hs]
        L=[[Decimal(0) for _ in range(k)] for _ in range(k)]
        for i in range(k):
            for j in range(i+1):
                v=hd[i][j]-sum(L[i][h]*L[j][h] for h in range(j))
                L[i][j]=v.sqrt() if i==j else v/L[j][j]
        # P=L^{-T}; rounding is only a choice of a rational basis.
        P=[[Decimal(0) for _ in range(k)] for _ in range(k)]
        for col in range(k):
            for i in range(k-1,-1,-1):
                v=(Decimal(1) if i==col else Decimal(0))-sum(L[j][i]*P[j][col] for j in range(i+1,k))
                P[i][col]=v/L[i][i]
        denominator=10**45
        pf=[[F(int((v*denominator).to_integral_value()),denominator) for v in row] for row in P]
    assert all(pf[i][i] for i in range(k))
    assert all(pf[i][j]==0 for i in range(k) for j in range(i))
    chosen=E.Mat([[row[j] for j in selected] for row in U.a],k)
    frame=chosen@E.Mat(pf,k)
    return jmatrix(frame.a),{'relative_dimension':U.cols,'rank':k,'selected':selected,
                              'rational_frame':[[str(v) for v in row] for row in frame.a]}

def interval_ldl(A):
    """Positive interval LDL pivots certify every symmetric matrix enclosed."""
    a=[row[:] for row in A]; piv=[]
    while a:
        p=a[0][0]
        piv.append(p)
        if p.lo<=0: return False,piv
        a=[[a[i][j]-a[i][0]*a[0][j]/p for j in range(1,len(a))]
           for i in range(1,len(a))]
    return True,piv

def certify(A,qmin):
    from math import comb
    k=len(A)
    A=[[(A[i][j]+A[j][i]).scale(F(1,2)) for j in range(k)] for i in range(k)]
    rem=max((sum(v.r.absupper() for v in row) for row in A),default=0)
    error=I(ceildiv(rem,qmin**(ORDER+1)))
    controls=[]
    for b in range(ORDER+1):
        M=[]
        for i,row in enumerate(A):
            M.append([sum((v.c[a].scale(F(comb(b,a),comb(ORDER,a)*qmin**a))
                           for a in range(b+1)),IZ)-(error if i==j else IZ)
                      for j,v in enumerate(row)])
        controls.append(M)
    reports=[]
    def verify(ctrl,depth=0):
        local=[]
        for idx,M in enumerate(ctrl):
            ok,piv=interval_ldl(M)
            local.append((ok,piv))
        if all(ok for ok,piv in local):
            reports.append({'depth':depth,'pivots':[[p.report() for p in piv] for ok,piv in local]})
            return True
        if depth>=8:
            reports.append({'depth':depth,'failed':True,'pivots':[[p.report() for p in piv] for ok,piv in local]})
            return False
        # de Casteljau subdivision preserves the same matrix polynomial.
        levels=[ctrl]
        for level in range(ORDER):
            prev=levels[-1]
            levels.append([[[ (a+b).scale(F(1,2)) for a,b in zip(row,col)]
                             for row,col in zip(left,right)]
                           for left,right in zip(prev,prev[1:])])
        left=[level[0] for level in levels]
        right=[level[-1] for level in reversed(levels)]
        return verify(left,depth+1) and verify(right,depth+1)
    ok=verify(controls)
    lowers=[float(F(p[0])) for rec in reports for piv in rec['pivots'] for p in piv]
    return {'certified':ok,'remainder_norm_upper':str(F(rem,UNIT)),
            'remainder_form_error':str(F(error.hi,UNIT)),
            'remainder_form_error_decimal':float(F(error.hi,UNIT)),
            'bernstein_subinterval_checks':reports,
            'minimum_endpoint_pivot_lower_decimal':min(lowers,default=0)}

class Model:
    def __init__(self,qmin):
        self.qmin=qmin
        self.P=[]; self.E=[]; self.di=[]; self.ei=[]
        for cap in range(17):
            p=JO; e=JO
            for j in range(cap):
                p=p*(JO-X.scale(j)); e=e*(JO-X.scale(F(j,2)))
            self.P.append(p); self.E.append(e)
            self.di.append(p.sqrt().inv()); self.ei.append(e.sqrt().inv())
        self.rows=json.loads((BASE/'exact_shifted_certificate_rows.json').read_text())
        self.K3={M:zeros(len(E.parts(3,M)),len(E.parts(3,M))) for M in range(9)}
        self.K4={M:zeros(len(E.parts(4,M)),len(E.parts(4,M))) for M in range(17)}
        self.make_body_forms()

    def make_body_forms(self):
        start=time.time()
        for t in range(4):
            data=self.rows[str(t)]; terms=data['terms']; rows=data['integer_scaled_rows']
            den=data['common_denominator']**2; count=len(terms)
            C=[[F(sum(row[a]*row[b] for row in rows),den) for b in range(count)] for a in range(count)]
            spec=[]
            for p,j in terms[1:]:
                i=p+j-t
                h=(self.ei[p]*self.di[i]*self.di[j]).scale(factorial(i))
                spec.append((p,j,i,h))
            for a,(p,j,i,h) in enumerate(spec,1):
                M=p+j
                left=annihilation_row(3,t,(i,)); right=annihilation_row(3,p,(j,))
                c=(h*self.ei[t]).scale(C[0][a])
                outer_add(self.K3[M],left,right,c); outer_add(self.K3[M],right,left,c)
                for b,(pp,jj,ii,hh) in enumerate(spec,1):
                    if not C[a][b]: continue
                    if i==ii:
                        c=(self.ei[p]*self.ei[pp]*self.di[j]*self.di[jj]).scale(C[a][b]*factorial(i))
                        outer_add(self.K3[M],right,annihilation_row(3,pp,(jj,)),c)
                    M4=p+j+ii
                    c=(h*hh).scale(C[a][b])
                    outer_add(self.K4[M4],annihilation_row(4,p,(j,ii)),
                              annihilation_row(4,pp,(i,jj)),c)
            print('body forms channel',t,'seconds',round(time.time()-start,2),flush=True)

    @lru_cache(None)
    def metric(self,n,M):
        out=[]
        for A in E.parts(n,M):
            q=JO.scale(E.g(A))
            for j in A: q=q/self.P[j]
            out.append(q)
        return out

    @lru_cache(None)
    def H(self,n,M):
        size=len(E.parts(n,M)); out=zeros(size,size)
        for p in range(M+1):
            B=E.bhat(n,M,p)
            coefficient=self.E[p].inv().scale(E.kappa2(p))
            for row,g in zip(B.a,self.metric(n-2,M-p)):
                v={j:a for j,a in enumerate(row) if a}
                outer_add(out,v,v,coefficient*g)
        return out

    def target(self,n,M):
        if n==3:
            H=self.H(n,M); g=self.metric(n,M)
            invH=[[v/g[i] for v in row] for i,row in enumerate(H)]
            return matadd(matmul(H,invH),H,-1)
        size=len(E.parts(n,M)); out=zeros(size,size)
        for p in range(M+1):
            q=M-p
            B=E.bhat(2,q,q)@E.bhat(4,M,p)
            v={j:a for j,a in enumerate(B.a[0]) if a}
            c=(self.E[p]*self.E[q]).inv().scale(E.kappa2(p)*E.kappa2(q))
            outer_add(out,v,v,c)
        return matscale(out,J.const(1-30*F(5,9)**9-F(1,50)))

    def raise_frame(self,n,M,V):
        src=E.parts(n,M); dst=E.parts(n,M+1); ix={A:i for i,A in enumerate(dst)}
        k=len(V[0]); out=zeros(len(dst),k)
        for col,A in enumerate(src):
            for j in set(A):
                B,w=E.ann(A,(j,)); B=tuple(sorted(B+(j+1,)))
                factor=(JO-X.scale(j)).scale(w)
                for a in range(k):
                    out[ix[B]][a]=out[ix[B]][a]+factor*V[col][a]
        return out

    def block(self,n,z,delta):
        frame,info=active_frame(n,z)
        if not info['rank']: return {'body':n,'z':z,'delta':str(delta),**info,'certified':True}
        k=info['rank']; V=frame
        result=quad(self.target(n,z),V)
        result=matadd(result,quad(self.H(n,z),V),delta)
        average=zeros(k,k); norm=JO
        body=self.K3 if n==3 else self.K4
        cap=8 if n==3 else 16
        for M in range(z,cap+1):
            average=matadd(average,matscale(quad(body[M],V),norm.inv()))
            if M<cap:
                step=M+1-z
                norm=norm*(JO.scale(n)-X.scale(2*z+step-1)).scale(step)
                V=self.raise_frame(n,M,V)
        schur=(JO.scale(2)+X)/(JO.scale(n)+X.scale(1-2*z))
        result=matadd(result,matscale(average,schur),-1)
        check=certify(result,self.qmin)
        # Matrices retained for auditing are fixed point interval data, not floats.
        check['taylor_matrix']=[[[*[c.report() for c in v.c],v.r.report()] for v in row] for row in result]
        return {'body':n,'z':z,'delta':str(delta),**info,**check}

def main():
    global XR,XR2,ORDER,JZ,JO,X
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--qmin',type=int,default=100000)
    parser.add_argument('--order',type=int,choices=[1,2,3,4,5],default=3)
    parser.add_argument('--shifts',type=Path,help='JSON mapping body number to a mapping z -> rational delta')
    parser.add_argument('--delta3',default='8/100000')
    parser.add_argument('--delta4',default='8/10000000')
    parser.add_argument('--body',type=int,choices=[3,4])
    parser.add_argument('--z',type=int)
    parser.add_argument('--result',type=Path)
    args=parser.parse_args()
    assert args.qmin>=1024
    ORDER=args.order; JZ=J(); JO=J(IO); X=J(IZ,IO)
    shifts=json.loads(args.shifts.read_text()) if args.shifts else {}
    XR=I(0,ceildiv(UNIT,args.qmin)); XR2=XR*XR
    started=time.time(); model=Model(args.qmin); checks=[]
    for n,cap,delta in [(3,8,F(args.delta3)),(4,16,F(args.delta4))]:
        if args.body and n!=args.body: continue
        for z in range(cap+1):
            if args.z is not None and z!=args.z: continue
            block_delta=F(shifts.get(str(n),{}).get(str(z),str(delta)))
            assert block_delta>=0
            rec=model.block(n,z,block_delta); checks.append(rec)
            brief={k:rec[k] for k in ['body','z','rank','certified']}
            for k in ['remainder_form_error_decimal','minimum_endpoint_pivot_lower_decimal']:
                if k in rec: brief[k]=rec[k]
            brief['elapsed_seconds']=round(time.time()-started,2)
            print(json.dumps(brief),flush=True)
    result={'status':'RIGOROUS_INTERVAL_HEAD_VERIFIED' if all(c['certified'] for c in checks) else 'INTERVAL_HEAD_NOT_CERTIFIED',
            'uniform_integer_Qmin':args.qmin,'shifts_file':str(args.shifts) if args.shifts else None,
            'shift_mode':'per_block_rational_file' if args.shifts else 'uniform_by_body',
            'default_delta3':str(F(args.delta3)),'default_delta4':str(F(args.delta4)),
            'dyadic_precision_bits':BITS,'taylor_order':ORDER,'interval':'0<=1/Q<=1/Qmin',
            'scope':'all retained blocks' if args.body is None and args.z is None else 'selected blocks only',
            'checks':checks,'elapsed_seconds':time.time()-started}
    path=args.result or BASE/f'optimized_head_interval_Q{args.qmin}_results.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))
    if not all(c['certified'] for c in checks): raise SystemExit(1)

if __name__=='__main__': main()
