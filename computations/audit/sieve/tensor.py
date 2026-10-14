"""Divisor-closed tensor weights c_d = prod_{l|d} a_l prod_{l|m, l not| d} b_l on the divisors of m.
Then A, B', sum c all factor over l|m, so AB'/(sum c)^4 = prod_l f_l(eps), eps=b/a, with
f_l = (eps^2 + 1/r)(eps^2 + 2 eps sigma + iota)/(1+eps)^4  (in c-variables; diag correction ignored -> upper bnd of B')."""
import numpy as np
from scipy.optimize import minimize_scalar
from sieveqp import primes_upto
def per(l, model):
    if model=='I': r=s=i=float(l)
    elif model=='II':
        d=l/(l*l-1); lam0=(l*l+1)/(l+1); r=(1-d)/d; s=(lam0-d)/(1-d); i=(1+(1-2*d)*(lam0-d)/(d*(1-d)))/r
    elif model=='III_rmax':
        r=l-1/l; s=float(l); i=l-(l-1)/r
    f=lambda e:(e*e+1/r)*(e*e+2*e*s+i)/(1+e)**4
    res=minimize_scalar(f,bounds=(0,1),method='bounded')
    return min(res.fun,f(0.0)), res.x
for model in ['I','II','III_rmax']:
    P=[p for p in primes_upto(10**6) if p>=5]
    vals=np.array([per(l,model)[0] for l in P])
    cum=np.cumprod(vals)
    out=[]
    for y in [7,13,30,100,1000,10**4,10**5,10**6]:
        k=np.searchsorted(P,y,side='right')-1
        out.append(f"y={y}: prod={cum[k]:.4f} (prod(1-1/l)={np.prod([1-1/p for p in P[:k+1]]):.4f}, 2*sqrt={2*np.sqrt(cum[k]):.3f})")
    print(model,'per-prime f_min at l=5,7,11,13,97:',[round(per(l,model)[0],5) for l in (5,7,11,13,97)],
          'kappa_l:',[round(l*(l*l+1)/((l+1)*(l*l-1)),5) for l in (5,7,11,13,97)],'eps*:',[round(per(l,model)[1],4) for l in (5,7,97)])
    print('   ','; '.join(out))
