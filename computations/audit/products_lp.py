import sys, math, numpy as np
"""Independent audit of Conjecture 4.12 on products of two or three factors: inf mu*lam over class-function
majorants of Inv x Inv (x Inv) vs the product of the kappa_l of Theorem B1, over the full range of the mean mu
(mean fixed exactly: 150 points in [mu0, 1/2], 75 in [1/2, 1], 40 in [1, 3]).  Usage: python products_lp.py 5 7"""
from characters_lp import setup, lp_min
ls=[int(a) for a in sys.argv[1:]]
facs=[]
for l in ls:
    K, chars, reps, X, sizes, dims, Fm, w, names, order = setup(l)
    facs.append((Fm,dims,w,[names.index("is"),names.index("in")],l))
Fm,dims,w=facs[0][0],facs[0][1],facs[0][2]
for f in facs[1:]:
    Fm=np.kron(Fm,f[0]); dims=np.kron(dims,f[1]); w=np.kron(w,f[2])
shape=[f[0].shape[1] for f in facs]
import itertools
D=set()
for tup in itertools.product(*[f[3] for f in facs]):
    i=0
    for k,s in zip(tup,shape): i=i*s+k
    D.add(i)
kap=np.prod([l*(l*l+1)/((l+1)*(l*l-1)) for l in ls])
mu0=float(sum(w[i] for i in D))
best=1e9; hi=1e9
grid=np.unique(np.concatenate([mu0*np.exp(np.linspace(0,math.log(0.5/mu0),150)),np.linspace(0.5,1,75),np.linspace(1,3,40)]))
for M in grid:
    _,ph,m,la=lp_min(Fm,dims,w,D,Meq=M); best=min(best,m*la)
    if M>=0.5: hi=min(hi,m*la)
print(ls,"inf mu*lam (grid, full mu range,",len(grid),"pts)",round(best,6),"prod kappa",round(kap,6),"ratio",round(best/kap,6),
      "| min mu*lam over mu>=1/2",round(hi,6))
