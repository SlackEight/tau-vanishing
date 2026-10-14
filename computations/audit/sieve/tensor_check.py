import numpy as np, itertools, math
from scipy.optimize import minimize
# model I, explicit enumeration over divisors of m; optimise all 2^k weights freely (not just tensor) from tensor start
for primes in [(5,7),(5,7,11),(5,7,11,13),(5,7,11,13,17),(5,7,11,13,17,19,23)]:
    k=len(primes); divs=[]
    for mask in range(2**k):
        S=[p for j,p in enumerate(primes) if mask>>j&1]; divs.append((math.prod(S),set(S)))
    m=math.prod(primes)
    d=np.array([x for x,_ in divs],float)
    L=np.array([[math.lcm(int(a),int(b)) for b in d] for a in d],float)
    best=None
    for t in [m*m/16, m*m/4, m*m, 4*m*m]:
        def f(z):
            c=np.exp(z); c/=c.sum(); return t*np.sum(c*c/d)+c@L@c
        # tensor start with eps=1/l
        z0=np.array([sum(-math.log(p) for p in primes if p not in S) for _,S in divs])
        res=minimize(f,z0,method='L-BFGS-B',options=dict(maxiter=5000))
        c=np.exp(res.x); c/=c.sum(); A=np.sum(c*c/d); B=c@L@c
        r=(res.fun/math.sqrt(t), A*B)
        if best is None or r[0]<best[0]: best=(r[0],r[1],t)
    kap=np.prod([1-1/p for p in primes])
    print(primes,'min tA+B over all weights on divisors of m: ratio/sqrt(t)=%.4f, AB=%.4f; 2sqrt(prod(1-1/l))=%.4f; single modulus=2.0'%(best[0],best[1],2*math.sqrt(kap)))
