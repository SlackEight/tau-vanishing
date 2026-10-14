import sympy as sp
l=sp.symbols('l',positive=True)
d=l/(l**2-1); lam0=(l**2+1)/(l+1)
r=sp.simplify((1-d)/d)
sig=sp.simplify((lam0-d)/(1-d))
lamphi2=1+(1-2*d)*(lam0-d)/(d*(1-d))
iota=sp.simplify(lamphi2/r)
print('r =',sp.factor(r)); print('sigma =',sp.factor(sig)); print('iota =',sp.factor(iota))
print('sigma-r =',sp.factor(sp.simplify(sig-r)))
print('iota-r =',sp.factor(sp.simplify(iota-r)))
# sharp general bound iota >= l-(l-1)/r at r = two-point r:
print('iota - (l-(l-1)/r) =',sp.factor(sp.simplify(iota-(l-(l-1)/r))))
for L in [5,7,11,97]:
    print(L, float(sig.subs(l,L)/r.subs(l,L)), float(iota.subs(l,L)/r.subs(l,L)))
