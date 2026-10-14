import numpy as np
from scipy.optimize import linprog
from pgl2 import table, inv_ind
for l in [5,7,11,13,29]:
    T=table(l); X=T['X']; d=T['dims']; sz=T['sizes']; G=T['G']; one=inv_ind(T); mu0=(one*sz).sum()/G
    k=len(d); r=3.0
    # vars: c_pi (k), a, b ; maximize a + b r ; s.t. a + b*one/mu0 - sum c_pi chi_pi(g) <= 0 ; |c_pi|<=d
    cost=np.concatenate([np.zeros(k),[-1,-r]])
    Aub=np.hstack([-X.T, np.ones((k,1)), (one/mu0)[:,None]])
    res=linprog(cost,A_ub=Aub,b_ub=np.zeros(k),bounds=[(-dd,dd) for dd in d]+[(None,None),(0,None)],method='highs')
    c=res.x[:k]; a,b=res.x[k:]
    print(l,'bound',-res.fun,'a',round(a,6),'b',round(b,6))
    print('   c/dim:',dict(zip(T['names'],np.round(c/d,4))))
    Psi=c@X
    print('   values:',dict(zip([str(cc[0])+(str(cc[1]) if cc[1] else '') for cc in T['classes']],np.round(Psi,3))))
