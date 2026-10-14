"""Per-prime inequalities of Proposition 4.10 and the sharpness of Lemma 4.9, independent check."""
import numpy as np
from scipy.optimize import linprog, minimize
from pgl2 import table, fourier, lamA, inv_ind

rng = np.random.default_rng(1)


def lp_min_lambda(T, A_eq=None, b_eq=None, A_ub=None, b_ub=None, nonneg=False):
    """min lambda_A(f) over class functions f (values on classes) subject to linear
    constraints on f.  Variables: f (k), s (k) with s >= |fhat|."""
    k = len(T['classes'])
    F = (T['X'] * T['sizes']) / T['G']          # fhat = F f
    d = T['dims']
    c = np.concatenate([np.zeros(k), d])
    Aub = [np.hstack([F, -np.eye(k)]), np.hstack([-F, -np.eye(k)])]
    bub = [np.zeros(k), np.zeros(k)]
    if A_ub is not None:
        Aub.append(np.hstack([A_ub, np.zeros((A_ub.shape[0], k))])); bub.append(b_ub)
    Aeq = None if A_eq is None else np.hstack([A_eq, np.zeros((A_eq.shape[0], k))])
    bounds = [(0, None) if nonneg else (None, None)] * k + [(0, None)] * k
    res = linprog(c, A_ub=np.vstack(Aub), b_ub=np.concatenate(bub), A_eq=Aeq, b_eq=b_eq,
                  bounds=bounds, method='highs')
    assert res.status == 0, res.message
    return res.fun, res.x[:k]


def run(l):
    T = table(l)
    G, sz, X, d = T['G'], T['sizes'], T['X'], T['dims']
    one = inv_ind(T)
    mu0 = (one * sz).sum() / G
    b = fourier(T, one)
    ratio = np.abs(b[1:]) / d[1:]
    lam0 = lamA(T, one)
    eps = np.sign(b)
    Psi = (eps * d) @ X
    on_inv = Psi[one > 0]
    out = dict(l=l, mu0=mu0, mu0_exact=l / (l * l - 1), lam0=lam0, lam0_exact=(l * l + 1) / (l + 1),
               max_b_over_dim=ratio.max(), target=1 / (l * l - 1), all_b_nonzero=bool(np.all(np.abs(b) > 1e-12)),
               Psi_min=Psi.min(), Psi_min_target=-2 * (l - 1), Psi_min_on_inv=on_inv.min(),
               Psi_inv_target=(l - 1) ** 2)
    # sigma LP: min lambda(v) s.t. E v = 0, E_Inv v = 1
    Aeq = np.vstack([sz / G, one * sz / (mu0 * G)])
    sig, v = lp_min_lambda(T, A_eq=Aeq, b_eq=np.array([0.0, 1.0]))
    out['sigma_LP'] = sig
    # L(r) LP: min lambda(h) s.t. h>=0, E h = 1, E_Inv h >= r
    Ls = {}
    for r in [1.0, 1.5, 2.0, 2.5, 3.0, 4.0, l / 2, l - 1, l - 1 / l]:
        if r * mu0 > 1 + 1e-12:
            continue
        val, h = lp_min_lambda(T, A_eq=(sz / G)[None, :], b_eq=np.array([1.0]),
                               A_ub=-(one * sz / (mu0 * G))[None, :], b_ub=np.array([-r]), nonneg=True)
        Ls[r] = val
    out['L'] = Ls
    return out, T


def iota_search(T, rt_target, trials=60):
    """nonconvex: min lambda(v^2) over v with E v=0, E v^2=1, (E_Inv v)^2 = rt_target."""
    G, sz = T['G'], T['sizes']
    one = inv_ind(T); mu0 = (one * sz).sum() / G
    k = len(sz)
    best = np.inf
    cons = [{'type': 'eq', 'fun': lambda v: (sz * v).sum() / G},
            {'type': 'eq', 'fun': lambda v: (sz * v * v).sum() / G - 1},
            {'type': 'eq', 'fun': lambda v: (one * sz * v).sum() / (mu0 * G) - np.sqrt(rt_target)}]
    for _ in range(trials):
        v0 = rng.normal(size=k)
        res = minimize(lambda v: lamA(T, v * v), v0, constraints=cons, method='SLSQP',
                       options=dict(maxiter=500, ftol=1e-10))
        if res.success:
            v = res.x
            if all(abs(c['fun'](v)) < 1e-6 for c in cons):
                best = min(best, lamA(T, v * v))
    return best


if __name__ == '__main__':
    PRIMES = [p for p in range(5, 98) if all(p % q for q in range(2, p))]
    allok = True
    for l in PRIMES:
        o, T = run(l)
        ok = all(abs(v - (1 + l * (r - 1))) < 1e-7 for r, v in o['L'].items())
        allok &= ok
        print(f"l={l}: mu0 {o['mu0']:.6f}/{o['mu0_exact']:.6f} lam0 {o['lam0']:.6f}/{o['lam0_exact']:.6f} "
              f"max|b|/dim {o['max_b_over_dim']:.3e} vs {o['target']:.3e}; all b!=0 {o['all_b_nonzero']}; "
              f"Psi min {o['Psi_min']:.4f} (target {o['Psi_min_target']}), min on Inv {o['Psi_min_on_inv']:.4f} "
              f"(target {o['Psi_inv_target']}); sigma_LP {o['sigma_LP']:.4f} (claim >= l={l})")
        print('    L(r) = min lam(h), h>=0, Eh=1, E_Inv h>=r :  ' +
              '  '.join(f"r={r:g}: L={v:.4f} [lr-2(l-1)={l*r-2*(l-1):.2f}, r^2={r*r:.2f}]" for r, v in o['L'].items()))
        print(f"    Lemma 4.9 sharpness: L(r) = 1 + l(r-1) for all r tested: {ok}")
    print(f"Lemma 4.9 sharpness, all primes 5 <= l <= 97: {allok}")
    print('--- nonconvex iota search (min lambda(v^2)/rt at fixed rt) ---')
    for l in [5, 7, 11]:
        T = table(l)
        for rt in [1.5, 2.0, 2.5, 3.0, 3.5]:
            if rt > (l * l - 1) / l:
                continue
            bst = iota_search(T, rt)
            print(f"l={l} rt={rt}: min lam(v^2) = {bst:.4f}  iota = {bst/rt:.4f}  "
                  f"[analytic lower bound l - 2(l-1)/rt = {l-2*(l-1)/rt:.4f}; audit (l-1)(l/(l+1)-2/rt) = {(l-1)*(l/(l+1)-2/rt):.4f}]")
