"""Independent re-implementation of the Proposition 4.10 sieve optimisation.
Minimise  t*A(c) + B(c)  over c >= 0, sum c = 1, where (models)
  I   (audit's model)  A = sum c_m^2/m,  B = sum c_m c_n lcm(m,n)
  II  (exact two-point = Bellaiche's phi_l, lambda_A):
        A = sum c_m^2/R(m), R = prod r_l, r_l = (l^2-l-1)/l,
        B = sum_{m,n} c_m c_n [prod_{s} sigma_l prod_{i} iota_l - delta_{mn}/R(m)]
  III (adversarial per-prime data allowed by the sharp per-prime bounds):
        r_l free in [1+eta, l-1/l], sigma_l = l, iota_l = l - (l-1)/r_l
        (lower envelopes, so the min here lower-bounds every admissible sieve with these r_l)
over squarefree m <= N with all prime factors >= 5 (m = 1 included).
Report min/sqrt(t) (Proposition 4.10 predicts ~ 2*sqrt(AB')... i.e. bounded below) and the optimiser's support."""
import numpy as np, sys, json, time
from math import gcd

rng = np.random.default_rng(12345)


def primes_upto(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i * i::i] = False
    return [int(p) for p in np.nonzero(s)[0]]


def support(N):
    P = [p for p in primes_upto(N) if p >= 5]
    ms = []
    for m in range(1, N + 1):
        x, ok, fac = m, True, []
        for p in P:
            if p * p > x: break
            if x % p == 0:
                x //= p
                if x % p == 0: ok = False; break
                fac.append(p)
        if not ok: continue
        if x > 1:
            if x < 5: continue
            fac.append(x)
        if m == 1 or all(f >= 5 for f in fac):
            if all(m % q for q in (2, 3)):
                ms.append((m, tuple(fac)))
    return ms


def build(ms, model, rmap=None):
    n = len(ms)
    sets = [set(f) for _, f in ms]
    allp = sorted(set().union(*sets))
    if model == 'I':
        r = {l: float(l) for l in allp}; sig = r; iot = r
    elif model == 'II':
        r = {l: (l * l - l - 1) / l for l in allp}
        lam0 = {l: (l * l + 1) / (l + 1) for l in allp}
        dl = {l: l / (l * l - 1) for l in allp}
        sig = {l: (lam0[l] - dl[l]) / (1 - dl[l]) for l in allp}            # lambda(phi)/g~
        iot = {}
        for l in allp:
            d = dl[l]; a = (1 - d) / d; b = d / (1 - d)
            lam_phi2 = 1 + (a - b) * (lam0[l] - d)                          # lambda_A(phi^2)
            iot[l] = lam_phi2 / r[l]
    elif model == 'III':
        r = {l: rmap(l) for l in allp}
        sig = {l: float(l) for l in allp}
        iot = {l: l - (l - 1) / r[l] for l in allp}
    R = np.array([np.prod([r[l] for l in s]) if s else 1.0 for s in sets])
    K = np.empty((n, n))
    for a in range(n):
        for b in range(a, n):
            s = sets[a] ^ sets[b]; i = sets[a] & sets[b]
            v = np.prod([sig[l] for l in s]) * np.prod([iot[l] for l in i])
            if model == 'II' and a == b:
                v -= 1.0 / R[a]
            K[a, b] = K[b, a] = v
    return R, K


def obj(c, t, R, K):
    return t * np.sum(c * c / R) + c @ K @ c


def proj_simplex(v):
    u = np.sort(v)[::-1]; css = np.cumsum(u)
    k = np.nonzero(u * np.arange(1, len(v) + 1) > (css - 1))[0][-1]
    th = (css[k] - 1) / (k + 1)
    return np.maximum(v - th, 0)


def pg(c, t, R, K, iters=1500):
    H = 2 * (t * np.diag(1 / R) + K)
    L = np.abs(H).sum(1).max()  # crude Lipschitz bound
    step = 1.0 / L
    f = obj(c, t, R, K)
    for it in range(iters):
        g = H @ c
        cn = proj_simplex(c - step * g)
        fn = obj(cn, t, R, K)
        if fn > f - 1e-15 * abs(f):
            # try a bigger step search on a local scale
            cn2 = proj_simplex(c - 50 * step * g); f2 = obj(cn2, t, R, K)
            if f2 < f: c, f = cn2, f2; continue
            break
        c, f = cn, fn
    return c, f


def replicator(c, t, R, K, iters=3000):
    # multiplicative updates for min of a quadratic on the simplex (K>0 entrywise)
    H = t * np.diag(1 / R) + K
    for _ in range(iters):
        g = H @ c
        cn = c * (g.max() - g + 1e-12 * g.max())
        s = cn.sum()
        if s <= 0: break
        cn /= s
        if np.abs(cn - c).max() < 1e-13: c = cn; break
        c = cn
    return c, obj(c, t, R, K)


def solve(t, R, K, ms, starts=60):
    n = len(R)
    best = (np.inf, None)
    # singletons and best pairs (exact on 2-element supports)
    diag = t / R + np.diag(K)
    j = int(np.argmin(diag)); best = (diag[j], np.eye(n)[j])
    # random starts
    for s in range(starts):
        kind = s % 4
        if kind == 0: c = rng.dirichlet(np.ones(n))
        elif kind == 1: c = rng.dirichlet(0.05 * np.ones(n))
        elif kind == 2:
            c = np.zeros(n); idx = rng.choice(n, size=min(n, rng.integers(2, 12)), replace=False); c[idx] = 1; c /= c.sum()
        else:
            c = np.exp(-np.abs(np.log(np.array([m for m, _ in ms]) + 1) - 0.5 * np.log(t)) * rng.uniform(0.5, 4)); c /= c.sum()
        c1, f1 = replicator(c, t, R, K)
        c2, f2 = pg(c1, t, R, K)
        if f2 < best[0]: best = (f2, c2)
    return best


RMAPS = {'III_rmax': lambda l: l - 1 / l, 'III_rhalf': lambda l: l / 2, 'III_r2': lambda l: 2.0,
         'III_r1.2': lambda l: 1.2}


def job(args):
    import os
    os.environ['OMP_NUM_THREADS'] = '1'
    model, N, t = args
    global rng
    rng = np.random.default_rng(hash((model, N, t)) % 2**32)
    ms = support(N)
    R, K = build(ms, 'III', RMAPS[model]) if model.startswith('III') else build(ms, model)
    f, c = solve(t, R, K, ms, starts=40 if N > 1000 else 80)
    top = np.argsort(-c)[:4]
    sup = [(ms[i][0], round(float(c[i]), 4)) for i in top if c[i] > 1e-4]
    A = float(np.sum(c * c / R)); Bp = float(c @ K @ c)
    # structured comparisons
    diag = t / R + np.diag(K)
    j = int(np.argmin(diag))
    return dict(model=model, N=N, nsupp=len(ms), t=t, min=f, ratio=f / np.sqrt(t), AB=A * Bp, support=sup,
                best_single=(ms[j][0], float(diag[j] / np.sqrt(t))))


if __name__ == '__main__':
    import multiprocessing as mp
    configs = []
    for model in ['I', 'II'] + list(RMAPS):
        configs += [(model, 400, t) for t in (1e2, 1e3, 1e4)] + [(model, 2500, t) for t in (1e4, 1e5, 1e6)]
    import os
    with mp.Pool(min(18, os.cpu_count() or 1)) as pool:
        out = pool.map(job, configs)
    for o in out:
        print(f"model {o['model']:10s} N={o['N']:5d} |supp|={o['nsupp']:4d} t={o['t']:.0e}: min/sqrt(t)={o['ratio']:.4f} "
              f"A*B={o['AB']:.4f} best single m={o['best_single'][0]} ({o['best_single'][1]:.4f})  top support {o['support']}")
