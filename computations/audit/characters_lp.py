"""Independent audit of Theorem B1 (auditor's own code; does not import ../littlewood.py).

Characters of PGL2(F_l) are obtained from the GL2(F_l) table (Fulton-Harris / Piatetski-Shapiro) restricted to
characters with trivial central character, evaluated on *actual group elements* via eigenvalues in F_{l^2}.
For l <= 13 the class functions are checked on the brute-forced group (orthonormality summed over all elements,
constancy on true conjugacy classes computed by orbit enumeration).  Then exact LPs (HiGHS) on class functions, over the full range of the mean mu (LP 3).
"""
import itertools, math, sys
import numpy as np
from scipy.optimize import linprog


def legendre(a, l):
    a %= l
    if a == 0:
        return 0
    return 1 if pow(a, (l - 1) // 2, l) == 1 else -1


def nonsq(l):
    return next(e for e in range(2, l) if legendre(e, l) == -1)


class F2:
    """F_{l^2} = F_l[s], s^2 = eps.  elements (a,b) = a + b s"""
    def __init__(self, l):
        self.l, self.eps = l, nonsq(l)
        # generator of F_{l^2}^x
        n = l * l - 1
        primes = [q for q in range(2, n + 1) if n % q == 0 and all(q % r for r in range(2, int(q ** .5) + 1))]
        for a in range(l):
            for b in range(1, l):
                g = (a, b)
                if all(self.pow(g, n // q) != (1, 0) for q in primes):
                    self.gen = g
                    break
            else:
                continue
            break
        self.dlog = {}
        x = (1, 0)
        for k in range(n):
            self.dlog[x] = k
            x = self.mul(x, self.gen)

    def mul(self, x, y):
        l = self.l
        return ((x[0] * y[0] + self.eps * x[1] * y[1]) % l, (x[0] * y[1] + x[1] * y[0]) % l)

    def pow(self, x, k):
        r = (1, 0)
        while k:
            if k & 1:
                r = self.mul(r, x)
            x = self.mul(x, x)
            k >>= 1
        return r

    def sqrt(self, d):
        """square root of d in F_l (d maybe nonsquare) as element of F_{l^2}"""
        l = self.l
        d %= l
        for a in range(l):
            if (a * a - d) % l == 0:
                return (a, 0)
        # d = eps * b^2
        for b in range(l):
            if (self.eps * b * b - d) % l == 0:
                return (0, b)
        raise ValueError


def element_data(M, l, K):
    """For a GL2 matrix M: returns ('e'|'u'|'s'|'n', eigenvalue info) using eigenvalues in F_{l^2}."""
    a, b, c, d = M
    t, D = (a + d) % l, (a * d - b * c) % l
    disc = (t * t - 4 * D) % l
    inv2 = pow(2, l - 2, l)
    if disc == 0:
        lam = t * inv2 % l
        if (b, c) == (0, 0) and a == d:
            return ("e", (lam,))
        return ("u", (lam,))
    r = K.sqrt(disc)
    if r[1] == 0:
        l1 = (t + r[0]) * inv2 % l
        l2 = (t - r[0]) * inv2 % l
        return ("s", (l1, l2))
    z1 = (t * inv2 % l, r[1] * inv2 % l)
    z2 = (t * inv2 % l, (-r[1]) * inv2 % l)
    return ("n", (z1, z2))


def pgl2_characters(l, K):
    """list of (name, dim, f) with f(data)->value; PGL2 irreps."""
    g = next(x for x in range(2, l) if all(pow(x, (l - 1) // q, l) != 1 for q in range(2, l) if (l - 1) % q == 0))
    dl = {pow(g, i, l): i for i in range(l - 1)}
    out = []

    def det_of(data):
        typ, v = data
        if typ in "eu":
            return v[0] * v[0] % l
        if typ == "s":
            return v[0] * v[1] % l
        z = K.mul(v[0], v[1])
        return z[0]

    out.append(("1", 1, lambda dt: 1.0))
    out.append(("sgn", 1, lambda dt: float(legendre(det_of(dt), l))))
    stv = {"e": l, "u": 0, "s": 1, "n": -1}
    out.append(("St", l, lambda dt: float(stv[dt[0]])))
    out.append(("sgnSt", l, lambda dt: float(stv[dt[0]] * legendre(det_of(dt), l))))
    # principal series W(alpha, alpha^-1), alpha^2 != 1, alpha ~ alpha^-1 : alpha = j, j=1..(l-3)/2 in Z/(l-1)
    for j in range(1, (l - 3) // 2 + 1):
        def f(dt, j=j):
            typ, v = dt
            if typ == "e":
                return float(l + 1)
            if typ == "u":
                return 1.0
            if typ == "s":
                r = v[0] * pow(v[1], l - 2, l) % l
                return 2 * math.cos(2 * math.pi * j * dl[r] / (l - 1))
            return 0.0
        out.append((f"PS{j}", l + 1, f))
    # discrete series X(phi), phi on F_{l^2}^x trivial on F_l^x: phi(z) = exp(2 pi i k dlog(z) (l-1)/(l^2-1))
    # i.e. character of order dividing l+1: phi = omega^{(l-1) k}, k = 1..l, phi^2 != 1 -> k != (l+1)/2, k ~ -k
    n = l * l - 1
    for k in range(1, (l - 1) // 2 + 1):
        def f(dt, k=k):
            typ, v = dt
            if typ == "e":
                return float(l - 1)
            if typ == "u":
                return -1.0
            if typ == "s":
                return 0.0
            e = K.dlog[v[0]]
            return -2 * math.cos(2 * math.pi * k * (l - 1) * e / n)
        out.append((f"DS{k}", l - 1, f))
    return out


def classes(l, K):
    """class representatives (as GL2 matrices) + sizes, from parametrisation (independent of brute force)."""
    eps = K.eps
    reps = [("e", (1, 0, 0, 1), 1), ("u", (1, 1, 0, 1), l * l - 1)]
    g = next(x for x in range(2, l) if all(pow(x, (l - 1) // q, l) != 1 for q in range(2, l) if (l - 1) % q == 0))
    for i in range(1, (l - 3) // 2 + 1):
        reps.append((f"s{i}", (pow(g, i, l), 0, 0, 1), l * (l + 1)))
    reps.append(("is", (l - 1, 0, 0, 1), l * (l + 1) // 2))
    # nonsplit: z = gen^{(l-1) j}? projective classes: z in F_{l^2}^x / F_l^x cyclic of order l+1, generated by gen
    # matrix of multiplication by a + b s on basis (1, s): [[a, eps b],[b, a]]
    seen = set()
    for j in range(1, l + 1):
        z = K.pow(K.gen, j)  # image in quotient has order (l+1)/gcd
        a, b = z
        if b == 0:
            continue
        M = (a, eps * b % l, b, a)
        # invariant tr^2/det
        t, D = 2 * a % l, (a * a - eps * b * b) % l
        inv = t * t * pow(D, l - 2, l) % l
        if inv in seen:
            continue
        seen.add(inv)
        name = "in" if t == 0 else f"n{len(seen)}"
        reps.append((name, M, l * (l - 1) // (2 if t == 0 else 1)))
    assert len(reps) == l + 2, (l, len(reps))
    assert sum(r[2] for r in reps) == l * (l * l - 1)
    return reps


def brute(l, K, chars):
    els = []
    for a, b, c, d in itertools.product(range(l), repeat=4):
        if (a * d - b * c) % l == 0:
            continue
        lead = next(x for x in (a, b, c, d) if x)
        if lead != 1:
            continue
        els.append((a, b, c, d))
    assert len(els) == l * (l * l - 1)
    idx = {e: i for i, e in enumerate(els)}

    def norm(M):
        a, b, c, d = (x % l for x in M)
        lead = next(x for x in (a, b, c, d) if x)
        iv = pow(lead, l - 2, l)
        return tuple(x * iv % l for x in (a, b, c, d))

    def mul(X, Y):
        return norm((X[0] * Y[0] + X[1] * Y[2], X[0] * Y[1] + X[1] * Y[3], X[2] * Y[0] + X[3] * Y[2], X[2] * Y[1] + X[3] * Y[3]))

    def inv(X):
        return norm((X[3], -X[1], -X[2], X[0]))
    # true conjugacy classes
    cl = [-1] * len(els)
    ncl = 0
    sizes = []
    for i, x in enumerate(els):
        if cl[i] >= 0:
            continue
        orb = {idx[mul(mul(g, x), inv(g))] for g in els}
        for j in orb:
            cl[j] = ncl
        sizes.append(len(orb))
        ncl += 1
    V = np.array([[f(element_data(x, l, K)) for x in els] for (_, _, f) in chars])
    G = V @ V.T / len(els)
    orth = np.abs(G - np.eye(len(chars))).max()
    const = max(np.ptp(V[:, [j for j in range(len(els)) if cl[j] == c]], axis=1).max() for c in range(ncl))
    trz = sum(1 for x in els if (x[0] + x[3]) % l == 0)
    invol = sum(1 for x in els if x != (1, 0, 0, 1) and mul(x, x) == (1, 0, 0, 1))
    return ncl, sorted(sizes), orth, const, trz, invol


def setup(l):
    K = F2(l)
    chars = pgl2_characters(l, K)
    reps = classes(l, K)
    order = l * (l * l - 1)
    X = np.array([[f(element_data(M, l, K)) for (_, M, _) in reps] for (_, _, f) in chars])
    sizes = np.array([s for (_, _, s) in reps], float)
    dims = np.array([d for (_, d, _) in chars], float)
    Fm = X * sizes / order
    w = sizes / order
    names = [r[0] for r in reps]
    return K, chars, reps, X, sizes, dims, Fm, w, names, order


def lp_min(Fm, dims, w, D, cmu=0.0, Mcap=None, Meq=None):
    nc, npi = Fm.shape[1], Fm.shape[0]
    c = np.concatenate([cmu * w, dims])
    A = np.block([[Fm, -np.eye(npi)], [-Fm, -np.eye(npi)]])
    b = np.zeros(2 * npi)
    if Mcap is not None:
        A = np.vstack([A, np.concatenate([w, np.zeros(npi)])])
        b = np.concatenate([b, [Mcap]])
    Aeq = beq = None
    if Meq is not None:  # mean fixed exactly
        Aeq, beq = np.concatenate([w, np.zeros(npi)])[None, :], [Meq]
    bounds = [(1.0 if i in D else 0.0, None) for i in range(nc)] + [(0, None)] * npi
    r = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
    assert r.status == 0, r.message
    phi = r.x[:nc]
    return r.fun, phi, float(w @ phi), float(np.abs(Fm @ phi) @ dims)


def main(ls):
    for l in ls:
        K, chars, reps, X, sizes, dims, Fm, w, names, order = setup(l)
        orth = np.abs((X * sizes) @ X.T / order - np.eye(len(chars))).max()
        line = f"l={l:3d} classes={len(reps)} orth(param)={orth:.1e} sum dim^2 ok={int(dims @ dims) == order}"
        if l <= 13:
            ncl, bsz, borth, const, trz, invol = brute(l, K, chars)
            line += (f" | brute: #classes={ncl} sizes match={bsz == sorted(sizes.astype(int).tolist())}"
                     f" orth(all elements)={borth:.1e} const-on-classes={const:.1e} #tr0={trz} #invol={invol} (l^2={l*l})")
        print(line)
        D = {names.index("is"), names.index("in")}
        oneInv = np.zeros(len(reps)); oneInv[list(D)] = 1
        coef = Fm @ oneInv
        lam0 = float(np.abs(coef) @ dims)
        mu0 = float(w @ oneInv)
        eps = np.sign(coef)
        Psi = (eps * dims) @ X
        print(f"   min|coef|={np.abs(coef).min():.3e}; lam(1_Inv)={lam0:.6f} vs (l^2+1)/(l+1)={(l*l+1)/(l+1):.6f};"
              f" mu0={mu0:.6f} vs l/(l^2-1)={l/(l*l-1):.6f}")
        pv = dict(zip(names, np.round(Psi, 6)))
        others = sorted(set(np.round(Psi[[i for i, n in enumerate(names) if n not in ('e', 'u', 'is', 'in')]], 6)))
        print(f"   Psi: e={pv['e']} [(l-1)^2={(l-1)**2}] u={pv['u']} [-(l-1)] is={pv['is']} [l^2-1={l*l-1}]"
              f" in={pv['in']} [(l-1)^2] regular values={others} [0, -2(l-1)={-2*(l-1)}]; E[1_Inv Psi]={w @ (oneInv*Psi):.6f}")
        # sign pattern claims
        sg = dict(zip([c[0] for c in chars], np.sign(coef).astype(int)))
        eta = legendre(-1, l)
        # LP 1: min lam + 2(l-1) mu  over majorants  -> should be l+1 (=lam0 + 2(l-1)mu0)
        val, phi, mu, lam = lp_min(Fm, dims, w, D, cmu=2 * (l - 1))
        print(f"   LP min lam+2(l-1)mu = {val:.8f}  (claim l+1 = {l+1});  attained at mu={mu:.6f}, lam={lam:.6f}")
        # LP 2: Pareto lam*(M); min M lam*(M) on a fine grid in [mu0, 0.5]
        best = (1e9, None)
        for M in np.concatenate([mu0 * np.exp(np.linspace(0, math.log(0.5 / mu0), 400)), [mu0 * (1 + 1e-9)]]):
            _, ph, m_, la = lp_min(Fm, dims, w, D, Mcap=M)
            if m_ * la < best[0]:
                best = (m_ * la, M)
        kap = l * (l * l + 1) / ((l + 1) * (l * l - 1))
        print(f"   inf mu*lam over grid (400 pts) = {best[0]:.8f} at M={best[1]:.5f};  kappa_l = {kap:.8f}; 1-1/l = {1-1/l:.5f}")
        # check near mu = 1/2 (k = 1): is mu*lam >= kappa for mu in (lam0/(2(l-1)), l/(2(l-1))]?
        lo, hi = lam0 / (2 * (l - 1)), l / (2 * (l - 1))
        vals = []
        for M in np.linspace(lo, hi, 6):
            _, ph, m_, la = lp_min(Fm, dims, w, D, Mcap=M)
            vals.append((round(M, 4), round(m_ * la, 4)))
        print(f"   [mu near 1/2, k=1] mu-cap -> min mu*lam (on the LP's lam-optimal phi): {vals}")
        # LP 3: full mu range (Theorem B1 is stated for every mu).  lam*(mu) = min lam with mean EXACTLY mu, on
        # 200 points in [mu0, 1/2], 200 in [1/2, 1], 100 in [1, 3] (plus 1/2 +- 1e-4, 1 +- 1e-4); compare with
        # the three-term bound max{lam0 - 2(l-1)(mu-mu0), l - (l-1)mu, mu} of Theorem B1.
        grid = np.unique(np.concatenate([mu0 * np.exp(np.linspace(0, math.log(0.5 / mu0), 200)),
                                         np.linspace(0.5, 1, 200), np.linspace(1, 3, 100),
                                         [0.5 - 1e-4, 0.5 + 1e-4, 1 - 1e-4, 1 + 1e-4]]))
        prods, gaps, hi = [], [], 1e9
        for M in grid:
            _, ph, m_, la = lp_min(Fm, dims, w, D, Meq=M)
            b1 = max(lam0 - 2 * (l - 1) * (m_ - mu0), l - (l - 1) * m_, m_)
            prods.append(m_ * la)
            gaps.append(la - b1)
            if M >= 0.5:
                hi = min(hi, m_ * la)
        viol = sum(1 for g in gaps if g < -1e-7)
        print(f"   [full mu range, {len(grid)} pts in [mu0, 3]] min mu*lam = {min(prods):.8f} (kappa_l = {kap:.8f});"
              f" min over mu >= 1/2 = {hi:.6f}; points with lam* below the B1 bound: {viol};"
              f" max |lam* - B1 bound| = {max(abs(g) for g in gaps):.1e}")
        sys.stdout.flush()


if __name__ == "__main__":
    main([int(a) for a in sys.argv[1:]])
