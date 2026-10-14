"""Theorem B (paper Section 4): the Littlewood-norm inequality for involutions in PGL2(F_l) and the finite-group
facts behind the (1+theta)/2 exponent ceiling.

This script checks only the exact finite-group statements: Theorem B1 (kappa_l), Lemma 4.6 (per-factor bound) and the
linear programs for Conjecture 4.12.  It cannot check analytic constants or logarithmic factors.  Scope (paper 4.5):
only the exponent is a method ceiling, and only for (i) single-l majorant methods (Corollary B2) and (ii)
single-extension certificates with the Lagarias-Odlyzko error shape E = |C|[Omega:H]/m over squarefree mod-l images
(Theorem B3).

Notation (paper Section 4).  G = PGL2(F_l), l >= 5 prime.  For a real class function phi on G:
  mu(phi)     = mean of phi (Haar probability),
  lam(phi)    = sum_pi |phi^(pi)| dim(pi)           (Bellaiche's Littlewood norm lambda_A = Fourier-algebra norm),
  phi^(pi)    = <phi, chi_pi> = (1/|G|) sum_g phi(g) chi_pi(g)   (characters of PGL2(F_l) are real).
A "majorant" of a conjugation-stable D is phi >= 0 with phi >= 1 on D.  D_s = split involution class,
D_n = nonsplit involution class, Inv = D_s u D_n (the image of {tr = 0}).

Modes
  table L...      build the character table of PGL2(F_l) from the standard formulas; check orthogonality, sum dim^2,
                  and (l <= 13) brute-force class sizes and the permutation character of P^1 (= 1 + St) and the
                  induced characters Ind_B^G(mu) (fixed-point formula) against the table.
  lp L...         exact LPs (HiGHS): kappa(l) = inf_phi mu(phi) lam(phi) over majorants of D_s and of Inv, from the
                  Pareto curve lam*(mu) (mean fixed, mu over the FULL range [mu0, 3], see mu_grid);
                  the cost c(X) = min_phi (mu X + lam)/sqrt(X); compare with the Theorem B1 value and with the
                  majorant of Theorem A (Section 4.2), phi_A = 1_{D_s} + (l+1)/(l-1) 1_{D_n}.  Last columns (Inv):
                  min mu*lam over grid points with mu >= 1/2; number of grid points; number of points where
                  lam*(mu) is below the three-term bound of Theorem B1 (must be 0); max |lam*(mu) - B1 bound|.
  prod L1 L2 [L3] majorants of Inv x Inv (x Inv) on PGL2(F_l1) x PGL2(F_l2) (x ...): kappa(product) vs the product
                  of the single-factor kappas (tensorisation test, Conjecture 4.12), over the full mu range.
  subgroups L...  Lemma 4.6 per-factor check over all subgroups of PGL2(F_l) (Theorem B3).

  python littlewood.py table 5 7 11 13 17 29
  python littlewood.py lp 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97
  python littlewood.py prod 5 7          # also: 5 11, 7 11, 11 13, 5 7 11
  python littlewood.py subgroups 5 7 11 13
"""
import itertools
import math
import sys

import numpy as np
from scipy.optimize import linprog


def prim_root(l):
    for g in range(2, l):
        if all(pow(g, (l - 1) // q, l) != 1 for q in range(2, l) if (l - 1) % q == 0 and all(q % r for r in range(2, q))):
            return g
    raise ValueError


def pgl2_table(l):
    """Classes (name, size) and irreducible characters (name, dim, values) of PGL2(F_l), l odd prime >= 5.

    Classes: 'e'; 'u' (unipotent); split s_i = diag(g^i, 1), i = 1..(l-3)/2, and the split involution 'is'
    (i = (l-1)/2); nonsplit n_j = image of gamma^j in F_{l^2}^x / F_l^x (cyclic of order l+1), j = 1..(l-1)/2, and the
    nonsplit involution 'in' (j = (l+1)/2).
    Characters: 1, sgn, St, sgn.St, principal series PS_r (r = 1..(l-3)/2, dim l+1), discrete series DS_s
    (s = 1..(l-1)/2, dim l-1).
    """
    assert l >= 5 and l % 2
    order = l * (l * l - 1)
    cls = [("e", 1, ("e", 0)), ("u", l * l - 1, ("u", 0))]
    for i in range(1, (l - 3) // 2 + 1):
        cls.append((f"s{i}", l * (l + 1), ("s", i)))
    cls.append(("is", l * (l + 1) // 2, ("s", (l - 1) // 2)))
    for j in range(1, (l - 1) // 2 + 1):
        cls.append((f"n{j}", l * (l - 1), ("n", j)))
    cls.append(("in", l * (l - 1) // 2, ("n", (l + 1) // 2)))
    assert sum(c[1] for c in cls) == order

    def sgn(c):
        t, k = c
        return (-1) ** k if t in "sn" else 1

    def st(c):
        t, k = c
        return {"e": l, "u": 0, "s": 1, "n": -1}[t]

    chars = [("1", 1, [1.0 for _ in cls]), ("sgn", 1, [float(sgn(c[2])) for c in cls]),
             ("St", l, [float(st(c[2])) for c in cls]), ("sgnSt", l, [float(sgn(c[2]) * st(c[2])) for c in cls])]
    for r in range(1, (l - 3) // 2 + 1):
        v = []
        for _, _, (t, k) in cls:
            if t == "e":
                v.append(float(l + 1))
            elif t == "u":
                v.append(1.0)
            elif t == "s":
                v.append(2 * math.cos(2 * math.pi * r * k / (l - 1)))
            else:
                v.append(0.0)
        chars.append((f"PS{r}", l + 1, v))
    for s in range(1, (l - 1) // 2 + 1):
        v = []
        for _, _, (t, k) in cls:
            if t == "e":
                v.append(float(l - 1))
            elif t == "u":
                v.append(-1.0)
            elif t == "s":
                v.append(0.0)
            else:
                v.append(-2 * math.cos(2 * math.pi * s * k / (l + 1)))
        chars.append((f"DS{s}", l - 1, v))
    assert len(chars) == len(cls) == l + 2
    return order, cls, chars


def check_table(l, order, cls, chars):
    sizes = np.array([c[1] for c in cls], float)
    X = np.array([ch[2] for ch in chars])
    gram = (X * sizes) @ X.T / order
    err = np.abs(gram - np.eye(len(chars))).max()
    dims = sum(ch[1] ** 2 for ch in chars)
    return err, dims == order


def brute_pgl2(l):
    """Brute-force class data of PGL2(F_l): class sizes by invariant, permutation character on P^1, and
    Ind_B^G(mu) values via the fixed-point formula sum_{fixed x} mu(ratio at x)."""
    g = prim_root(l)
    dlog = {pow(g, i, l): i for i in range(l - 1)}
    els = []
    for a, b, c, d in itertools.product(range(l), repeat=4):
        det = (a * d - b * c) % l
        if det == 0:
            continue
        t = (a, b, c, d)
        lead = next(x for x in t if x)
        if lead != 1:
            continue
        els.append(t)
    assert len(els) == l * (l * l - 1)
    pts = [(x, 1) for x in range(l)] + [(1, 0)]

    def normp(v):
        x, y = v[0] % l, v[1] % l
        if y:
            return ((x * pow(y, l - 2, l)) % l, 1)
        return (1, 0)

    sq = {(x * x) % l for x in range(1, l)}
    out = {}
    for (a, b, c, d) in els:
        det = (a * d - b * c) % l
        tr = (a + d) % l
        # invariant tr^2/det; type via discriminant; identity / unipotent via (g - lambda) structure
        inv_ = (tr * tr * pow(det, l - 2, l)) % l
        disc = (tr * tr - 4 * det) % l
        fixed = []
        for p in pts:
            q = normp((a * p[0] + b * p[1], c * p[0] + d * p[1]))
            if q == p:
                # eigenvalue at p: g v = lam v
                lam = (a * p[0] + b * p[1]) * pow(p[0], l - 2, l) % l if p[0] else (c * p[0] + d * p[1]) * pow(p[1], l - 2, l) % l
                fixed.append((p, lam))
        if (b, c) == (0, 0) and a == d:
            key = "e"
        elif disc == 0:
            key = "u"
        elif disc in sq:
            # split: ratio of eigenvalues r, r ~ 1/r
            (p1, l1), (p2, l2) = fixed
            r = l1 * pow(l2, l - 2, l) % l
            i = dlog[r]
            i = min(i, (l - 1 - i) % (l - 1))
            key = ("s", i)
        else:
            key = ("n", inv_)
        out.setdefault(key, []).append(((a, b, c, d), fixed))
    return out, dlog


def table(ls):
    for l in ls:
        order, cls, chars = pgl2_table(l)
        err, okdim = check_table(l, order, cls, chars)
        line = f"l={l:3d} |G|={order} classes={len(cls)} orthogonality max err={err:.2e} sum dim^2 = |G|: {okdim}"
        if l <= 13:
            bf, dlog = brute_pgl2(l)
            # class sizes: split by ratio exponent, nonsplit grouped by tr^2/det invariant
            ok_sizes = True
            for name, size, (t, k) in cls:
                if t in ("e", "u"):
                    ok_sizes &= len(bf[t]) == size
                elif t == "s":
                    ok_sizes &= len(bf[("s", k)]) == size
            nonsplit_sizes = sorted(len(v) for kk, v in bf.items() if isinstance(kk, tuple) and kk[0] == "n")
            exp_ns = sorted(c[1] for c in cls if c[2][0] == "n")
            ok_sizes &= nonsplit_sizes == exp_ns
            # permutation character on P^1 = 1 + St; Ind_B mu_r = PS_r on split classes
            ok_perm = True
            St = dict(zip([c[0] for c in cls], chars[2][2]))
            for key, lst in bf.items():
                nf = len(lst[0][1])
                if key == "e":
                    ok_perm &= nf == 1 + St["e"]
                elif key == "u":
                    ok_perm &= nf == 1 + St["u"]
                elif key[0] == "s":
                    ok_perm &= nf == 2
                else:
                    ok_perm &= nf == 0
            ok_ind = True
            for r in range(1, (l - 3) // 2 + 1):
                ps = dict(zip([c[2] for c in cls], chars[3 + r][2]))
                for key, lst in bf.items():
                    if isinstance(key, tuple) and key[0] == "s":
                        val = sum(complex(math.cos(2 * math.pi * r * dlog[lam] / (l - 1)), math.sin(2 * math.pi * r * dlog[lam] / (l - 1)))
                                  for _, lam in lst[0][1])
                        # ratio-of-eigenvalue convention: Ind_B(mu) at x is mu(lambda_x / lambda'_x); with projective
                        # normalisation the two fixed points give mu(r) + mu(1/r); compare the real part
                        (p1, l1), (p2, l2) = lst[0][1]
                        rr = l1 * pow(l2, l - 2, l) % l
                        v = 2 * math.cos(2 * math.pi * r * dlog[rr] / (l - 1))
                        ok_ind &= abs(v - ps[("s", key[1])]) < 1e-9
            line += f" | brute force: class sizes {ok_sizes}, perm char = 1+St {ok_perm}, Ind_B mu = PS {ok_ind}"
        print(line)


def fourier_matrix(order, cls, chars):
    sizes = np.array([c[1] for c in cls], float)
    X = np.array([ch[2] for ch in chars])
    F = X * sizes / order  # phi^(pi) = F[pi] . phi
    dims = np.array([ch[1] for ch in chars], float)
    w = sizes / order
    return F, dims, w


def lam_of(phi, F, dims):
    return float(np.abs(F @ phi) @ dims)


def solve(F, dims, w, Didx, X=None, M=None, Meq=None):
    """min lam(phi) + X mu(phi)  [or min lam s.t. mu <= M, or s.t. mu = Meq] over phi >= 0, phi >= 1 on Didx."""
    nc, npi = F.shape[1], F.shape[0]
    c = np.concatenate([np.zeros(nc) if X is None else X * w, dims])
    A = np.block([[F, -np.eye(npi)], [-F, -np.eye(npi)]])
    b = np.zeros(2 * npi)
    if M is not None:
        A = np.vstack([A, np.concatenate([w, np.zeros(npi)])])
        b = np.concatenate([b, [M]])
    Aeq = beq = None
    if Meq is not None:
        Aeq, beq = np.concatenate([w, np.zeros(npi)])[None, :], [Meq]
    bounds = [(1.0 if i in Didx else 0.0, None) for i in range(nc)] + [(0, None)] * npi
    r = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
    if r.status != 0:
        return None
    phi = r.x[:nc]
    return phi, float(w @ phi), lam_of(phi, F, dims)


def mu_grid(m0, ngrid=60):
    """Grid of means covering the FULL range of mu (Theorem B1 is stated for every mu >= mu0):
    ngrid log-spaced points on [mu0, 1/2], ngrid/2 on [1/2, 1], ngrid/4 on [1, 3], and 1/2 +- 1e-4, 1 +- 1e-4."""
    g = np.concatenate([m0 * np.exp(np.linspace(0, math.log(0.5 / m0), ngrid)), np.linspace(0.5, 1, ngrid // 2),
                        np.linspace(1, 3, ngrid // 4), [0.5 - 1e-4, 0.5 + 1e-4, 1 - 1e-4, 1 + 1e-4]])
    return np.unique(g[g >= m0])


def pareto(F, dims, w, Didx, ngrid=60):
    """lam*(mu) = min lam over majorants with mean exactly mu, for mu on mu_grid; returns [(mu, lam*, phi)]."""
    m0 = float(sum(w[i] for i in Didx))
    out = []
    for M in mu_grid(m0, ngrid):
        s = solve(F, dims, w, Didx, Meq=M)
        if s is not None:
            out.append((M, s[2], s[0]))
    return out


def kappa(F, dims, w, Didx, ngrid=60):
    """inf mu*lam over majorants, scanning the Pareto curve lam*(mu) over the full mu range (mu_grid).
    Returns (min mu*lam, (mu, lam, phi) at the minimum, min of mu*lam over grid points with mu >= 1/2)."""
    best = (math.inf, None)
    high = math.inf
    for mu, lam, phi in pareto(F, dims, w, Didx, ngrid):
        if mu * lam < best[0]:
            best = (float(mu * lam), (float(mu), lam, phi))
        if mu >= 0.5:
            high = min(high, float(mu * lam))
    return best[0], best[1], high


def b1_bound(l, mu):
    """the three-term lower bound of Theorem B1 for lam_A at mean mu"""
    lam0 = (l * l + 1) / (l + 1)
    mu0 = l / (l * l - 1)
    return max(lam0 - 2 * (l - 1) * (mu - mu0), l - (l - 1) * mu, mu)


def cost(F, dims, w, Didx, Xs):
    out = []
    for X in Xs:
        phi, mu, lam = solve(F, dims, w, Didx, X=X)
        out.append(((mu * X + lam) / math.sqrt(X), mu, lam))
    return out


def lp(ls):
    print("kappa = inf mu*lam over majorants (Pareto scan). LB columns: crude first-pass dual lower bounds (superseded"
          " by Theorem B1); kappa_B1 = l(l^2+1)/((l+1)(l^2-1)) = mu(1_Inv) lam(1_Inv), the exact value proved in"
          " Theorem B1")
    print(f"{'l':>3} | {'kappa(D_s)':>10} {'LB(D_s)':>8} | {'kappa(Inv)':>10} {'LB(Inv)':>8} | {'phiA mu*lam':>12} {'phiA mu*E_LO':>13} |"
          f" {'min_X c(X) Inv':>14} {'2sqrt(kappa)':>12} | {'kappa_B1':>10} | {'mu>=1/2':>8} {'npts':>4} {'viol':>4} {'max|LP-B1|':>10}")
    for l in ls:
        order, cls, chars = pgl2_table(l)
        F, dims, w = fourier_matrix(order, cls, chars)
        names = [c[0] for c in cls]
        i_s, i_n = names.index("is"), names.index("in")
        ks = kappa(F, dims, w, {i_s})[0]
        pts = pareto(F, dims, w, {i_s, i_n})
        ki = min(mu * lam for mu, lam, _ in pts)
        hi = min(mu * lam for mu, lam, _ in pts if mu >= 0.5)
        gaps = [lam - b1_bound(l, mu) for mu, lam, _ in pts]
        viol = sum(1 for g in gaps if g < -1e-7)
        mus = w[i_s]
        lbs = mus * (l + 1) / 2 * (1 - 2 * mus)
        mui = w[i_s] + w[i_n]
        lbi = mui * (l - 1) / 2 * (2 * l / (l + 1) - 6 * mui)
        phiA = np.zeros(len(cls))
        phiA[i_s], phiA[i_n] = 1.0, (l + 1) / (l - 1)
        muA, lamA = float(w @ phiA), lam_of(phiA, F, dims)
        EA = l * (l + 1) / (l - 1)
        # best cost constant over X: the method's (mu X + lam)/sqrt X, optimised over phi for each X
        Xs = np.exp(np.linspace(math.log(l / 4), math.log(16 * l * l * l), 40))
        cs = cost(F, dims, w, {i_s, i_n}, Xs)
        cmin = min(c[0] for c in cs)
        print(f"{l:3d} | {ks:10.4f} {lbs:8.4f} | {ki:10.4f} {lbi:8.4f} | {muA * lamA:12.4f} {muA * EA:13.4f} |"
              f" {cmin:14.4f} {2 * math.sqrt(ki):12.4f} | {l * (l * l + 1) / ((l + 1) * (l * l - 1)):10.4f} |"
              f" {hi:8.4f} {len(pts):4d} {viol:4d} {max(abs(g) for g in gaps):10.2e}")
        sys.stdout.flush()


def prod(ls):
    tabs = [pgl2_table(l) for l in ls]
    facs = []
    for (order, cls, chars) in tabs:
        F, dims, w = fourier_matrix(order, cls, chars)
        names = [c[0] for c in cls]
        facs.append((F, dims, w, {names.index("is"), names.index("in")}))
    # single-factor kappas
    ks = [kappa(*f)[0] for f in facs]
    F, dims, w = facs[0][0], facs[0][1], facs[0][2]
    D = [facs[0][3]]
    for f in facs[1:]:
        F = np.kron(F, f[0])
        dims = np.kron(dims, f[1])
        w = np.kron(w, f[2])
        D.append(f[3])
    # class index of tuple
    shape = [f[0].shape[1] for f in facs]
    Didx = set()
    for tup in itertools.product(*D):
        idx = 0
        for k, s in zip(tup, shape):
            idx = idx * s + k
        Didx.add(idx)
    kp, data, hi = kappa(F, dims, w, Didx, ngrid=40)
    print(f"factors l = {ls}: single kappas = {[round(k, 4) for k in ks]}, product of kappas = {np.prod(ks):.4f};"
          f" kappa(product group, all majorants, full mu range) = {kp:.4f}; ratio = {kp / np.prod(ks):.4f};"
          f" min mu*lam over grid points with mu >= 1/2 = {hi:.4f}")
    mu, lam, phi = data
    # is the optimiser (close to) a tensor product?  rank of phi reshaped (2 factors only)
    if len(ls) == 2:
        sv = np.linalg.svd(phi.reshape(shape), compute_uv=False)
        print(f"  optimiser: mu = {mu:.5f}, lam = {lam:.3f}; singular values of phi as a matrix: {np.round(sv[:4], 4)}")


if __name__ == "__main__":
    mode = sys.argv[1]
    args = [int(a) for a in sys.argv[2:]]
    if mode != "subgroups":
        {"table": table, "lp": lp, "prod": prod}[mode](args)


# ---------------------------------------------------------------------------------------------------------------
# mode `subgroups L...`: the single-extension (Lagarias-Odlyzko error shape) exponent ceiling, Theorem B3.  For every
# subgroup M of G = PGL2(F_l) (up to conjugacy; all subgroups of PGL2(F_l) are 2-generated) compute
#   nu(M) = max over cosets yM of |yM n Inv|   and   F(M) = |M| |Inv|^2 / (nu(M)^2 |G|),
# and check min_M F(M) = F(T_n) = l^3/((l+1)(l^2-1)) (the nonsplit torus) and that F(M) < 1 only for M = T_n.
# Also evaluates A*E for the split-Cartan (Theorem A) and nonsplit-Cartan certificates.
# The auditor's independent audit/subgroups.py extends this check to every prime 5 <= l <= 61 (maximal-class
# representatives B, N(T_s), N(T_n), S4, A5 and all their subgroups; Dickson), so Lemma 4.6 holds for all l >= 5
# (proof for l >= 61).

def _group_tables(l):
    from group_lemma import pgl2, mul
    els = pgl2(l)
    idx = {e: i for i, e in enumerate(els)}
    n = len(els)
    M = np.empty((n, n), dtype=np.int32)
    for i, a in enumerate(els):
        for j, b in enumerate(els):
            M[i, j] = idx[mul(a, b, l)]
    e = idx[(1, 0, 0, 1)]
    inv = np.array([int(np.where(M[i] == e)[0][0]) for i in range(n)])
    invol = np.array([M[i, i] == e and i != e for i in range(n)])
    return els, M, e, inv, invol


def _closure(gens, M, e):
    S = {e}
    frontier = [e]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = int(M[x, g])
                if y not in S:
                    S.add(y)
                    new.append(y)
        frontier = new
    return frozenset(S)


def subgroups(ls):
    for l in ls:
        els, M, e, inv, invol = _group_tables(l)
        n = len(els)
        # conjugacy class representatives of elements
        seen, reps = set(), []
        for i in range(n):
            if i in seen:
                continue
            cl = {int(M[M[g, i], inv[g]]) for g in range(n)}
            seen |= cl
            reps.append(i)
        subs = set()
        for a in reps:
            for b in range(n):
                subs.add(_closure([a, b], M, e))
        # dedupe up to conjugacy is unnecessary for the invariants; compute nu, F
        S = int(invol.sum())
        lp = S * S / n
        rows = {}
        for H in subs:
            Hl = np.array(sorted(H))
            cos = M[:, Hl]                 # row y = coset yH
            nu = int(invol[cos].sum(axis=1).max())
            F = len(H) * lp / nu ** 2 if nu else float("inf")
            key = (len(H), nu)
            rows.setdefault(key, F)
        Fmin_pred = l ** 3 / ((l + 1) * (l * l - 1))
        Fs = sorted(rows.items(), key=lambda kv: kv[1])
        print(f"l={l}: {len(subs)} subgroups; |Inv|^2/|G| = {lp:.4f}; predicted min F = F(T_n) = {Fmin_pred:.4f}")
        print("   lowest F over (|M|, nu): " + ", ".join(f"(|M|={k[0]}, nu={k[1]}): {v:.4f}" for k, v in Fs[:6]))
        print("   all (|M|, nu) with F < 1: " + str([k for k, v in Fs if v < 1 - 1e-12]))
        # certificates: H = N(T), N0 = T, C = nontrivial coset; A = 1/(2m), E = [G:H]/m (|C| = 1)
        for name, order_T in (("split Cartan (Theorem A)", l - 1), ("nonsplit Cartan", l + 1)):
            def _order(x):
                k, y = 1, x
                while y != e:
                    y, k = int(M[y, x]), k + 1
                return k
            cands = [H for H in subs if len(H) == order_T and any(_order(x) == order_T for x in H)]  # cyclic
            # pick a cyclic subgroup of the right order that is a torus: its normaliser has order 2*order_T
            best = None
            for T in cands:
                Tl = np.array(sorted(T))
                Nm = [g for g in range(n) if set(int(v) for v in M[M[g, Tl], inv[g]]) == set(T)]
                if len(Nm) != 2 * order_T:
                    continue
                Nout = [g for g in Nm if g not in T]
                # m = min over involutions i of #{cosets xN : x^{-1} i x in N_out}
                Nset = set(Nm)
                cosreps, covered = [], set()
                for x in range(n):
                    if x in covered:
                        continue
                    c = {int(M[x, g]) for g in Nm}
                    covered |= c
                    cosreps.append(x)
                Noutset = set(Nout)
                ms = []
                for i in np.where(invol)[0]:
                    ms.append(sum(1 for x in cosreps if int(M[M[inv[x], i], x]) in Noutset))
                m = min(ms)
                A = 1 / (2 * m)
                E = len(cosreps) / m
                best = (m, A, E, A * E)
                break
            if best:
                m, A, E, AE = best
                print(f"   {name}: m = {m}, A = {A:.5f}, E = {E:.4f}, A*E = {AE:.4f}  (>= F_min {Fmin_pred:.4f})")


if __name__ == "__main__" and sys.argv[1] == "subgroups":
    subgroups([int(a) for a in sys.argv[2:]])
