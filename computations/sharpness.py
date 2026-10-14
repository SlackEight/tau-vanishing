"""Sharpness of the three-term bound of Theorem B1 (paper, Remark 4.3).

The three-term bound b(mu) = max{lam0 - 2(l-1)(mu - mu0), l - (l-1)mu, mu} is piecewise linear with breakpoints
mu1 = 1/(l-1) (value l-1) and 1 (value 1). Remark 4.3 proves that it is attained for every mu >= mu0 by exhibiting
majorants at the breakpoints; the only nontrivial one is

    phi1 = 1_Inv + 2/(l-1)^2 * 1_Nreg,   Nreg = nonsplit regular elements that are not involutions,

for which the claims are  mu(phi1) = 1/(l-1)  and  lambda_A(phi1) = l - 1.

This script checks those claims in three independent ways.

  symbolic   general l (SymPy): the Fourier coefficients of phi1 from the character values on nonsplit elements,
             their signs against eps_pi = sign of the coefficient of 1_Inv, lambda_A(phi1) = l-1 in both cases
             l = 1, 3 mod 4, and the value Psi = -2(l-1) on Nreg (root-of-unity sums evaluated by orthogonality).
  table      every prime 5 <= l <= 199: explicit (floating-point) character table on the conjugacy classes;
             orthogonality, mean, lambda_A(phi1), lambda_A(1_Inv), and lambda_A of the convex combinations
             t*1_Inv + (1-t)*phi1 and t*phi1 + (1-t)*1 against b(mu).
  brute      l = 5, 7, 11, 13, 17: no character table at all. lambda_A(phi) = ||C_phi||_1 / |G|, where
             C_phi[g,h] = phi(g h^{-1}) is the (symmetric) convolution matrix on L^2(PGL_2(F_l)) and ||.||_1 is the
             trace norm (sum of |eigenvalues|).

Usage:  python sharpness.py [symbolic|table|brute|all]
"""
import sys
from fractions import Fraction

import numpy as np


def primes_between(a, b):
    return [p for p in range(a, b + 1) if p > 1 and all(p % q for q in range(2, int(p ** 0.5) + 1))]


def bound(l, mu):
    lam0 = Fraction(l * l + 1, l + 1)
    mu0 = Fraction(l, l * l - 1)
    return max(lam0 - 2 * (l - 1) * (mu - mu0), l - (l - 1) * mu, mu)


# --------------------------------------------------------------------------------------------------------------
# symbolic, general l
# --------------------------------------------------------------------------------------------------------------
def symbolic():
    import sympy as sp

    l = sp.symbols("l", positive=True)
    G = l * (l**2 - 1)
    mu0 = l / (l**2 - 1)
    lam0 = (l**2 + 1) / (l + 1)
    nu = 2 / (l - 1) ** 2
    nNreg = l * (l - 1) ** 2 / 2  # (l(l-1)/2 nonsplit tori) x (l-1 non-involutions in each)
    ok = True

    def check(name, expr, target=0):
        nonlocal ok
        r = sp.simplify(expr - target) == 0
        ok &= r
        print(f"  {name}: {r}")

    print("[symbolic, general l]")
    check("mean(phi1) = 1/(l-1)", mu0 + nu * nNreg / G, 1 / (l - 1))
    # Sum over g in Nreg of chi(g) = (l(l-1)/2) * S, S = sum over u in U \ {1, iota} (U = T_n cyclic of order l+1,
    # each class {u, u^-1} has l(l-1) elements). Hence hat(1_Nreg)(pi) = S / (2(l+1)).
    # Character values at u = w^k (k != 0, (l+1)/2): 1 -> 1; sgn -> (-1)^k; St -> -1; sgn.St -> -(-1)^k;
    # chi_xi -> 0; pi_psi_j -> -(z^jk + z^-jk). Root-of-unity sums by orthogonality, with sgn(iota) = -s,
    # s = (-1/l):   sum_{k != 0, (l+1)/2} (-1)^k = -1 + s;   sum_{k != 0,(l+1)/2} z^{jk} = -1 - (-1)^j.
    for s in (1, -1):
        cls = "l = 1 mod 4" if s == 1 else "l = 3 mod 4"
        print(f" case s = {s:+d} ({cls})")
        S = {"1": l - 1, "sgn": -1 + s, "St": -(l - 1), "sgnSt": 1 - s, "chi": 0}
        hatInv = {"1": mu0, "sgn": s / (l**2 - 1), "St": 1 / (l**2 - 1), "sgnSt": s * mu0, "chi": None}
        dims = {"1": 1, "sgn": 1, "St": l, "sgnSt": l}
        coef = {}
        for k in ("1", "sgn", "St", "sgnSt"):
            coef[k] = sp.factor(hatInv[k] + nu * S[k] / (2 * (l + 1)))
        print("  coefficients of phi1:", {k: coef[k] for k in coef})
        check("St coefficient vanishes", coef["St"])
        eps = {"1": 1, "sgn": s, "St": 1, "sgnSt": s}
        # discrete series: j = 1..(l-1)/2, psi_j(iota) = (-1)^j, S = -2(-1 - (-1)^j) = 2(1 + (-1)^j)
        disc = {}
        for par in (1, -1):  # par = psi(iota)
            c = sp.factor(-par / (l + 1) + nu * 2 * (1 + par) / (2 * (l + 1)))
            disc[par] = c
            print(f"  pi_psi with psi(iota) = {par:+d}: coefficient {c}, eps = {-par:+d}")
        # positivity of eps*coef for l >= 5 (each is a rational function; check numerator/denominator signs)
        vals = [eps[k] * coef[k] for k in ("1", "sgn", "sgnSt")] + [(-par) * disc[par] for par in (1, -1)]
        vals.append(1 / (l - 1))  # chi_xi: |coefficient| unchanged, sign xi(-1) = eps
        for v in vals:
            v = sp.factor(v)
            pos = all(v.subs(l, L) > 0 for L in range(5, 400))
            num, den = sp.fraction(v)
            print(f"   eps*coef = {v}: > 0 for 5 <= l < 400: {pos}; numerator, denominator: {num}, {den}")
            ok &= pos
        # number of j in [1,(l-1)/2] with (-1)^j = +1 / -1
        if s == 1:
            n_even, n_odd = (l - 1) / 4, (l - 1) / 4
        else:
            n_even, n_odd = (l - 3) / 4, (l + 1) / 4
        lamA = (sum(eps[k] * coef[k] * dims[k] for k in dims)
                + (l - 3) / 2 * (l + 1) / (l - 1)
                + n_even * (-1) * disc[1] * (l - 1) + n_odd * disc[-1] * (l - 1))
        check("lambda_A(phi1) = sum eps*coef*dim = l - 1", lamA, l - 1)
        # Psi at u in Nreg: sum eps_pi dim_pi chi_pi(u)
        # = 1 + s*sgn(u) + l*(-1) + s*l*(-sgn(u)) + sum_j (-(-1)^j)(l-1)(-(z^jk+z^-jk))
        # sum_j (-1)^j (z^jk + z^-jk) over j = 1..(l-1)/2 = [full sum over Z/(l+1)] - [j=0] - [j=(l+1)/2]
        #   = 0 - 1 - (-1)^{(l+1)/2} (-1)^k = -1 + s*sgn(u)    (k != (l+1)/2)
        for sg in (1, -1):
            psi_val = 1 + s * sg - l - s * l * sg + (l - 1) * (-1 + s * sg)
            check(f"Psi(u) = -2(l-1) for sgn(u) = {sg:+d}", psi_val, -2 * (l - 1))
        check("E[phi1 Psi] = lam0 - 2(l-1)(mu1 - mu0) = l - 1",
              lam0 + nu * (-2 * (l - 1)) * nNreg / G, l - 1)
    check("branches 1 and 2 meet at mu1 = 1/(l-1) with value l-1",
          lam0 - 2 * (l - 1) * (1 / (l - 1) - mu0) - (l - (l - 1) / (l - 1)))
    print("symbolic: all True" if ok else "symbolic: FAILURE")
    return ok


# --------------------------------------------------------------------------------------------------------------
# explicit class-level character table (floating point)
# --------------------------------------------------------------------------------------------------------------
def class_table(l):
    """Classes of PGL_2(F_l) with sizes and labels, and the character table (rows = irreducibles)."""
    n_s, n_n = l - 1, l + 1
    classes = [("1", None, 1), ("unip", None, l * l - 1)]
    # split: diag(a,1) up to a <-> a^-1, a = g^k, k = 1..(l-1)/2 ; k = (l-1)/2 is the split involution
    for k in range(1, (l - 1) // 2 + 1):
        size = l * (l + 1) // 2 if 2 * k == l - 1 else l * (l + 1)
        classes.append(("s", k, size))
    for k in range(1, (l + 1) // 2 + 1):
        size = l * (l - 1) // 2 if 2 * k == l + 1 else l * (l - 1)
        classes.append(("n", k, size))
    sizes = np.array([c[2] for c in classes], float)
    G = l * (l * l - 1)
    assert sizes.sum() == G
    s = 1 if l % 4 == 1 else -1

    def sgn(c):
        t, k, _ = c
        if t in ("1", "unip"):
            return 1
        return (-1) ** k  # index-2 subgroup of each cyclic torus is its intersection with PSL_2

    chars, dims, names = [], [], []

    def add(name, f, d):
        chars.append([f(c) for c in classes]); dims.append(d); names.append(name)

    add("1", lambda c: 1.0, 1)
    add("sgn", lambda c: float(sgn(c)), 1)
    st = {"1": l, "unip": 0, "s": 1, "n": -1}
    add("St", lambda c: float(st[c[0]]), l)
    add("sgnSt", lambda c: float(sgn(c) * st[c[0]]), l)
    for j in range(1, (l - 3) // 2 + 1):  # xi = x -> e(jk/(l-1)), xi^2 != 1 ; j = 1..(l-3)/2
        def f(c, j=j):
            t, k, _ = c
            if t == "1": return float(l + 1)
            if t == "unip": return 1.0
            if t == "s": return 2 * np.cos(2 * np.pi * j * k / n_s)
            return 0.0
        add(f"chi{j}", f, l + 1)
    for j in range(1, (l - 1) // 2 + 1):  # psi_j on Z/(l+1), psi^2 != 1
        def f(c, j=j):
            t, k, _ = c
            if t == "1": return float(l - 1)
            if t == "unip": return -1.0
            if t == "s": return 0.0
            return -2 * np.cos(2 * np.pi * j * k / n_n)
        add(f"pi{j}", f, l - 1)
    X = np.array(chars)
    return classes, sizes, X, np.array(dims, float), names, G, s


def table(primes):
    print("[table] explicit character table on classes, floating point")
    allok = True
    for l in primes:
        classes, sizes, X, dims, names, G, s = class_table(l)
        gram = (X * sizes) @ X.T / G
        orth = np.abs(gram - np.eye(len(dims))).max()
        inv = np.array([1.0 if (c[0] == "s" and 2 * c[1] == l - 1) or (c[0] == "n" and 2 * c[1] == l + 1) else 0.0
                        for c in classes])
        nreg = np.array([1.0 if c[0] == "n" and 2 * c[1] != l + 1 else 0.0 for c in classes])
        phi1 = inv + 2.0 / (l - 1) ** 2 * nreg
        one = np.ones(len(classes))

        def hat(phi):
            return (X * sizes) @ phi / G

        def lamA(phi):
            return float(np.abs(hat(phi)) @ dims)

        def mean(phi):
            return float(sizes @ phi / G)

        eps = np.sign(hat(inv))
        Psi = (eps * dims) @ X
        psi_nreg = Psi[nreg == 1]
        psi_sreg = Psi[np.array([c[0] == "s" and 2 * c[1] != l - 1 for c in classes])]
        h1 = hat(phi1)
        signs_ok = bool(np.all(eps * h1 > -1e-12))
        st_zero = abs(h1[names.index("St")]) < 1e-12
        minpos = float(np.min(np.abs(np.delete(h1, names.index("St")))))
        lam1 = lamA(phi1)
        dev = 0.0
        for t in np.linspace(0, 1, 11):
            for a, b in ((inv, phi1), (phi1, one)):
                phi = t * a + (1 - t) * b
                mu = mean(phi)
                dev = max(dev, abs(lamA(phi) - float(bound(l, Fraction(mu).limit_denominator(10**12)))))
        ok = (orth < 1e-10 and abs(mean(phi1) - 1 / (l - 1)) < 1e-12 and abs(lam1 - (l - 1)) < 1e-9
              and abs(lamA(inv) - (l * l + 1) / (l + 1)) < 1e-9 and signs_ok and st_zero
              and np.allclose(psi_nreg, -2 * (l - 1)) and np.allclose(psi_sreg, 0) and dev < 1e-9)
        allok &= ok
        print(f"  l={l:3d}: orth {orth:.1e}  mean(phi1)*(l-1)={mean(phi1)*(l-1):.12f}  lam_A(phi1)-(l-1)={lam1-(l-1):+.1e}"
              f"  signs ok {signs_ok}  St coef 0 {st_zero}  min|coef| (others) {minpos:.2e}"
              f"  Psi on Nreg {sorted(set(np.round(psi_nreg, 9)))}  Psi on split reg {sorted(set(np.round(psi_sreg, 9)))}"
              f"  max|lam_A(segment) - b| {dev:.1e}  {'OK' if ok else 'FAIL'}")
    print("table: all OK" if allok else "table: FAILURE")
    return allok


# --------------------------------------------------------------------------------------------------------------
# brute force: no character table
# --------------------------------------------------------------------------------------------------------------
def brute(primes):
    print("[brute] lambda_A = trace norm of the convolution matrix / |G|  (no character table)")
    allok = True
    for l in primes:
        sq = {(x * x) % l for x in range(1, l)}
        els = []
        for a in range(l):
            for b in range(l):
                for c in range(l):
                    for d in range(l):
                        if (a * d - b * c) % l == 0:
                            continue
                        first = next(v for v in (a, b, c, d) if v)
                        if first == 1:  # normalised representative of the class mod scalars
                            els.append((a, b, c, d))
        M = np.array(els, dtype=np.int64)
        G = len(M)
        assert G == l * (l * l - 1)
        a, b, c, d = (M[:, i] for i in range(4))
        # g h^{-1} ~ g adj(h), adj(h) = [[d,-b],[-c,a]]
        # trace of g*adj(h) = a_g d_h - b_g c_h - c_g b_h + d_g a_h
        tr = (a[:, None] * d[None, :] - b[:, None] * c[None, :] - c[:, None] * b[None, :] + d[:, None] * a[None, :]) % l
        det = ((a * d - b * c) % l)
        dd = (det[:, None] * det[None, :]) % l
        disc = (tr * tr - 4 * dd) % l
        is_inv = tr == 0
        issq = np.zeros(l, bool); issq[list(sq)] = True
        nonsq = (disc != 0) & ~issq[disc]
        is_nreg = nonsq & ~is_inv
        n_inv = int(is_inv[:, 0].sum()); n_nreg = int(is_nreg[:, 0].sum())
        mats = {"1_Inv": is_inv.astype(float),
                "phi1": is_inv.astype(float) + 2.0 / (l - 1) ** 2 * is_nreg.astype(float),
                "1": np.ones((G, G))}
        res = {}
        for k, C in mats.items():
            assert np.allclose(C, C.T)
            ev = np.linalg.eigvalsh(C)
            res[k] = (float(C[:, 0].mean()), float(np.abs(ev).sum() / G))
        mu1, lam1 = res["phi1"]
        ok = (n_inv == l * l and n_nreg == l * (l - 1) ** 2 // 2 and abs(mu1 - 1 / (l - 1)) < 1e-12
              and abs(lam1 - (l - 1)) < 1e-8 and abs(res["1_Inv"][1] - (l * l + 1) / (l + 1)) < 1e-8
              and abs(res["1"][1] - 1) < 1e-8)
        allok &= ok
        print(f"  l={l:2d}: |G|={G}  |Inv|={n_inv}  |Nreg|={n_nreg} (pred {l*(l-1)**2//2})"
              f"  lam_A(1_Inv)={res['1_Inv'][1]:.10f} (pred {(l*l+1)/(l+1):.10f})"
              f"  mean(phi1)={mu1:.10f} (pred {1/(l-1):.10f})  lam_A(phi1)={lam1:.10f} (pred {l-1})  {'OK' if ok else 'FAIL'}")
    print("brute: all OK" if allok else "brute: FAILURE")
    return allok


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    ok = True
    if what in ("symbolic", "all"):
        ok &= symbolic()
    if what in ("table", "all"):
        ok &= table(primes_between(5, 199))
    if what in ("brute", "all"):
        ok &= brute([5, 7, 11, 13, 17])
    print("ALL CHECKS PASSED" if ok else "SOME CHECK FAILED")
