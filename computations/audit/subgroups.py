"""Independent audit of Lemma 4.6 (Theorem B3): for every subgroup M of PGL2(F_l) not containing PSL2 (Dickson: contained in a conjugate
of B, N(T_s), N(T_n), S4, or A5), nu(M) = max_y |yM n Inv| and F(M) = |M||Inv|^2/(nu^2 |G|).
Claim: min F = F(T_n) = l^3/((l+1)(l^2-1)), and F < 1 only for M = T_n (cyclic of order l+1).
Here Inv = trace-zero elements of PGL2.  nu is conjugation invariant, so subgroups of one representative of each
maximal class suffice.  All subgroups of the small maximal groups are found by 2-generator closure.
"""
import itertools, math, sys
import numpy as np


def run(l):
    # all elements of PGL2(F_l) as normalised matrices
    els = []
    for a, b, c, d in itertools.product(range(l), repeat=4):
        if (a * d - b * c) % l == 0:
            continue
        lead = next(x for x in (a, b, c, d) if x)
        if lead != 1:
            continue
        els.append((a, b, c, d))
    Y = np.array(els, dtype=np.int64)
    n = len(els)
    assert n == l * (l * l - 1)
    Inv_count = int(((Y[:, 0] + Y[:, 3]) % l == 0).sum())
    assert Inv_count == l * l

    def norm(M):
        a, b, c, d = (x % l for x in M)
        lead = next(x for x in (a, b, c, d) if x)
        iv = pow(lead, l - 2, l)
        return tuple(x * iv % l for x in (a, b, c, d))

    def mul(X, Z):
        return norm((X[0] * Z[0] + X[1] * Z[2], X[0] * Z[1] + X[1] * Z[3], X[2] * Z[0] + X[3] * Z[2], X[2] * Z[1] + X[3] * Z[3]))

    def closure(gens):
        S = {norm((1, 0, 0, 1))}
        fr = list(S)
        while fr:
            new = []
            for x in fr:
                for g in gens:
                    y = mul(x, g)
                    if y not in S:
                        S.add(y)
                        new.append(y)
            fr = new
        return frozenset(S)

    def order(x):
        k, y = 1, x
        while y != (1, 0, 0, 1):
            y, k = mul(y, x), k + 1
        return k

    def nu(M):
        # max over y of #{m in M : tr(y m) = 0}
        cnt = np.zeros(n, dtype=np.int64)
        for m in M:
            tr = (Y[:, 0] * m[0] + Y[:, 1] * m[2] + Y[:, 2] * m[1] + Y[:, 3] * m[3]) % l
            cnt += (tr == 0)
        return int(cnt.max())

    def all_subgroups(Gset):
        Gl = sorted(Gset)
        subs = set()
        for a in Gl:
            for b in Gl:
                subs.add(closure([a, b]))
        return subs

    g = next(x for x in range(2, l) if all(pow(x, (l - 1) // q, l) != 1 for q in range(2, l) if (l - 1) % q == 0))
    eps = next(e for e in range(2, l) if pow(e, (l - 1) // 2, l) == l - 1)
    lp = l ** 4 / n  # |Inv|^2/|G|
    rows = []
    # Borel: subgroups up to conjugacy = C_d in T_s and U x| C_d
    Ts = (g, 0, 0, 1)
    U = (1, 1, 0, 1)
    for d in [d for d in range(1, l) if (l - 1) % d == 0]:
        cd = norm((pow(g, (l - 1) // d, l), 0, 0, 1))
        rows.append((f"C{d}<T_s", closure([cd])))
        rows.append((f"U.C{d}", closure([cd, U])))
    # N(T_s) all subgroups
    NTs = closure([Ts, (0, 1, 1, 0)])
    assert len(NTs) == 2 * (l - 1)
    for H in all_subgroups(NTs):
        rows.append((f"<N(Ts)|{len(H)}", H))
    # nonsplit torus: multiplication by z = a + b s in basis (1,s): [[a, eps b],[b, a]]; generator of F_{l^2}^x
    def f2mul(x, y):
        return ((x[0] * y[0] + eps * x[1] * y[1]) % l, (x[0] * y[1] + x[1] * y[0]) % l)
    def f2pow(x, k):
        r = (1, 0)
        for _ in range(k):
            r = f2mul(r, x)
        return r
    N2 = l * l - 1
    gen = None
    for a in range(l):
        for b in range(1, l):
            ok = True
            for q in range(2, N2 + 1):
                if N2 % q == 0 and all(q % r for r in range(2, int(q ** .5) + 1)):
                    if f2pow((a, b), N2 // q) == (1, 0):
                        ok = False
                        break
            if ok:
                gen = (a, b)
                break
        if gen:
            break
    Tn = norm((gen[0], eps * gen[1], gen[1], gen[0]))
    Tn_grp = closure([Tn])
    assert len(Tn_grp) == l + 1, len(Tn_grp)
    # Frobenius conjugation z -> z^l on basis (1,s): diag(1,-1) normalises T_n
    NTn = closure([Tn, (1, 0, 0, l - 1)])
    assert len(NTn) == 2 * (l + 1), len(NTn)
    for H in all_subgroups(NTn):
        rows.append((f"<N(Tn)|{len(H)}", H))
    # S4 and A5 by search
    elist = els
    ordd = {}
    import random
    random.seed(1)
    def find(o1, o2, o3, size, tries=200000):
        c1 = [x for x in elist if order(x) == o1]
        c2 = [x for x in elist if order(x) == o2]
        for _ in range(tries):
            a, b = random.choice(c1), random.choice(c2)
            if order(mul(a, b)) == o3:
                H = closure([a, b])
                if len(H) == size:
                    return H
        return None
    S4 = find(4, 3, 2, 24)
    assert S4 is not None
    for H in all_subgroups(S4):
        rows.append((f"<S4|{len(H)}", H))
    if l % 5 in (1, 4):
        A5 = find(2, 3, 5, 60)
        assert A5 is not None
        for H in all_subgroups(A5):
            rows.append((f"<A5|{len(H)}", H))
    seen = {}
    for name, H in rows:
        key = H
        if key in seen:
            continue
        v = nu(H)
        F = len(H) * lp / v ** 2
        seen[key] = (name, len(H), v, F)
    vals = sorted(seen.values(), key=lambda r: r[3])
    Fn = l ** 3 / ((l + 1) * (l * l - 1))
    below = sorted({(r[0], r[1], r[2]) for r in vals if r[3] < 1 - 1e-12})
    # nu claims
    B = closure([Ts, U])
    nuB, nuNs, nuNn = nu(B), nu(NTs), nu(NTn)
    print(f"l={l}: {len(seen)} distinct subgroups examined; min F = {vals[0][3]:.5f} at {vals[0][:3]}; F(T_n) pred = {Fn:.5f};"
          f" F<1: {below}; nu(B)={nuB} nu(N(Ts))={nuNs} nu(N(Tn))={nuNn} (claims l, l, l+2);"
          f" next-lowest F: {[(r[0], r[1], r[2], round(r[3], 4)) for r in vals[1:4]]}")
    sys.stdout.flush()


if __name__ == "__main__":
    for a in sys.argv[1:]:
        run(int(a))
