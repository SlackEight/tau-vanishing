"""Group lemma behind Theorem A (paper Lemma 3.4) and an empirical check of the Chebotarev densities it uses.

Lemma 3.4. Let l >= 5 be prime, G' = PGL2(F_l), T the image of the diagonal torus, N = N(T) its normaliser
(dihedral, order 2(l-1)), N_out = N \\ T.  Then
  (i) every element of N_out is an involution;
  (ii) for every involution i of G', #{cosets gN : g^{-1} i g in N_out} = |i^{G'} cap N_out| * |Z(i)| / |N| >= (l-1)/2
      (this is Lemma 3.4(c) of the paper);
  (iii) #Inv(G') / |G'| = l / (l^2 - 1)  (so the main term Li(x)/(l-1) of Theorem A is at most (1 + 1/l) x the truth).
`groups` verifies (i)-(iii) by brute force for 5 <= l <= 23 (for (ii) via the class-size formula).  `cosets` checks (ii)
independently: it enumerates the left cosets gN of N in G' explicitly, checks [G':N] = l(l+1)/2 = n_E, and for each
involution class counts the cosets fixed by i (degree-1 primes of E = L'^N) split into "inert in M = L'^T"
(g^{-1} i g in N_out) and "split in M" (g^{-1} i g in T).  `density X` compares #{p <= X : tau(p) = 0 mod l} with
l/(l^2-1) * pi(X) and with the main term pi(X)/(l-1) of the upper bound, and counts the p <= X with tau(p) = 0
(needs cypari2).

  python group_lemma.py groups
  python group_lemma.py cosets            # l in {5, 7, 11, 13, 29}
  python group_lemma.py density 100000
"""
import itertools
import math
import sys


def pgl2(l):
    """Elements of PGL2(F_l) as normalised 4-tuples (first nonzero entry = 1)."""
    els = []
    for a, b, c, d in itertools.product(range(l), repeat=4):
        if (a * d - b * c) % l == 0:
            continue
        t = (a, b, c, d)
        lead = next(x for x in t if x)
        inv = pow(lead, l - 2, l)
        n = tuple((x * inv) % l for x in t)
        if n == t:
            els.append(t)
    return els


def norm(t, l):
    lead = next(x for x in t if x)
    inv = pow(lead, l - 2, l)
    return tuple((x * inv) % l for x in t)


def mul(x, y, l):
    a, b, c, d = x
    e, f, g, h = y
    return norm(((a * e + b * g) % l, (a * f + b * h) % l, (c * e + d * g) % l, (c * f + d * h) % l), l)


def inv(x, l):
    a, b, c, d = x
    return norm((d % l, (-b) % l, (-c) % l, a % l), l)


def groups(lmax=23):
    for l in (5, 7, 11, 13, 17, 19, 23):
        if l > lmax:
            break
        G = pgl2(l)
        one = (1, 0, 0, 1)
        invs = [g for g in G if g != one and mul(g, g, l) == one]
        T = [g for g in G if g[1] == 0 and g[2] == 0]
        Nout = [g for g in G if g[0] == 0 and g[3] == 0]
        N = T + Nout
        assert len(G) == l * (l * l - 1) and len(N) == 2 * (l - 1)
        a_ok = all(mul(g, g, l) == one for g in Nout)
        Nout_set = set(Nout)
        minc = 10 ** 9
        classes = {}
        for i in invs:
            # class of i: split iff -det is a square (trace 0); use representative-independent invariant
            a, b, c, d = i
            det = (a * d - b * c) % l
            # i normalised; the projective class of -det modulo squares is well defined
            key = pow((-det) % l, (l - 1) // 2, l)
            classes.setdefault(key, []).append(i)
        for key, cl in classes.items():
            i = cl[0]
            Z = sum(1 for g in G if mul(g, i, l) == mul(i, g, l))
            meet = sum(1 for x in cl if x in Nout_set)
            cnt = meet * Z // len(N)
            assert meet * Z % len(N) == 0
            assert len(cl) * Z == len(G)
            minc = min(minc, cnt)
            print(f"l={l:2d} class {'split ' if key == 1 else 'nonsplit'}: |class|={len(cl):5d} |Z|={Z:3d} "
                  f"|class cap N_out|={meet:3d}  #cosets gN with g^-1 i g in N_out = {cnt}", flush=True)
        dens = len(invs) / len(G)
        print(f"l={l:2d}: |G'|={len(G)}, #Inv={len(invs)} (l^2={l*l}), N_out all involutions: {a_ok}, "
              f"min #cosets = {minc} >= (l-1)/2 = {(l-1)//2}: {minc >= (l-1)//2},  #Inv/|G'| = {dens:.5f} "
              f"= l/(l^2-1): {abs(dens - l/(l*l-1)) < 1e-12}", flush=True)


def cosets(ls=(5, 7, 11, 13, 29)):
    """Independent check of Lemma 3.4(c) by explicit coset enumeration (no class-size formula)."""
    one = (1, 0, 0, 1)
    for l in ls:
        G = pgl2(l)
        T = [g for g in G if g[1] == 0 and g[2] == 0]
        Nout = [g for g in G if g[0] == 0 and g[3] == 0]
        Tset, Noutset = set(T), set(Nout)
        N = T + Nout
        # left cosets gN, each represented by its sorted tuple of elements (canonical)
        reps, seen = [], set()
        for g in G:
            if g in seen:
                continue
            c = [mul(g, h, l) for h in N]
            seen.update(c)
            reps.append(g)
        assert len(reps) == l * (l + 1) // 2, (l, len(reps))
        # one representative per involution class (split iff -det is a square)
        reps_inv = {}
        for g in G:
            if g != one and mul(g, g, l) == one:
                a, b, c, d = g
                key = pow((-(a * d - b * c)) % l, (l - 1) // 2, l)
                reps_inv.setdefault(key, g)
        for key, i in sorted(reps_inv.items(), reverse=True):
            inert = split = 0
            for g in reps:   # the condition g^{-1} i g in N (resp. N_out, T) is independent of the coset rep
                c = mul(mul(inv(g, l), i, l), g, l)
                inert += c in Noutset
                split += c in Tset
            want = (l - 1) // 2 if key == 1 else (l + 1) // 2
            print(f"l={l:2d} {'split   ' if key == 1 else 'nonsplit'} involution: [G':N] = {len(reps)} = l(l+1)/2;"
                  f" fixed cosets inert in M = {inert} (expected {want}: {inert == want}),"
                  f" fixed cosets split in M = {split}", flush=True)


def density(X=2_000_000):
    import cypari2
    P = cypari2.Pari()
    P.allocatemem(10 ** 9)
    ls = [11, 13, 17, 19, 29, 31, 37]
    cnt = {l: 0 for l in ls}
    npr = 0
    zero = 0
    p = 2
    # tau(p) via PARI ramanujantau (exact)
    for p in P.primes(P.primepi(X)):
        p = int(p)
        t = int(P.ramanujantau(p))
        npr += 1
        if t == 0:
            zero += 1
        for l in ls:
            if p != l and t % l == 0:
                cnt[l] += 1
    print(f"X = {X}: pi(X) = {npr}; #{{p: tau(p) = 0}} = {zero}")
    for l in ls:
        pred = l / (l * l - 1) * npr
        print(f"  l={l:2d}: #{{p <= X: tau(p) = 0 mod l}} = {cnt[l]:6d};  l/(l^2-1) pi(X) = {pred:9.1f};"
              f"  ratio {cnt[l]/pred:.4f};  bound main term pi(X)/(l-1) = {npr/(l-1):9.1f}", flush=True)


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "groups"
    if cmd == "groups":
        groups()
    elif cmd == "cosets":
        cosets()
    elif cmd == "density":
        density(int(sys.argv[2]) if len(sys.argv) > 2 else 2_000_000)
