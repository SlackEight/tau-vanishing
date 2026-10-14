"""Independent PGL_2(F_l) class/character table (formula-based), validated by
orthogonality and (for small l) brute-force class enumeration.
Classes: e, u, split a (a in F_l^x, a != +-1, pair {a,1/a}), iota_s, nonsplit z (z in T_n
cyclic order l+1, z != 1, z^2 != 1, pair {z,1/z}), iota_n."""
import numpy as np
from itertools import product


def prim_root(p):
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in set(factor(p - 1))):
            return g


def factor(n):
    out, d = [], 2
    while d * d <= n:
        while n % d == 0:
            out.append(d); n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def table(l):
    g = prim_root(l)
    eta = 1 if l % 4 == 1 else -1
    # split classes: a = g^k, k=1..(l-3)/2 (a != +-1; a ~ 1/a)
    split_k = list(range(1, (l - 1) // 2))           # g^k, k in 1..(l-3)/2
    # nonsplit: T_n = <t> order l+1, z = t^j, j=1..(l-1)/2 (z != 1, z != t^{(l+1)/2})
    ns_j = list(range(1, (l + 1) // 2))
    classes = [('e', None, 1), ('u', None, l * l - 1)]
    classes += [('s', k, l * (l + 1)) for k in split_k]
    classes += [('is', None, l * (l + 1) // 2)]
    classes += [('n', j, l * (l - 1)) for j in ns_j]
    classes += [('in', None, l * (l - 1) // 2)]
    sizes = np.array([c[2] for c in classes], float)
    G = l ** 3 - l
    assert sizes.sum() == G, (sizes.sum(), G)
    chars, dims, names = [], [], []

    def leg_pow(k):  # Legendre symbol of g^k
        return (-1) ** k

    # trivial
    chars.append([1.0] * len(classes)); names.append('1')
    # sgn
    row = []
    for (t, k, _) in classes:
        row.append({'e': 1, 'u': 1, 'is': eta, 'in': -eta}.get(t, None) if t in ('e', 'u', 'is', 'in')
                   else (leg_pow(k) if t == 's' else (-1) ** k))
    chars.append([float(x) for x in row]); names.append('sgn')
    # St
    st = []
    for (t, k, _) in classes:
        st.append({'e': l, 'u': 0, 's': 1, 'is': 1, 'n': -1, 'in': -1}[t])
    chars.append([float(x) for x in st]); names.append('St')
    chars.append([a * b for a, b in zip(chars[1], st)]); names.append('sgnSt')
    # principal series: mu = character of F_l^x, mu(g) = exp(2 pi i m/(l-1)), mu^2 != 1, pairs
    for m in range(1, (l - 1) // 2):
        if 2 * m == l - 1:
            continue
        row = []
        for (t, k, _) in classes:
            if t == 'e': row.append(l + 1)
            elif t == 'u': row.append(1)
            elif t == 's': row.append(2 * np.cos(2 * np.pi * m * k / (l - 1)))
            elif t == 'is': row.append(2 * np.cos(np.pi * m))  # mu(-1) = mu(g^{(l-1)/2})
            else: row.append(0)
        chars.append(row); names.append(f'PS{m}')
    # discrete series: theta char of T_n cyclic order l+1, theta^2 != 1
    for m in range(1, (l + 1) // 2):
        row = []
        for (t, k, _) in classes:
            if t == 'e': row.append(l - 1)
            elif t == 'u': row.append(-1)
            elif t in ('s', 'is'): row.append(0)
            elif t == 'n': row.append(-2 * np.cos(2 * np.pi * m * k / (l + 1)))
            else: row.append(-2 * np.cos(np.pi * m))   # z = t^{(l+1)/2}
        chars.append(row); names.append(f'DS{m}')
    X = np.array(chars, float)
    dims = X[:, 0].copy()
    # orthogonality
    gram = (X * sizes) @ X.T / G
    err = np.abs(gram - np.eye(len(X))).max()
    assert X.shape[0] == X.shape[1], X.shape
    assert abs((dims ** 2).sum() - G) < 1e-9
    return dict(l=l, classes=classes, sizes=sizes, G=G, X=X, dims=dims, names=names, orth_err=err)


def fourier(T, f):
    """coefficients <f, chi> = E[f chi] (real chars)."""
    return (T['X'] * T['sizes']) @ f / T['G']


def lamA(T, f):
    return float(np.abs(fourier(T, f)) @ T['dims'])


def inv_ind(T):
    return np.array([1.0 if c[0] in ('is', 'in') else 0.0 for c in T['classes']])


def brute_check(l):
    """Enumerate PGL2(F_l), compute conjugacy classes by brute force and compare
    class sizes / types with the formula table."""
    mats = []
    seen = set()
    for a, b, c, d in product(range(l), repeat=4):
        if (a * d - b * c) % l == 0:
            continue
        # normalise: first nonzero entry = 1
        v = (a, b, c, d)
        s = next(x for x in v if x)
        inv = pow(s, l - 2, l)
        key = tuple((x * inv) % l for x in v)
        if key not in seen:
            seen.add(key); mats.append(key)
    assert len(mats) == l ** 3 - l
    idx = {m: i for i, m in enumerate(mats)}

    def mul(x, y):
        a, b, c, d = x; e, f, g, h = y
        v = ((a * e + b * g) % l, (a * f + b * h) % l, (c * e + d * g) % l, (c * f + d * h) % l)
        s = next(t for t in v if t); inv = pow(s, l - 2, l)
        return tuple((t * inv) % l for t in v)

    def inverse(x):
        a, b, c, d = x
        v = (d, (-b) % l, (-c) % l, a)
        s = next(t for t in v if t); inv = pow(s, l - 2, l)
        return tuple((t * inv) % l for t in v)
    cls = [-1] * len(mats); sizes = []
    for i, m in enumerate(mats):
        if cls[i] >= 0:
            continue
        orb = {mul(mul(g, m), inverse(g)) for g in mats}
        for o in orb:
            cls[idx[o]] = len(sizes)
        sizes.append(len(orb))
    # involutions: trace 0 (projectively)
    ninv = sum(1 for m in mats if (m[0] + m[3]) % l == 0)
    return sorted(sizes), ninv


if __name__ == '__main__':
    import sys
    for l in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 97]:
        T = table(l)
        print(l, 'nclasses', len(T['classes']), 'orth_err %.2e' % T['orth_err'])
    for l in [5, 7]:
        T = table(l)
        bs, ninv = brute_check(l)
        print('brute', l, 'class sizes match:', bs == sorted(int(s) for s in T['sizes']),
              '|Inv| =', ninv, '= l^2:', ninv == l * l)
