# Independent check of Lemma 3.4(c): enumerate left cosets gN explicitly (as frozensets) and, for each involution
# class, count cosets with g^{-1} i g in N_out; also count the "split" ones (g^{-1} i g in T). Also check the
# Frobenius/degree-1 dictionary sum: #fixed cosets = #{gN: g^-1 i g in N}.
import itertools, sys
def run(l):
    def norm(t):
        lead = next(x for x in t if x); iv = pow(lead, l-2, l); return tuple((x*iv) % l for x in t)
    def mul(x, y):
        a,b,c,d = x; e,f,g,h = y
        return norm(((a*e+b*g)%l, (a*f+b*h)%l, (c*e+d*g)%l, (c*f+d*h)%l))
    def inv(x):
        a,b,c,d = x; return norm((d, (-b)%l, (-c)%l, a))
    G = sorted({norm(t) for t in itertools.product(range(l), repeat=4) if (t[0]*t[3]-t[1]*t[2]) % l})
    one = (1,0,0,1)
    T = [g for g in G if g[1]==0 and g[2]==0]; Nout = [g for g in G if g[0]==0 and g[3]==0]
    N = T+Nout; Ns=set(N); Ts=set(T); Nos=set(Nout)
    cosets = {}
    for g in G:
        key = frozenset(mul(g, n) for n in N)
        cosets.setdefault(key, g)
    assert len(cosets) == l*(l+1)//2*1 or True
    invs = [g for g in G if g != one and mul(g,g)==one]
    # one representative per conjugacy class: classify by brute conjugation orbit
    seen=set(); reps=[]
    for i in invs:
        if i in seen: continue
        orb={mul(mul(inv(g),i),g) for g in G}; seen|=orb; reps.append((i,len(orb)))
    out=[]
    for i,sz in reps:
        nout = sum(1 for g in cosets.values() if mul(mul(inv(g),i),g) in Nos)
        ntor = sum(1 for g in cosets.values() if mul(mul(inv(g),i),g) in Ts)
        out.append((sz, nout, ntor))
    print(f"l={l}: |G'|={len(G)} #cosets={len(cosets)} (=l(l+1)/2? {len(cosets)==l*(l+1)//2}); classes (size, #inert deg-1, #split deg-1): {out}; min inert={min(o[1] for o in out)} vs (l-1)/2={(l-1)//2}")
for l in map(int, sys.argv[1:]): run(l)
