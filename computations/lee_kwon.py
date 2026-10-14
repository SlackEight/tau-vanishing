"""Proposition 5.3 (paper Section 8): CM fields with relative class number one, following Lee-Kwon,
"CM-fields with relative class number one", Math. Comp. 75 (2006), 997-1013 [LK].

Prints (1) the recomputation of LK's constant C7 from LK Table 1 (rows m = 108, 109, 110, 120, 130, 134) compared with
LK Table 7; (2) the consistency of LK's h(n) column with C7^n/(n C8(n)); (3) for 108 <= n <= 140 the lower bounds for
h^-_K in case Z (a real zero of zeta_K in I; Cureton-Thorner gives 1 - beta >= 1/6000) and in case N (no real zero in
I; LK (5.4)), which give degree <= 252 from Cureton-Thorner alone, and <= 258 if only the Table-1-recomputable rows are
used.  The tables below are transcribed from LK; nothing else is input.

  python lee_kwon.py
"""
import math


# Lee-Kwon, Math. Comp. 75 (2006), Table 7: n -> (rho_K >=, C8(n), b, t, C7(n,b,t), h(n))   (unconditional, normal CM)
LK_T7 = {134: (44.636, 6.0568, 8.866, 47, 1.0813, 43.703), 133: (44.569, 6.0544, 8.866, 47, 1.0806, 37.421),
         132: (44.501, 6.0520, 8.774, 46, 1.0799, 32.044), 131: (44.432, 6.0495, 8.678, 45, 1.0792, 27.442),
         130: (44.362, 6.0470, 8.678, 45, 1.0785, 23.532), 129: (44.292, 6.0445, 8.678, 45, 1.0777, 20.181),
         128: (44.221, 6.0419, 8.678, 45, 1.0770, 17.311), 127: (44.149, 6.0394, 8.678, 45, 1.0763, 14.851),
         126: (44.076, 6.0367, 8.678, 45, 1.0755, 12.758), 125: (44.003, 6.0341, 8.678, 45, 1.0748, 10.950),
         124: (43.928, 6.0314, 8.678, 45, 1.0740, 9.4016), 123: (43.853, 6.0286, 8.480, 43, 1.0732, 8.0832),
         122: (43.777, 6.0259, 8.480, 43, 1.0725, 6.9517), 121: (43.700, 6.0230, 8.480, 43, 1.0717, 5.9807),
         120: (43.622, 6.0202, 8.480, 43, 1.0709, 5.1414), 119: (43.543, 6.0173, 8.480, 43, 1.0700, 4.4266),
         118: (43.463, 6.0144, 8.480, 43, 1.0692, 3.8127), 117: (43.382, 6.0114, 8.378, 42, 1.0684, 3.2819),
         116: (43.301, 6.0084, 8.378, 42, 1.0675, 2.8294), 115: (43.218, 6.0054, 8.378, 42, 1.0667, 2.4380),
         114: (43.134, 6.0023, 8.378, 42, 1.0658, 2.1041), 113: (43.049, 5.9991, 8.272, 41, 1.0649, 1.8150),
         112: (42.963, 5.9960, 8.272, 41, 1.0641, 1.5666), 111: (42.876, 5.9927, 8.272, 41, 1.0632, 1.3530),
         110: (42.788, 5.9894, 8.163, 40, 1.0622, 1.1694), 109: (42.699, 5.9861, 8.163, 40, 1.0613, 1.0103),
         108: (42.609, 5.9827, 8.163, 40, 1.0604, 0.8735)}
# Lee-Kwon Table 1 (unconditional rows m >= 108): m -> (b, t, sigma, sigma~, c4, C5)
LK_T1 = {134: (8.866, 47, 1.0162, 1.2865, 0.08181, 54.799), 130: (8.678, 45, 1.0167, 1.2868, 0.08310, 54.604),
         120: (8.480, 43, 1.0172, 1.2872, 0.08452, 54.361), 110: (8.163, 40, 1.0181, 1.2879, 0.08689, 53.967),
         109: (8.163, 40, 1.0181, 1.2879, 0.08689, 53.961), 108: (8.163, 40, 1.0181, 1.2879, 0.08689, 53.954)}


def lk():
    """Proposition 5.3(a).  Lee-Kwon Prop 8(2), I = [1 - 1/(c log D_K), 1), c = (2+sqrt 3)/4, K CM of degree 2n >= 2m.
    By (1.4), h^- >= 2 D_K^{1/4} kappa_K / ((2 pi)^n kappa_k).  Prop 5(2): kappa_k <= E_sigma (D_k / C5^n)^{c4}
    prod_i exp(2 L_i)^{g_i}, with E_sigma <= 1 always (Lemma 4: E_sigma = 1 or (1-beta)/(sigma-beta)); D_k <= D_K^{1/2}.
    Case Z (zeta_K has a real zero in I; covers LK cases (i) and (ii) without normality): take beta = a real zero in I,
    so zeta_K(beta) = 0 <= 0 and Prop 6(2) (2nd branch; totally imaginary, degree >= 10, rho_K >= 2 pi^2) gives
    kappa_K >= (1-beta)/(2 e^{1/(2c)}) >= 1/(12000 e^{1/(2c)}) by [CT] (beta <= 1 - 1/6000).  Lemma 7(1) with exponent
    1/4 - c4/2 >= 0 and P(m,i,b,t) >= 1 (LK Sec. 6.2; our factor exp((1-2c4) l_i)/exp(2 L_i) >= P since l_i >= 0):
        h^- >= C7(m,b,t)^n / (6000 e^{1/(2c)}),     C7 = (2 pi)^{-1} C5^{c4} exp(B(m)(1/2 - c4)).
    Case N (no real zero in I): zeta_K < 0 on I, first branch of Prop 6(2): LK (5.4) => h^- >= C7^n/(n C8(m)).
    LK's own case (i) bound (sigma - 1) C7^n / e^{1/(2c)} is also printed (it is never the minimum)."""
    c = (2 + math.sqrt(3)) / 4
    e2c = math.exp(1 / (2 * c))
    thr = 6000 * e2c
    print(f"c = {c:.6f}, e^(1/(2c)) = {e2c:.6f}, threshold 6000 e^(1/(2c)) = {thr:.2f}")
    print("Cross-check 1: C7 recomputed from LK Table 1 (C5, c4) and B(m) = C8(m)/(c e^(1/(2c))) (= log rho column)")
    for m, (b, t, sg, sgt, c4, C5) in sorted(LK_T1.items()):
        rho, C8, b7, t7, C7, h = LK_T7[m]
        B = C8 / (c * e2c)
        C7r = C5 ** c4 * math.exp(B * (0.5 - c4)) / (2 * math.pi)
        print(f"  m={m}: (b,t) T1=({b},{t}) T7=({b7},{t7});  B = {B:.4f} (log rho = {math.log(rho):.4f});  "
              f"C7 recomputed = {C7r:.5f}  vs Table 7 {C7}  ({'agree' if abs(C7r - C7) < 6e-4 else 'DIFFER'})")
    print("Cross-check 2: LK's h(n) column = C7^n/(n C8(n))")
    bad = [n for n, r in LK_T7.items() if abs(r[4] ** n / (n * r[1]) / r[5] - 1) > 0.01]
    print(f"  max relative deviation over Table 7: "
          f"{max(abs(r[4] ** n / (n * r[1]) / r[5] - 1) for n, r in LK_T7.items()):.4f}; rows off by > 1%: {bad}")
    print("Bounds for n = 108..140 (m = n for n <= 134, m = 134 beyond; C7 rounded down by 5e-5 for 'robust'):")
    first_all = None
    recomputable = None
    for n in range(108, 141):
        m = n if n <= 134 else 134
        rho, C8, b7, t7, C7, h = LK_T7[m]
        z = C7 ** n / thr
        zlo = (C7 - 5e-5) ** n / thr
        nn = C7 ** n / (n * C8)
        sig1 = 0.0162 if m >= 134 else 0.0167
        ci = sig1 * C7 ** n / e2c
        ok = min(zlo, (C7 - 5e-5) ** n / (n * C8)) > 1
        print(f"  n={n:3d} (deg {2*n}) m={m}: case Z [CT] {z:8.3f} (robust {zlo:7.3f}); case N (5.4) {nn:9.3f}; "
              f"LK case (i) {ci:9.2f}  -> h^- > 1: {ok}")
        if ok and first_all is None:
            first_all = n
        if not ok:
            first_all = None
    print(f"=> [CT] alone: every CM field with h^- = 1 has n <= {first_all - 1}, i.e. degree <= {2*(first_all - 1)}")
    # using only rows whose C7 we recomputed from Table 1
    for n0 in range(108, 200):
        okall = True
        for n in range(n0, 400):
            m = max([mm for mm in LK_T1 if mm <= n], default=None)
            if m is None:
                okall = False; break
            C7 = LK_T7[m][4]
            if min((C7 - 5e-5) ** n / thr, (C7 - 5e-5) ** n / (n * LK_T7[m][1])) <= 1:
                okall = False; break
        if okall:
            print(f"=> using only Table-1-recomputable rows (m in {sorted(LK_T1)}): degree <= {2*(n0 - 1)}")
            break


if __name__ == "__main__":
    lk()
