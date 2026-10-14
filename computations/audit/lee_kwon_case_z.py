# Independent audit of Proposition 5.3(a) (case Z, Cureton-Thorner only), following Lee-Kwon, Math. Comp. 75 (2006).
# CT-only branch for Lee-Kwon Prop 8(2): a real zero beta in I has 1-beta >= 1/6000, so by LK Prop 6(2) (2nd branch)
# kappa_K >= (1-beta)/(2 e^{1/(2c)}); with LK (1.4), Prop 5(2), Lemma 7(1) and P(m,i,b,t) >= 1:
#    h^- >= C7(m)^n / (6000 e^{1/(2c)}).   C7 from LK Table 7 (m = n for 108..134; m = 134 for n >= 134).
import math
c=(2+math.sqrt(3))/4; K=6000*math.exp(1/(2*c))
T7={134:1.0813,133:1.0806,132:1.0799,131:1.0792,130:1.0785,129:1.0777,128:1.0770,127:1.0763,126:1.0755,125:1.0748,
    124:1.0740,123:1.0732,122:1.0725,121:1.0717,120:1.0709,119:1.0700,118:1.0692,117:1.0684,116:1.0675,115:1.0667,
    114:1.0658,113:1.0649,112:1.0641,111:1.0632,110:1.0622,109:1.0613}
print("threshold 6000 e^{1/2c} =",round(K,1))
for n in range(109,141):
    C=T7.get(n,T7[134]) if n<=134 else T7[134]
    hb=C**n/K
    lo=(C-0.00005)**n/K
    print(n, 2*n, f"{hb:.3f}", "OK" if lo>1 else "--")
