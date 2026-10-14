# Computations

The finite computations cited in `paper/note.pdf` (mainly §6, "Computations"), with the commands that run them and
their output logs. Except where noted, each check exists twice: our script (top level) and the independent
auditor's re-implementation (`audit/`), which was written separately and does not import ours.

None of these scripts is part of the Lean formalisation; they support the parts of the paper that are not formalised
(Lemma 3.4 is also proved in Lean, see `TauVanishing/GroupLemma.lean`).

Statement numbers refer to versions 1.1.0 to 1.1.2 of the paper (the numbering did not change). (In version 1.0.0: Lemma 3.3, Lemma 4.4, Lemma 4.6,
Proposition 4.7, Remark 4.8, Conjecture 4.9 and Corollary E; the scripts' comments and printed labels were renumbered,
and `logs/audit/sieve_perprime.log`, the only log that prints a label, was regenerated.)

## Setup

Python 3 with the packages in `requirements.txt` (the logs were produced with Python 3.14.7, NumPy 2.5.3,
SciPy 1.18.1, SymPy 1.14.0, cypari2 2.2.4 / PARI 2.17.2). All linear programs are solved in floating point with HiGHS through
`scipy.optimize.linprog(method="highs")`. Only `group_lemma.py density` needs `cypari2`.

```sh
python3 -m venv .venv && .venv/bin/pip install -r computations/requirements.txt
PYTHON=.venv/bin/python computations/run_all.sh          # or: ... run_all.sh ours | audit
git diff --stat computations/logs                        # compare with the committed (expected) logs
```

`run_all.sh` runs every command below from the right directory and rewrites `logs/`. On one machine (24 cores) the
whole run takes about 7 minutes; the slowest steps are `audit/subgroups.py` (about 3 min), `littlewood.py prod 5 7 11`
(about 2 min) and `audit/sieve/sieveqp.py` (under 1 min with 18 worker processes; set `OMP_NUM_THREADS=1`, as
`run_all.sh` does, or the workers oversubscribe the BLAS threads and the run takes hours). Outputs are
deterministic, except that the floating-point LP values may differ in the last printed digit across SciPy/HiGHS
versions and `sieveqp.py` is a randomised multistart (seeded; `run_all.sh` sets `PYTHONHASHSEED=0`).

## What each script checks

### Theorem A (paper §3)

| paper | command (in `computations/`) | log | expected result |
|---|---|---|---|
| Lemma 3.4(b),(c), and `#Inv / #PGL₂ = ℓ/(ℓ²−1)` | `python group_lemma.py groups` | `logs/group_lemma_groups.log` | brute force over `PGL₂(𝔽_ℓ)`, `5 ≤ ℓ ≤ 23`: every summary line reports `True`; the number of cosets `gN` with `g⁻¹ιg ∈ N∖T` is `(ℓ−1)/2` (split involution) and `(ℓ+1)/2` (nonsplit) |
| Lemma 3.4(c), explicit coset enumeration | `python group_lemma.py cosets` | `logs/group_lemma_cosets.log` | `ℓ ∈ {5, 7, 11, 13, 29}`: `[G':N] = ℓ(ℓ+1)/2`, inert counts as expected (`True`) |
| same (auditor) | `cd audit && python cosets.py 5 7 11 13 29` | `logs/audit/cosets.log` | same counts, by conjugation orbits |
| empirical density of `τ(p) ≡ 0 mod ℓ`; no `τ(p) = 0` | `python group_lemma.py density 100000` | `logs/tau_density.log` | `π(10⁵) = 9592`, `#{p : τ(p) = 0} = 0`; ratios to `ℓ/(ℓ²−1)·π(x)` between 0.95 and 1.06 |

### Theorem B (paper §4)

| paper | command | log | expected result |
|---|---|---|---|
| character table of `PGL₂(𝔽_ℓ)` | `python littlewood.py table 5 7 … 97` (all primes `5 ≤ ℓ ≤ 97`) | `logs/littlewood_table.log` | orthogonality error `< 1e-14`, `Σ dim² = #G`; for `ℓ ≤ 13` brute-force class sizes, permutation character and induced characters agree |
| Theorem B1 (LPs, floating point, `κ_ℓ`), `φ_A` of §4.3 | `python littlewood.py lp 5 7 … 97` | `logs/littlewood_lp.log` | LPs with the mean `μ` fixed, on a grid covering the **full range** `μ₀ ≤ μ ≤ 3`: column `kappa(Inv)` equals column `kappa_B1 = ℓ(ℓ²+1)/((ℓ+1)(ℓ²−1))` for every prime `ℓ ≤ 97` (e.g. 0.9028 at 5, 0.9900 at 97); column `mu>=1/2` (min of `μλ_A` over grid points with `μ ≥ 1/2`) is `1.0000`; column `viol` (grid points where the LP value is below the three-term bound of Theorem B1) is `0`, and `max\|LP-B1\|` is `< 1e-9` (the bound is attained at every grid point, as Remark 4.3 proves); `φ_A` has `μλ_A = 1 + 1/(ℓ−1)` |
| Theorem B1 (auditor: characters from the `GL₂` table, evaluated via eigenvalues in `𝔽_{ℓ²}`; Fourier coefficients of `1_Inv`; values of `Ψ`; LPs) | `cd audit && python characters_lp.py 5 7 11 13 17 31 61 97` | `logs/audit/characters_lp.log` | `λ(1_Inv) = (ℓ²+1)/(ℓ+1)`, `Ψ` values as in the proof, LP minimum of `λ + 2(ℓ−1)μ` is `ℓ+1`, `inf μλ = κ_ℓ`; line `[full mu range, … pts in [mu0, 3]]` (mean fixed, about 500 points): min `μλ = κ_ℓ`, min over `μ ≥ 1/2` is `1`, no point below the B1 bound, max deviation from the B1 bound `< 1e-9` |
| **Remark 4.3: sharpness of the three-term bound** (the majorant `φ₁ = 1_Inv + 2(ℓ−1)⁻²·1_N` has mean `1/(ℓ−1)` and `λ_A(φ₁) = ℓ−1`) | `python sharpness.py` | `logs/sharpness.log` | `symbolic` (SymPy, general `ℓ`, both classes mod 4): coefficients of `φ₁`, St-coefficient `0`, all others with the sign of `1_Inv`'s, `λ_A(φ₁) = ℓ−1`, `Ψ = −2(ℓ−1)` on `N`, all `True`; `table` (explicit character table, every prime `5 ≤ ℓ ≤ 199`): `OK` on every line, `λ_A` on the segments `1_Inv–φ₁–1` within `2e-11` of the bound; `brute` (no character table: trace norm of the convolution matrix on `PGL₂(𝔽_ℓ)`, `ℓ = 5, 7, 11, 13, 17`): `λ_A(φ₁) = ℓ−1`, `λ_A(1_Inv) = (ℓ²+1)/(ℓ+1)`; last line `ALL CHECKS PASSED` |
| Lemma 4.6 (per-factor bound), all subgroups, `ℓ ≤ 13` | `python littlewood.py subgroups 5 7 11 13` | `logs/littlewood_subgroups.log` | `min F = F(T_n) = ℓ³/((ℓ+1)(ℓ²−1))`, and `F < 1` only for `#M = ℓ+1` (`T_n`) |
| **Lemma 4.6 for every prime `5 ≤ ℓ ≤ 61` (auditor), on which Theorem B3 depends for `ℓ < 61`** | `cd audit && python subgroups.py 5 7 11 … 61` | `logs/audit/subgroups.log` | for each of the 16 primes: `min F = F(T_n)` (predicted value printed alongside), `F<1` only for the subgroup of order `ℓ+1` of `N(T_n)`; `ν(B) = ν(N(T_s)) = ℓ`, `ν(N(T_n)) = ℓ+2` |
| Conjecture 4.12, LPs on products | `python littlewood.py prod 5 7` (also `5 11`, `7 11`, `11 13`, `5 7 11`) | `logs/littlewood_prod.log` | `ratio = 1.0000` (the minimum of `μλ_A` over majorants, with the mean fixed on a grid covering the full range `μ₀ ≤ μ ≤ 3`, equals `∏ κ_ℓ`); minimum over grid points with `μ ≥ 1/2` is `1.0000` |
| same (auditor) | `cd audit && python products_lp.py 5 7` (also `7 13`) | `logs/audit/products_lp.log` | full `μ` range: `ratio 1.0`; min over `μ ≥ 1/2` is `1.0` |
| Lemma 4.9 (sharpness LPs, `5 ≤ ℓ ≤ 97`, `r ∈ [1, ℓ − 1/ℓ]`) and the per-prime constants of Proposition 4.10 (auditor) | `cd audit/sieve && python perprime.py` | `logs/audit/sieve_perprime.log` | `L(r) = 1 + ℓ(r−1)` for all `r` tested and all primes: last summary line `True`; `σ_LP = ℓ`; `Ψ` bounds as claimed |
| dual certificate `Ψ′` of Lemma 4.9 (auditor) | `cd audit/sieve && python dual.py` | `logs/audit/sieve_dual.log` | dual values `1 − ℓ` off `Inv`, `ℓ² − ℓ` on `Inv` |
| Bellaïche's two-point functions: `σ − r̃`, `ι − r̃` (auditor, SymPy) | `cd audit/sieve && python twopoint.py` | `logs/audit/sieve_twopoint.log` | the closed forms quoted in Remark 4.11(i), positive for `ℓ ≥ 5` |
| Remark 4.11(i): tensor weights reproduce `∏ κ_ℓ` (auditor) | `cd audit/sieve && python tensor.py` | `logs/audit/sieve_tensor.log` | model II per-prime minima equal `κ_ℓ` at `ℓ = 5, 7, 11, 13, 97` |
| Remark 4.11(i): free weights on divisors of `m` (auditor) | `cd audit/sieve && python tensor_check.py` | `logs/audit/sieve_tensor_check.log` | `ratio/sqrt(t)` stays above `2√∏(1−1/ℓ)` (a single modulus gives 2.0) |
| Proposition 4.10, numerical sieve optimisation; Remark 4.11(iii) (weak primes do not help) (auditor) | `cd audit/sieve && PYTHONHASHSEED=0 python sieveqp.py` | `logs/audit/sieve_qp.log` | `min/sqrt(t)` stays bounded below: about 1.5–2.0 in models I, II and III with `r̃ = ℓ − 1/ℓ`, about 2.5–2.8 with `r̃ = ℓ/2`, and increasing with `t` (weak primes do not help) for `r̃ = 2` and `r̃ = 1.2` |
| character table used by the sieve scripts (auditor) | `cd audit/sieve && python pgl2.py` | `logs/audit/sieve_pgl2.log` | orthogonality error `< 1e-14`; brute-force classes agree at `ℓ = 5, 7` |

### Proposition 5.3 (paper §5.3; Corollary E in version 1.0.0)

| paper | command | log | expected result |
|---|---|---|---|
| recomputation of Lee–Kwon's `C_7` from their Table 1, consistency of the `h(n)` column of Table 7, case Z / case N bounds for `108 ≤ n ≤ 140` | `python lee_kwon.py` | `logs/lee_kwon.log` | `C_7` agrees with Table 7 for `m = 108, 109, 110, 120, 130, 134`; `h(n)` column within 1.1%; final lines: degree `≤ 252` from Cureton–Thorner alone, `≤ 258` using only the recomputed rows |
| case Z values for `109 ≤ n ≤ 140` (auditor) | `cd audit && python lee_kwon_case_z.py` | `logs/audit/lee_kwon_case_z.log` | `C_7^n/(6000 e^{1/(2c)})` is `0.938` at `n = 126` and `1.108 > 1` (`OK`) from `n = 127` on |

The only inputs to the Proposition 5.3 scripts are the constants transcribed from Lee–Kwon, *CM-fields with relative class
number one*, Math. Comp. 75 (2006), Tables 1 and 7.

## Provenance

The scripts were written by AI agents (Claude, Anthropic), see paper §7 and [`AUDITS.md`](../AUDITS.md). They were copied here from the working
directory in which the paper was developed; the only changes are comments and printed labels (now using the paper's
numbering), import paths, the full prime ranges stated in the paper for `perprime.py` (all primes `5 ≤ ℓ ≤ 97`, with
`r = ℓ − 1/ℓ` added and an explicit pass/fail line) and `tensor.py` (`ℓ = 13` added to the printout), and the
removal of a JSON side-output from `sieveqp.py`. In version 1.1.1 the linear-programming scans of `littlewood.py`
(`lp`, `prod`), `audit/characters_lp.py` and `audit/products_lp.py`, which had covered only `μ ≤ 1/2`, were extended
to the full range `μ₀ ≤ μ ≤ 3` with the mean fixed exactly, and a comparison with the three-term bound of Theorem B1
was added. The logs in `logs/` were regenerated with these versions.
In version 1.1.2, `sharpness.py` (and its log `logs/sharpness.log`) was added. It checks the sharpness proof of
Remark 4.3 and is not part of the auditor's re-implementations. A separate statement audit, whose code is not in this
repository, independently checked the same majorant `φ₁` symbolically and numerically for `ℓ ≤ 199`.
