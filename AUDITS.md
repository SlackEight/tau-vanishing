# Review passes ("audits")

This file summarises the review passes that the mathematics, the literature comparisons and the Lean formalisation
went through before and after version 1.0.0 of the paper. It replaces the audit narrative that was §10 of version 1.0.0.

**What these are, and what they are not.** Each pass was carried out by an AI agent (Claude, Anthropic) that had not
written the material it reviewed, with independently written code wherever computations were involved. They are
internal checks, not peer review, and their verdicts are not a statement of correctness: AI reviewers can make errors,
including errors they share with the material they review. The author takes responsibility for the content of the
paper and is verifying the proofs; see paper §7. The full reports are kept in the author's research archive and are
available on request.

Statement numbers below refer to versions 1.1.0 and 1.1.1 of the paper (the numbering did not change); version 1.0.0 numbers are given in parentheses where they
differ.

## Passes on the mathematics (before version 1.0.0)

1. **Theorem A** (and Proposition 5.3, then Corollary E, in the same pass). Every step re-derived; Lemma 3.4(c)
   (Lemma 3.3(c)) checked by independent coset enumeration; the uniformity of the Cureton–Thorner inputs checked; a
   same-day literature sweep.
   Changes it led to: an early draft missed Cojocaru–Meyer's Lemma 11, which pre-empts a Lang–Trotter statement
   (`a ≠ 0`) that the draft had listed as new; it was dropped. A claim of a "first unconditional power saving" had
   to be restricted to weight `k ≥ 4`, and was later withdrawn altogether (pass 4).
2. **Theorem B** (B1–B3). Independent code: character tables built from `GL₂` and evaluated via eigenvalues; exact
   linear programs (HiGHS) for `ℓ = 5, …, 97`; Lemma 4.6 (4.4) for all primes `5 ≤ ℓ ≤ 61`; tensorisation linear
   programs. Bellaïche's arXiv v1 was compared with the published text; a follow-up pass read the journal version,
   which acknowledges the sieve error (Rem. 18(i)), and corrected the draft's statement that no erratum had been found.
   Changes: the draft claimed a ceiling at the level of logarithms, which Zywina's smoothed bound refutes; the
   statements were restricted to the exponent, and their scope narrowed to explicitly defined classes.
3. **Proposition 4.10** (4.7). Every step re-derived; character data and linear programs recomputed for `ℓ ≤ 97`.
   Changes: the scope was made explicit (pairwise error accounting, one-signed constraint, tensor test functions,
   `ℓ ≤ x^γ`); a Cauchy–Schwarz exponent was corrected to `(Σc)⁴`; the sharp Lemma 4.9 (4.6) replaced a lossy bound
   that left a gap at `ℓ = 5`; the claim that the optimal sieve "collapses to one modulus" was wrong (spread weights
   gain a factor of order `(log log x)^{1/2}`, which does not change the exponent).
4. **Propositions 5.1 and 5.2** (Theorems C and D). Every step of 5.1 re-derived; the hypotheses of the cited
   `θ`-conditional theorems checked in full text; two literature sweeps (the last on 13 October 2026, 18:52 UTC).
   This pass found Murty–Murty–Pujahari's eq. (7), which led to withdrawing the "first power saving" claim for
   Theorem A.
5. **Proposition 5.3** (Corollary E; part of pass 1). Lee–Kwon read in full text and the sole use of normality
   located. The bound `252` from the preprint alone was found in this pass (the draft had understated the result).

## Passes on the formalisation and the inputs

6. **Lean formalisation of Theorem A.** Checked for gaps, faithfulness of the statement, visibility of inputs and
   honesty of hypothesis H1, including a Lean proof that the trusted notion of "unramified" agrees with
   `p ∤ disc K` (now `TauVanishing/Sanity.lean`). Changes: the claim must carry the `+ε`; H1 assumes existence,
   unramifiedness and trace compatibility of the mod-`ℓ` representations as well as large image; the Cureton–Thorner
   Lean theorem is a proved dependency, not an input. The recommended fresh build and kernel replays were then run
   (README, "Checks performed").
7. **Input (I2).** `AxiomMath/DedekindZetaZeroFree` at `09afbb4c` built in full; axioms, faithfulness of the
   statement (Mathlib's `dedekindZeta`, unshadowed), uniqueness of the continuation, and the derivation of the
   `1 − 1/6000` statement checked. Comparator was not run on that repository's own challenge in this pass; it was run
   for version 1.1.1 (below). (A third-party report that the shipped challenge fails for a syntactic instance-path
   reason while the proof replays is described in the paper, §1.1.)
8. **Context inputs.** `openai/math` at `fd4aeeb2` rebuilt and accepted by Comparator (Lean kernel and `nanoda`).
   Hu's `7/8` preprint reviewed adversarially: no error found, but its analytic core is transferred from OpenAI's
   preprint by locator rather than proved. Neither is used as an established input.

## Reviews of version 1.0.0, and version 1.1.0

Two referee-style reviews of version 1.0.0 (one on the number theory, one on the formalisation, exposition and
release), also carried out by AI agents, led to version 1.1.0. The main changes:

* **Theorem A** is presented as what it is: the transfer of the Serre / Murty–Murty–Saradha / Zywina argument to
  `Z(θ)`, an immediate consequence of the half-plane. The paper quotes Murty–Murty–Pujahari's remark that the
  quasi-GRH bound is "easy to derive" from MMS §4 (and corrects the location to their §7(b)), and credits Zywina 2015
  §4 and Serre 1981 §7.3(iii). The comparison with the exponent `(3+θ)/4` was removed from the abstract.
* **Certificates** (Definition 4.1(b)) are now defined by a group-theoretic validity condition on the full preimage
  of the trace-zero set. The 1.0.0 definition (a condition on the primes with `a(p) = 0`) did not match the proof and
  made Theorem B3 vacuous or false. Theorem B3 is now stated for fields `Ω` for which the kernel of
  `Gal(Ω/ℚ) → ∏ PGL₂(𝔽_ℓ)` is central (e.g. inside the compositum of the mod-`ℓ` fields); the 1.0.0 claim for
  arbitrary `Ω` was not justified by the argument given (paper, Remark 4.7).
* **Theorem B** is stated as lower bounds for three explicitly defined error functionals (Definition 4.1), not for
  "the method"; the title was changed accordingly, and the claim that it explains why the exponent `3/4` has not been
  improved was removed.
* **Inputs.** All corollaries that use the Cureton–Thorner inputs are stated as conditional on (I1) or (I2); the
  convention "unconditionally = given (I2)" was dropped.
* **Theorem B1** now holds for all majorants (the hypothesis `μ(φ) ≤ 1/2` was removed, by a second dual function).
* **Further consequences** (former Theorems C, D and Corollary E) are compressed into §5 with explicit status;
  Zywina 2008, footnote 1, is credited for Proposition 5.2.
* Smaller corrections: the `|ρ| < 1/2` zeros in Proposition 2.2 are treated explicitly (the bound now has a
  `log d_L · log log x` term); Lemma 4.6's dihedral case and coset bounds are proved; `δ < 1/32` in §5.1; the
  `1/168` reference is made precise; strict inequality in Proposition 5.3(b); Bellaïche's Remark 16 is described
  precisely; numerical observations are labelled as such; build details moved from the paper to the README.

## Second review (of version 1.1.0), and version 1.1.1

A second referee-style review of version 1.1.0 (number theory; also an AI agent, the author of the first number-theory
review) re-derived the new proofs (Proposition 2.2, Theorem B1 for all `μ`, Theorem B3 with central kernel, Lemmas
4.5–4.6), ran its own linear programs over the full range of `μ`, and re-ran `computations/run_all.sh` (all logs
byte-identical). It found no mathematical error and asked for small text fixes. Version 1.1.1 makes them:

* **Abstract.** The Lean development proving `Z(31/32)` is described as Cureton–Thorner's own Lean development,
  whose constant is not in their preprint v1 (which states `1 − 1/6000`), not as "a Lean formalisation of their work";
  the central-kernel hypothesis of Theorem B3 is stated.
* **§5.** Three sentences that framed a conditional result as making something newly unconditional were rephrased
  ("Unconditionally, the best known bound is …; Proposition 5.x gives … under (I1) or (I2)").
* **Definition 4.1** allows error weights `w ≥ x^{−o(1)}` (as the proof of Corollary B2 permits), so that the
  smoothed weight `w ≍ log ℓ / log x` of §4.6 lies inside the definition; Proposition 4.10 keeps `1 ≤ w ≤ x^{(1−θ)/2}`.
* **Notation.** The kernel in the proof of Lemma 4.5(i) is now `K_ϖ` (it is `ker ϖ`, not the central `K₀ = ker π` of
  Theorem B3); the sieve weights `c_m` of Proposition 4.10 are now `z_m` (they clashed with the constant `c`).
* **Computations.** The linear-programming scans for Theorem B1 and Conjecture 4.12 (`littlewood.py lp`/`prod`,
  `audit/characters_lp.py`, `audit/products_lp.py`) covered only `μ ≤ 1/2`; they now fix the mean exactly on grids
  covering `μ₀ ≤ μ ≤ 3`, and compare with the three-term bound of Theorem B1. Results: the minimum of `μλ_A` is `κ_ℓ`
  (products: `∏ κ_ℓ`), the minimum over `μ ≥ 1/2` is `1`, and the B1 bound is attained at every grid point to within
  `10⁻⁹` (Remark 4.3 records this as a numerical observation). Logs regenerated with `run_all.sh`.
* **Remark 4.7** now contains a sketch, suggested by the review and re-checked by hand (and, for the two values
  `F(PSL₂) = 2ℓ²/(ℓ+1)²`, `F(PGL₂) = 1`, numerically for `ℓ ≤ 23`), that for arbitrary `Ω` the certificate bound keeps
  the exponent `(1+θ)/2` with a loss `(log(|P|+2))^{−1/2}`. It is labelled a sketch, and Theorem B3 is unchanged.

* **Comparator on (I2).** Run on the challenge shipped with `AxiomMath/DedekindZetaZeroFree` at `09afbb4c`, unmodified:
  accepted by Lean's default kernel ("Your solution is okay!", exit 0). The syntactic instance-path mismatch reported
  by a third party did not reproduce (paper §1.1, README "Checks performed").
* **Frontier sweep before release** (`python -m lab.bench.frontier sweep --days 14 --github-auth`, window
  30 September – 14 October 2026; started 2026-10-14T03:33:39Z, arXiv re-run 2026-10-14T04:14:00Z after HTTP 429
  errors). Keywords: Littlewood norm / Littlewood complexity; Bellaïche; uncertainty principle & PGL; involution &
  PGL₂; τ(p) = 0; Lehmer; Chebotarev & half-plane / zero-free half-plane; Cureton; Thorner. Sources: arXiv (392
  records scanned; one query, "uncertainty principle" & "PGL", still rate-limited), Hexagon (117), Zenodo, GitHub
  repository search (673), GitHub code search (796 files), watched Lean repositories (441 files); no commits to
  `AxiomMath/DedekindZetaZeroFree` after `09afbb4c`. **PRE-EMPTION verdict:** none for Theorem A, Theorem B1,
  Corollary B2, Theorem B3 or Proposition 4.10 (no hit on Littlewood norms, involutions in `PGL₂(𝔽_ℓ)` or `τ(p) = 0`
  bounds other than known sources). **Partial (concurrent):** Frei–Sofos–Widmer, arXiv:2610.18491v1
  (2026-10-13T14:46Z), announce an effective Chebotarev theorem under the quasi-Riemann hypothesis for Dedekind zeta
  functions (overlapping Proposition 2.2) and, drawing on OpenAI and Cureton–Thorner, the Ellenberg–Venkatesh
  `ℓ`-torsion bounds for all number fields (Proposition 5.1, already labelled an immediate consequence). Only the
  abstract was available (the PDF returned 404); the paper now cites it in Remark 2.3, Table 1 and §5.1.
* **Final frontier sweep** (`python -m lab.bench.frontier sweep --days 4 --github-auth`, window 10–14 October 2026,
  generated 2026-10-14T05:57Z; keywords Euclidean, Weinberger, Euclidean ring, real quadratic, Harper, units,
  primitive root, τ(p), Lehmer, Ramanujan tau, Littlewood norm, PGL₂, involutions, Chebotarev; all 7 sources ok:
  arXiv 284, Hexagon 42, Zenodo 117, GitHub repositories 1986, code 2092 files, Lean repositories 301 files), plus
  the arXiv math.NT `/new` page (still the 12 October listing) and hand `gh search repos`/`gh search code` queries.
  **PRE-EMPTION verdict:** none for Theorem A or Theorem B (B1, B2, B3, Proposition 4.10).
  - Frei–Sofos–Widmer, arXiv:2610.18491v1, full text now read. Thm 1.1: under QRH(δ) for `ζ_L` alone,
    `|π_C − (#C/#G)Li(x)| ≤ c₁(#C/#G)x^{1−δ}log(Δ_L^{1/δ}x^{n_L})`, `c₁` absolute: the same kind of statement as
    Proposition 2.2 (whose `(1−θ)^{-1}` term carries an extra `1/log x`). Cor 1.4: the EV bound for `L/K` under
    QRH(δ) for the normal closure (contains Proposition 5.1 for `K = ℚ`). The body is conditional on QRH(δ) (the
    authors have not verified OpenAI or Cureton–Thorner); the abstract claims unconditionality via them. No τ(p),
    Serre-type counting, PGL₂ or Littlewood-norm content. Remark 2.3 and §5.1 now give these pointers.
  - Bhargava, hexagon:2610.00228v1 (14 October): positive lower density of primes with a nonsquare `a ≠ −1` as a
    primitive root, from Cureton–Thorner and OpenAI's marked Type II estimates. Its Lemma 7 (complete-splitting upper
    bound under a zero-free strip, uniform in the field and the width) is now cited in Remark 2.3. No τ(p), PGL₂,
    involutions or Chebotarev-certificate limits.

## Statement audit (of version 1.1.1), and version 1.1.2

A targeted audit of the exact statements (written from scratch, without reading the repository's scripts) checked
four things. **Theorem B1** holds for its full stated class (nonnegative real class functions that are `≥ 1` on
`Inv`): its dual-certificate proof was re-derived symbolically for general `ℓ`, the character table was validated
against a brute-force enumeration of `PGL₂(𝔽_ℓ)` for `ℓ ≤ 13`, and floating-point LPs with random and adversarial
searches for `ℓ ≤ 43` found nothing below the bound. The hypothesis `φ ≥ 0` is necessary: signed `φ` violate the
bound. **Sharp exponent versus Lean `+ε`:** every outward-facing statement distinguishes the paper's sharp
`x^{(1+θ)/2}` from the Lean form `x^{(1+θ)/2+ε}`. **Bellaïche and Zywina:** every claim checked against the primary
texts is accurate. **Dependencies:** a proof-dependency table was drafted, and it showed two missing citations.
Changes in version 1.1.2:

* **Remark 4.3** now proves that the three-term bound of Theorem B1 is sharp for every mean `μ ≥ μ₀`, following the
  auditor's argument. Before, this was a numerical observation. The explicit majorant is
  `φ₁ = 1_Inv + 2(ℓ−1)⁻²·1_N` (`N` = nonsplit regular non-involutions), with `μ(φ₁) = 1/(ℓ−1)` and
  `λ_A(φ₁) = ℓ − 1`; convexity of `λ_A` covers the segments between breakpoints. It also states that equality in
  `μλ_A ≥ κ_ℓ` holds only for `1_Inv`, and in the proof of B1 the values of `Ψ` on regular elements are now exact
  (`0` split, `−2(ℓ−1)` nonsplit). We re-verified all of this independently in `computations/sharpness.py`, in three
  ways: symbolically for general `ℓ` in both classes mod 4; from an explicit character table for every prime
  `ℓ ≤ 199`; and, without any character table, as the trace norm of the convolution operator for
  `ℓ ∈ {5, 7, 11, 13, 17}`.
* **Appendix B** (new) and README "What is formally checked": the proof-dependency table.
* **Citations added:** Fulton–Harris §5.2 and Piatetski-Shapiro (1983) for the character table; Dickson (1901),
  Part II, Ch. XII, §260, and Huppert, *Endliche Gruppen I*, Hauptsatz II.8.27, for the subgroups of `PSL₂(𝔽_q)`,
  applied through `PGL₂(𝔽_ℓ) ⊂ PSL₂(𝔽_{ℓ²})` (Lemmas 4.5 and 4.6).
* **Wording:** Corollary 3.1 now says that `x^{63/64}` is proved on paper and the kernel-checked statement is
  `x^{63/64+ε}`. "Exact linear programs" is now "linear programs solved in floating point with HiGHS". The
  introduction now says that Bellaïche acknowledges two errors (Zywina; Devin and the referee), and that the
  Thorner–Zaman (9.6) substitute costs `(log x)²` but leaves the exponent unchanged. The README's Frei–Sofos–Widmer
  entry now cites the body (Cor. 1.4) instead of "abstract only".
* The Lean statements and proofs are unchanged.
