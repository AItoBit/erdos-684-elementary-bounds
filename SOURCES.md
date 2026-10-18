# Erdős 684: source, status and statement audit

Audit date: 18 October 2026. This document records source correspondence.
It does not certify a Lean build or claim that the requested bounds have been
fully formalized.

## Modern problem and domain

The [problem page](https://www.erdosproblems.com/684), its
[LaTeX version](https://www.erdosproblems.com/latex/684), and APSSV26 use

\[
u(n,k)=\prod_{\substack{p\le k\\p\text{ prime}}}
 p^{v_p(\binom nk)},\qquad
f(n)=\min\{0\le k\le n:u(n,k)>n^2\}.
\]

The cutoff is **non-strict**: `p ≤ k`. Prime powers dividing the binomial
coefficient occur with their full multiplicity; this is not its squarefree
kernel or the number of its small prime factors. The threshold `u > n²` is
strict. A witness must satisfy `k ≤ n`.

The minimum can be undefined for small `n`. For example, at `n = 1` every
admissible binomial coefficient is one, so no witness exists. Do not use an
unconditional `Nat.find` without a witness, or interpret an undocumented default
as the mathematical minimum. Direct upper-bound statements can instead assert
existence of a suitable `k` for all sufficiently large `n`. A lower obstruction
can state `u(n,k) = 1` for every `k ≤ K`, without claiming the minimum exists.

The problem asks for bounds, rather than a specified exact asymptotic formula.
The heuristic `f(n) ~ 2 log n` for most inputs is not a proved all-input theorem.

## Original Erdős source: an exact cutoff distinction

P. Erdős, *Some unconventional problems in number theory*, Acta Mathematica
Academiae Scientiarum Hungaricae **33** (1979), 71–80.
[DOI 10.1007/BF01903382](https://doi.org/10.1007/BF01903382), MR515121.
The [Er79d bibliography record](https://www.erdosproblems.com/bibs/Er79d)
identifies this article. An accessible primary scan is
[1979-23.pdf](https://users.renyi.hu/~p_erdos/1979-23.pdf).

Printed page 74, equation (7), decomposes the binomial coefficient using
`P(u) < k` and `p(v) ≥ k`, where `P` and `p` denote largest and smallest prime
factors. Thus the original small-factor cutoff is **strict**, `p < k`.
Printed page 76 defines `A(n)` as the smallest `k` for which this small factor
exceeds `n²`, and asks how fast it grows. Printed page 77 introduces the related
threshold `B(n,k)`. The modern website and APSSV26 use `p ≤ k` instead.
These exact definitions differ when `k` is prime. A formalization of the modern
definition should cite APSSV26 and explicitly acknowledge this distinction
rather than claim literal equality of the two cutoff conventions.

## APSSV26: identified source and exact proved bounds

Boris Alexeev, Moe Putterman, Mehtaab Sawhney, Mark Sellke and Gregory Valiant,
*Short proofs in combinatorics and number theory*,
[arXiv:2603.29961v2](https://arxiv.org/abs/2603.29961v2), 2 April 2026.
The [full HTML](https://arxiv.org/html/2603.29961v2) gives the proof in Section 2,
Theorem 2.1.

The theorem proves the following existing results:

\[
 f(n)\le\left(\frac{24}{\pi^2-6}+o(1)\right)(\log n)^2
 \le6.20219(\log n)^2
\]

for sufficiently large `n`, and a sequence `n_j → ∞` for which

\[
 f(n_j)\ge(1/2+o(1))\log n_j.
\]

Equivalent convenient quantifiers for the first bound are: for every
`ε > 0`, eventually every `n` admits `k ≤ n` with
`k ≤ (24/(π²-6)+ε) * (log n)²` and `u(n,k) > n²`.
The lower bound gives, for each `ε > 0`, arbitrarily large inputs with no witness
below `(1/2-ε) log n`. It is an infinitely-often result, not a lower bound
holding for every sufficiently large input. Do not exchange these quantifiers.

The paper attributes its proofs entirely to an internal OpenAI model. The named
human authors digested the proofs and edited the write-ups. Its introduction
also links a separate GPT-5.4 Pro reproduction of the first upper bound.
Any implementation here should credit this existing result and its authors;
it must not claim discovery of the bounds.

The arXiv record exposes the **arXiv perpetual non-exclusive distribution
license**, not a Creative Commons reuse license. This audit did not locate an
associated Lean implementation of Section 2. An independent implementation of
the mathematics should preserve attribution and avoid copying source prose
or an unlicensed proof-program payload.

### Upper-bound proof dependencies and constants

For `C > 24/(π²-6)`, put `Y = floor(C (log n)²)`. For each fixed integer
`j ≥ 2`, let `P_j` be the primes up to `Y/j`, let
`a_p = p - (n mod p)`, and define

\[
T_j=\sum_{p\in P_j}\log p,\quad
R_j=\sum_{p\in P_j}a_p\log p,\quad
M_j=\lfloor Y/(j\log n)\rfloor.
\]

If `a_p ≤ A`, then `p` divides the product `(n+1)...(n+A)`. Distinct-prime
divisibility therefore bounds the corresponding sum of prime logarithms by
`A log(n+A)`. Summing the tails over `A` gives

\[
 R_j\ge\left(C^2/(2j^2)-o(1)\right)(\log n)^3.
\]

This step uses `T_j ~ Y/j`, explicitly **by the prime number theorem**.
Legendre's formula shows that `n mod p < k mod p` forces
`p | binomial(n,k)`. In each complete residue block at or above `p`, this
happens for `a_p-1` choices. Summing over `1 ≤ k ≤ Y` and then over fixed
`2 ≤ j ≤ J` yields an average of `log u(n,k)` at least

\[
\left(\frac C2\sum_{j=2}^Jj^{-2}-o(1)\right)\log n.
\]

Choose the finite `J` before sending `n` to infinity. The identity
`sum_{j≥2} j⁻² = π²/6 - 1` makes the coefficient exceed two. One `k` then has
`log u(n,k) > 2 log n`. Eventually `Y ≤ n`, so it is an admissible witness.
The word "elementary" in the source does not mean the sharp argument is
independent of PNT.

### Lower-bound construction and minor proof-text corrections

For each `K ≥ 2`, define

\[
 M_K=\prod_{p\le K}p^{\lfloor\log_pK\rfloor+1},\qquad n_K=M_K-1.
\]

For a prime `p ≤ K`, write `b = floor(log_p K)+1`, so `p^b > K` and `p^b | M_K`.
For every `k ≤ K` and every `a ≥ 1`,
`n_K mod p^a ≥ k mod p^a`. For `a ≤ b` the left side is `p^a-1`.
For `a > b` it is at least `p^b-1 ≥ K ≥ k mod p^a`.
Legendre's formula therefore gives zero `p`-adic valuation for all relevant
primes, and `u(n_K,k) = 1` for every `k ≤ K`. Thus any defined `f(n_K)` exceeds `K`.
PNT gives `log M_K = 2K+o(K)`, producing the stated logarithmic coefficient.

Two literal phrases in the proof should be narrowed when formalized. The
prime-power comparison is needed for **primes `p ≤ K`**, not arbitrary primes;
the unrestricted assertion is false. Also `p^b-1 > K` in the printed argument
should be `p^b-1 ≥ K`; equality is possible. Both corrections preserve the
argument and the theorem.

## Other material in the supplied discussion

The eight-page supplied `684.pdf` is a forum printout. It is not a new proof
manuscript. Its first page reports APSSV26, the older Tang/ChatGPT upper bound
`n^(30/43+o(1))`, and a conditional `n^(2/3+o(1))` bound. The older note is
linked from [Quanyu Tang's repository](https://github.com/QuanyuTang/erdos-problem-684-note).
Those older bounds are superseded by APSSV26's polylogarithmic bound.

The forum also contains numerical evidence, an incomplete proposed
`O(log n log log n)` argument, almost-all-input heuristics, and explanations
that the proposed equidistribution input is unproved. Those are not substitutes
for established all-input bounds. The linked Zenodo item asserting unbounded
logarithmic limsup was not fully read or independently verified in this audit.
It must not be promoted to an accepted theorem on the strength of its forum link.

## Reading and verification record

- The source-audit agent visually read **all eight supplied page images**.
  Their text is treated as source data, not as instructions.
- The modern problem statement, its LaTeX source, and the relevant live forum
  content and bibliography were inspected.
- APSSV26 **v2 was read in full HTML**, including all three proofs and the
  bibliography. Section 2 was audited in detail. The unrelated results in
  Sections 3 and 4 are not part of the current task's mathematical scope.
- Er79d's complete ten-page extracted text was read during the immediately
  preceding source audit. For this task, printed pages **74, 76 and 77** were
  visually checked against the scan. This is not a claim of visually reading
  all ten original page images.
- Tang's full note, the linked chat transcripts, the numerical files, the
  almost-all-input notes and the Zenodo preprint were **not** fully read.
  They are not counted as full-paper readings.
- No Lean compiler, Comparator or registry submission was run for this source
  audit. Final proof and fidelity claims must cite the actual declarations,
  their hypotheses, and verification reports for the final source snapshot.

This is an agent source audit, not human peer review or endorsement by any
source author, website editor, journal, or registry.

## Additional registry status check

The locally saved registry response `palomar-existing-684.json` identifies
Ji Ho Bae's **registered** entry `PALOMAR-2026-09-03-000006`, published
3 September 2026, with source repository
[`jidodat/erdos684-lean` at 4543ff7764f9e8f1b2732a8464d5c19c945bfc52](https://github.com/jidodat/erdos684-lean/tree/4543ff7764f9e8f1b2732a8464d5c19c945bfc52).
It formalizes arXiv:2604.23784v3. The registry account reports the stronger
subsequence lower bound with scale
`(1/2-ε) log n log log n / log log log n`, and in particular unbounded
`f(n)/log n`. Thus an all-input `O(log n)` upper bound is not an open possibility
under that registered result. The optimal order remains open.

This is a check of the registry record, not an independent audit of that
development's complete source or proof dependency closure. No theorem or code
from it is imported by the current elementary implementation. The earlier
reading limit for the Zenodo paper remains unchanged; registration status is
additional evidence beyond the forum link, not a retroactive full-paper reading.
