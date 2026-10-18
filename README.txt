ELEMENTARY BOUNDS FOR ERDOS PROBLEM 684

Repository: AItoBit/erdos-684-elementary-bounds
Final standalone build and axiom checks are pending; see VERIFICATION.txt.

Result
------
For natural n,k let
  U(n,k) = product over primes p <= k of p ^ v_p(binomial(n,k)).
The full p-adic multiplicity is retained. We prove the following two known
qualitative bounds with explicit, nonoptimal constants:

* For every sufficiently large n, there exists 1 <= k <= n with
  k <= 514(log n)^2 and U(n,k) > n^2.
* For arbitrarily large n > 1, every natural k <= (log n)/8 satisfies
  U(n,k) = 1.

The compared upper theorem states k <= n; its proof constructs k >= 1, which
also follows from the strict threshold for these positive inputs. These
statements avoid assigning a default to a minimum that may not exist for
small n. Whenever f(n) is defined as the least index with U(n,k) > n^2,
they give an eventual quadratic-logarithmic upper bound and an
infinitely-often logarithmic lower bound.

These are an independent implementation of known results, not a claim of a
new solution or optimal order. Alexeev, Putterman, Sawhney, Sellke and Valiant
proved the sharper upper coefficient 24/(pi^2-6) + o(1), hence an eventual
6.20219(log n)^2 bound, and the subsequential lower coefficient 1/2 + o(1).
Our constants 514 and 1/8 do not formalize those sharper coefficients.

The exact order remains open. In particular, one must not describe O(log n)
as a plausible proved all-input bound here: Ji Ho Bae's separately registered
formalization proves that f(n)/log n is unbounded. This project neither
imports that development nor claims its stronger lower result.

Proof of the upper bound
------------------------
Write L = log n, X = ceil(256L^2), and A = ceil(32L). For all sufficiently
large n, elementary Chebyshev estimates and elementary limits give
  theta(X) >= X/2,  2X <= n,  A <= n,
  32L <= A <= 33L,  256L^2 <= X <= 257L^2,
  log(n+A) <= 2L,  L >= 1.
Here theta(X) is the sum of log p over primes p <= X.

Call a prime p <= X bad when p - (n mod p) <= A. Each bad prime divides
one of n+1,...,n+A, so the product of the distinct bad primes divides that
positive product. Taking logarithms shows that bad-prime weight is at most
A log(n+A). The remaining good primes therefore have logarithmic weight
at least theta(X) - A log(n+A).

For a good prime p put r = n mod p. For each i = 1,...,A choose
  k = p + r + i.
Then p <= k < 2p <= 2X <= n, and k mod p = r+i > n mod p. The first-level
carry in the binomial coefficient forces v_p(binomial(n,k)) >= 1. These
A indices are distinct. Adding their log p contributions over all good
primes and exchanging finite sums yields
  sum_{k=1}^{2X} log U(n,k) >= A(theta(X) - A log(n+A)).

The parameter bounds make the right side at least
  (32L)(128L^2 - 66L^2) = 1984L^3.
If every U(n,k) in the window were at most n^2, the left side would be at
most (2X)(2L) <= 1028L^3. This contradicts L >= 1. Some index therefore
satisfies U(n,k) > n^2 and k <= 2X <= 514L^2.

Proof of the lower obstruction
-----------------------------
For a large integer K put
  M_K = lcm(1,...,K) * product_{p <= K} p,  n_K = M_K - 1.
For each prime p <= K the number p^(floor(log_p K)+1) is larger than K
and divides M_K. Thus n_K has maximal residues modulo the smaller powers
of p, and residues at least K modulo the larger powers. For each k <= K
this excludes every p-adic carry, so v_p(binomial(n_K,k)) = 0 and
U(n_K,k) = 1.

The identities log M_K = psi(K) + theta(K), together with elementary
Chebyshev estimates, give log M_K <= 8K. Hence (log n_K)/8 <= K.
Also n_K >= K for K > 2, so these inputs are unbounded. This proves the
second assertion. Neither proof assumes the prime number theorem.

Sources and attribution
-----------------------
* Alexeev, Putterman, Sawhney, Sellke and Valiant, Short proofs in combinatorics
  and number theory, arXiv:2603.29961v2, Theorem 2.1, Section 2:
  https://arxiv.org/html/2603.29961v2#S2
  The paper attributes its proofs entirely to an internal OpenAI model;
  the human authors digested and edited the proofs. The residue-averaging
  method and prime-power obstruction are adapted here.
* P. Erdos, Some unconventional problems in number theory, Acta Math. Acad.
  Sci. Hungar. 33 (1979), 71-80, especially pages 74, 76 and 77:
  https://doi.org/10.1007/BF01903382
  https://users.renyi.hu/~p_erdos/1979-23.pdf
  The original cutoff p < k differs from the modern p <= k used here.
* Modern problem and discussion:
  https://www.erdosproblems.com/684
  https://www.erdosproblems.com/forum/thread/684
* Bae's independent, stronger lower-bound development:
  https://github.com/jidodat/erdos684-lean/tree/4543ff7764f9e8f1b2732a8464d5c19c945bfc52
  Registry entry PALOMAR-2026-09-03-000006, registered 3 September 2026.
  It formalizes arXiv:2604.23784v3. No code or theorems from that repository
  are imported here; no authorship or endorsement of that work is claimed.

The reading ledger in SOURCES.md distinguishes full readings from excerpts.
The eight supplied forum pages were read as images; the APSSV26 v2 HTML was
read in full; relevant original Erdos pages were checked against the scan.
The registry record of Bae's development was inspected. This account does
not claim that its full Lean dependency closure was independently audited.
The focused corpus contains three discovered and screened works, two reviewed
in full text, and one used in the proof. The arXiv subset has two discovered,
two screened, one fully read and one used. The broader 100-paper research
quota has not been met. This is not a claim of campaign completion.

Production and responsibility
-----------------------------
AItoBit directed the task and confirmed responsibility as the human project
maintainer. Codex agents generated the Lean implementation and documentation;
a separate agent audited mathematical fidelity and source correspondence.
Human project attribution records task direction and responsibility, not
manual proof generation or human expert review. Source authors retain credit
for their existing mathematical results. No source-author participation or
endorsement is claimed.

The package uses Lean 4.35.0-rc2 with canonical Mathlib commit
065356127b1dc0016f66b7283ce0ce2c4055aa55 and no substantive external proof
dependency. The independent implementation is licensed under Apache-2.0.
Challenge defines U
identically and Comparator checks that definition and both result statements.
Only actual final build, warning, axiom, Comparator and independent-kernel
reports establish the corresponding verification claims. A local build or
preparation draft is not registry registration or editorial acceptance.
