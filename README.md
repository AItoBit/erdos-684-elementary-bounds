# Elementary bounds for Erdős problem 684

This Lean development implements two known bounds with nonoptimal constants
**514** and **1/8**. For

\[
U(n,k)=\prod_{p\le k,\ p\text{ prime}}p^{v_p(\binom nk)},
\]

the result statements are:

- For every sufficiently large natural number `n`, some `k ≤ n` satisfies
  `k ≤ 514 (log n)²` and `U(n,k) > n²`.
- For arbitrarily large natural numbers `n > 1`, every natural number
  `k ≤ (log n)/8` satisfies `U(n,k) = 1`.

The implementation adapts the residue averaging and prime-power obstruction
in [APSSV26, Theorem 2.1](https://arxiv.org/html/2603.29961v2#S2), using
elementary Chebyshev estimates. No prime number theorem hypothesis is assumed.
The source proves sharper coefficients, approximately **6.20219** above and
**1/2** below; those coefficients are outside this formalization's scope.
No mathematical novelty is claimed.

The optimal growth remains open. [Ji Ho Bae's separate registered
development](https://github.com/jidodat/erdos684-lean/tree/4543ff7764f9e8f1b2732a8464d5c19c945bfc52)
proves a stronger subsequential lower bound and unbounded `f(n)/log n`.
No proof from that development is imported here.

See [the mathematical proof and attribution](README.txt),
[source audit](SOURCES.md), [statement audit](FIDELITY.txt), and
[verification status](VERIFICATION.txt). Both final theorems passed the standalone build and axiom audit in
[CI run 39101125950](https://github.com/AItoBit/erdos-684-elementary-bounds/actions/runs/39101125950).
The source audit is a focused review; the 100-paper research campaign remains incomplete.

The package pins Lean **4.35.0-rc2** and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
lake exe cache get
lake --wfail build Solution Challenge
```

`Challenge.lean` contains two deliberate comparison holes and defines the
small-prime part identically. `Solution.lean` does not import Challenge.
Comparator is configured to compare that definition and both theorems,
permitting only `propext`, `Classical.choice`, and `Quot.sound`.
Mechanical verification and registry acceptance are separate checks.

AItoBit directed the task and accepts maintenance responsibility. Codex agents
generated the implementation and performed the documented agent audits.
This is not a claim of manual human proof generation or human expert review.
The independent implementation is licensed under Apache-2.0.
