# Elementary bounds for Erdős 684

Candidate Lean formalization of the known quadratic-logarithmic upper bound
and a logarithmic lower obstruction, with nonoptimal constants514 and1/8.
The optimal order remains open. No mathematical novelty is claimed.

See [the mathematical account](README.txt), [source audit](SOURCES.md), and
[verification record](VERIFICATION.txt). The Lean implementation is independent;
it adapts APSSV26, Theorem2.1. Bae's separate stronger registered lower theorem
is credited in the source notes and is not imported here.

The package uses Lean4.35.0-rc2 and pinnedMathlib065356127b1dc0016f66b7283ce0ce2c4055aa55.

```sh
lake exe cache get
lake --wfail build Solution Challenge
```

`Challenge.lean` deliberately has two comparison holes. It defines the compared
small-prime part exactly; Comparator also checks this definition against Solution.
The solution may use only propext, Classical.choice and Quot.sound.

AItoBit directed this task and is responsible for maintenance. Codex agents
wrote the Lean implementation and performed the reported audits. No human
expert review or manual human proof generation is asserted.
