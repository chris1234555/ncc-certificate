# A Lean certificate that the Li–Li network coding conjecture is false

This Lean 4 / Mathlib project proves

```lean
theorem NccCert.not_NCC_rate_one : ¬ NccCert.NCC_rate_one
```

`NCC_rate_one` is a consequence of the undirected *k*-pairs (multiple-unicast) network coding
conjecture of Li and Li (2004), also posed by Harvey, Kleinberg and Lehman (2006). Its negation
says that some finite undirected unit-capacity graph with *k* source–sink pairs has a scalar
linear network code delivering every message at rate one, while no concurrent multicommodity flow
reaches rate one. So network coding can beat routing in undirected networks, and the conjecture is
false.

The same argument shows that the advantage is unbounded:

```lean
theorem NccCert.not_NCC_rate {r : ℝ} (hr : 0 < r) : ¬ NccCert.NCC_rate r
```

For every ε > 0 there is such a network on which a scalar linear code delivers every message at
rate one while no concurrent multicommodity flow reaches rate ε (`NccCert/UnboundedGap.lean`). In
particular, no constant-factor weakening of the conjecture holds either.

Every `LinearCode` sends each edge in one fixed direction along an acyclic orientation. So the
counterexample is a rate-one code on a directed acyclic network whose undirected version has no
rate-one (indeed no rate-ε) flow. This also refutes the weaker directed-acyclic form of the
conjecture used by Afshani–Freksen–Kamma–Larsen, Farhadi–Hajiaghayi–Larsen–Shi and
Dvořák–Koucký–Král–Slívová.

**Credit.** The essential ingredient is OpenAI's theorem that the exact *n*-point discrete Fourier
transform has linear circuits with fewer than *c*·*n*·log₂ *n* gates, for every *c* > 0 and
arbitrarily large *n*. It is family 130, "Exact Fourier transforms below *n* log *n*", in
[openai/math](https://github.com/openai/math), released on 6 October 2026, with the preprint
*Finite tensor savings and exact Fourier circuits*. OpenAI's Lean proof of it is included here
unmodified. This repository contributes the reduction from that theorem to a network coding
counterexample, formalized end to end.

**Status.** This has not been peer reviewed. Scrutiny of the definitions in
[What you have to trust](#what-you-have-to-trust) is especially welcome.

## Structure of the proof

```lean
-- this project (NccCert/Main.lean)
theorem NccCert.not_NCC_rate_one_of_exactFourier :
    OAI.ExactFourier.MainStatement → ¬ NccCert.NCC_rate_one
-- OpenAI (OAI/Computability/FourierCircuit/Main.lean, vendored unmodified)
theorem OAI.ExactFourier.main_theorem : OAI.ExactFourier.MainStatement
-- this project (NccCert/Unconditional.lean)
theorem NccCert.not_NCC_rate_one : ¬ NccCert.NCC_rate_one :=
  not_NCC_rate_one_of_exactFourier OAI.ExactFourier.main_theorem
-- this project (NccCert/UnboundedGap.lean)
theorem NccCert.not_NCC_rate_of_exactFourier (hF : OAI.ExactFourier.MainStatement)
    {r : ℝ} (hr : 0 < r) : ¬ NccCert.NCC_rate r
theorem NccCert.not_NCC_rate {r : ℝ} (hr : 0 < r) : ¬ NccCert.NCC_rate r
```

`NCC_rate r` is `NCC_rate_one` with the flow rate `1` replaced by `r`; `NCC_rate 1` is literally
`NCC_rate_one` (checked by `Iff.rfl` in the file). The unbounded version uses the same network with
c = r/64 and n ≥ 2^m, m = max(18, ⌈16/r⌉ + 2). The best flow rate on the network is at most about
32c, where c measures how far the Fourier circuit beats n log₂ n.

* `NccCert.NCC_rate_one` (`NccCert/Statement.lean`) is the rate-one, unit-capacity form of the
  conjecture. It says that on any finite undirected unit-capacity multigraph with no loops, *k*
  distinct sources and *k* distinct sinks (no vertex is both), if a linear network code over a
  finite field delivers the *k* messages at rate one, then a concurrent multicommodity flow of rate
  one exists.
* `OAI.ExactFourier.MainStatement` is the statement of OpenAI's Comparator challenge
  `lean/ComparatorChallenges/ExactFourier.lean`. For every *c* > 0 there are arbitrarily large *n*
  with an exact linear circuit for the *n*-point DFT over ℂ with fewer than *c*·*n*·log₂ *n* gates.
  A gate is an addition, a subtraction, or a multiplication by an arbitrary complex constant.
* `OAI.ExactFourier.main_theorem` is OpenAI's proof: 51 files and about 19k lines in
  `lean/OAI/Computability/FourierCircuit/` at openai/math commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## What you have to trust

The final statement `¬ NCC_rate_one` does not mention OpenAI's circuit model. To believe it, you
need to read only these definitions, about 60 lines in total:

* `NccCert/Code.lean`: `tailOf`, `headOf`, `LinearCode`;
* `NccCert/Flow.lean`: `netOut`, `ConcurrentFlow`;
* `NccCert/Statement.lean`: `NCC_rate_one`.

Beyond those, you trust the Lean kernel, the three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) and Mathlib's basic definitions. You do not need to trust OpenAI's informal paper,
their circuit model, or any proof in this repository. A loophole in the circuit model could not
help, because the kernel-checked argument turns any circuit satisfying `MainStatement` into an
actual graph, code and flow obstruction stated in the terms above.

Points to check when auditing the definitions:

* **Undirected capacity.** `ConcurrentFlow.capacity` is `∑ i, |f i e| ≤ 1`. Each edge's unit
  capacity is shared by all commodities and both directions.
* **Fractional routing.** Flows are real-valued; nothing forces integral or single-path routing.
* **Independent messages.** `LinearCode.solves` quantifies over every message vector
  `msg : Fin k → F`.
* **A genuine code.** Every edge is used in one direction and carries one field symbol (the value at
  its tail). Each vertex holds a fixed linear combination of its incoming symbols plus its own
  messages. The orientation is acyclic (`rank`), so vertex values are determined by the messages
  (`LinearCode.val_unique`). Each sink's value equals its message.
* **Non-degeneracy.** No self-loops, distinct sources, distinct sinks, and no vertex that is both.
  These hypotheses only weaken `NCC_rate_one`, so they strengthen its negation.

### Why the conjecture implies `NCC_rate_one`

The conjecture says that in an undirected network the network coding rate equals the maximum
concurrent multicommodity flow rate. A `LinearCode` is a network code of rate one, so the
conjecture would give a maximum flow rate of at least one. The feasible flows of rate *r* form a
closed polytope, so the maximum is attained. Scaling a flow of rate *r* ≥ 1 down to rate 1 keeps it
feasible, which gives a `ConcurrentFlow` of rate 1. This step is the only one not checked by Lean.

## The proof

Write Ω for the DFT matrix, ω = ζₙ, ν = 1/n and τ(t) = −t mod n. Then
Ω · diag(ν ω^{ls}) · Ω sends e_j to e_{τ(j+s)}. So two copies of a DFT circuit, joined by a diagonal
layer, route message *j* from input *j* to output τ(j+s), for each of the *n* cyclic shifts *s*.
Turning this into a counterexample takes five steps.

1. **Specialize to a finite field** (`Specialize.lean`). The circuit's constants, ζₙ and 1/n satisfy
   finitely many integer polynomial identities over ℂ. Because ℤ is a Jacobson ring (arithmetic
   Nullstellensatz), the same identities hold in some finite field *K*.
2. **Circuit to linear DAG** (`Fourier.lean`, `LDag.lean`). OpenAI's `Circuit` becomes a linear
   straight-line DAG over *K* computing the specialized DFT matrix *M*, with
   Σₗ M(τ(j+s), l) · d_s(l) · M(l, m) = [m = j] for every shift *s*.
3. **The network** (`ShiftCode.lean`). Take two copies of the DAG and give every use of a value its
   own relay vertex. The result is a graph of maximum degree 3 with at most 8|C| + 2n edges. The
   graph does not depend on *s*. For every shift *s* it carries a rate-one `LinearCode` with sources
   at input *j* and sinks at output τ(j+s).
4. **Routing lower bound** (`Graph.lean`, `Flow.lean`). In a graph of maximum degree 3, a ball of
   radius *T* has at most 4^T vertices. Averaging over shifts, some *s* has at least n − 4^T pairs
   at distance greater than *T*. Each such pair uses at least *T* + 1 units of edge capacity per
   unit of flow, so a rate-one flow needs at least (T+1) · n/2 edges.
5. **Contradiction** (`Main.lean`). Take c = 1/64, n ≥ 2^18 and T = ⌊log₄(n/2)⌋. The edge count
   8|C| + 2n < n log₂ n / 8 + 2n is smaller than (T+1) · n/2 > (log₂ n − 1) · n/4.

The result is an existence statement, not an explicit graph. The counterexample networks come from
OpenAI's asymptotic construction and are presumably astronomically large.

## Reproducing the check

You need Lean `v4.34.1` (pinned in `lean-toolchain`) and Mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612`, the same pins as OpenAI's `lean/` project.
OpenAI's `Core.lean` does `import Mathlib`, so the full library is needed.

```sh
lake exe cache get              # or build Mathlib from source (several hours on 2 cores)
lake build NccCert OAIFourier   # this project's 13 modules and OpenAI's 51 files
./scripts/check_axioms.sh       # fails unless the main theorems use only the 3 standard axioms
./check_all.sh                  # optional: leanchecker kernel replay of every project module
./scripts/verify_vendored.sh    # vendored OpenAI files are byte-identical to upstream
```

`.github/workflows/build.yml` runs all of these on every push; results are in the repository's
Actions tab. `logs/` holds the output of the same commands from the author's machine.

What the checks establish:

* The build completes with no errors and no `sorry`. The only warnings are linter and deprecation
  warnings.
* `scripts/check_axioms.sh` confirms that `not_NCC_rate_one`, `not_NCC_rate_one_of_exactFourier`,
  `not_NCC_rate`, `not_NCC_rate_of_exactFourier` and `OAI.ExactFourier.main_theorem` depend only on
  `propext`, `Classical.choice` and `Quot.sound`. These are also the axioms OpenAI's Comparator
  challenge permits.
* `leanchecker` (the kernel replay checker shipped with Lean) re-checks every declaration of every
  `NccCert.*` and `OAI.Computability.FourierCircuit.*` module.
* Neither development contains `axiom`, `sorry`, `native_decide`, `implemented_by`, `extern`,
  `unsafe`, `run_cmd`, `elab`, `addDecl` or `debug.skipKernelTC`. The only macro is a local tactic
  abbreviation, `nomega`, in `NccCert/Fourier.lean`. It expands to `simp only [...] at *` followed
  by `omega`.
* `OAI/Computability/FourierCircuit/` is byte-identical to upstream. The SHA-256 of
  `sha256sum *.lean` run in that folder is
  `e4d18fa70215e36dd89000e3f7962bf81ef7d8f0ae9aca3838119c599ad75778`. Apart from a `section`
  wrapper and doc comments, its `Core.lean` matches the definitions of the Comparator challenge
  `lean/ComparatorChallenges/ExactFourier.lean`.

## Scope and consequences

* Lean proves the negation of the rate-one, unit-capacity, scalar-linear form of the conjecture,
  and of every rate-r weakening of it. The conjecture itself then fails by the short argument in
  [Why the conjecture implies `NCC_rate_one`](#why-the-conjecture-implies-ncc_rate_one).
* The coding advantage is unbounded. Braverman, Garg and Schvartzman (ITCS 2017) showed that any
  gap can be amplified to a polylogarithmic one; `not_NCC_rate` gives unboundedness directly. The
  cut bound caps the advantage at O(log |V|).
* Conditional results of the form "the network coding conjecture implies a lower bound" lose their
  hypothesis. Examples include Afshani–Freksen–Kamma–Larsen (ICALP 2019) on Ω(n log n) Boolean
  circuits for multiplication, Farhadi–Hajiaghayi–Larsen–Shi (STOC 2019) on external-memory integer
  sorting, Asharov–Lin–Shi (SODA 2021) on sorting circuits for short keys, and
  Dvořák–Koucký–Král–Slívová (ESA 2021) on data structure lower bounds. This does not refute those
  lower bounds; it removes that route to them.

## Layout

| File | Contents |
|---|---|
| `NccCert/Statement.lean`, `Code.lean`, `Flow.lean` | the statement (definitions to audit) |
| `NccCert/Graph.lean` | balls in bounded-degree graphs; some shift has many far pairs |
| `NccCert/Flow.lean` | the routing lower bound `flow_rate_mul_le` |
| `NccCert/LDag.lean` | linear straight-line DAGs |
| `NccCert/ShiftCode.lean` | the max-degree-3 network and its rate-one shift codes |
| `NccCert/Specialize.lean` | ℤ is Jacobson, so complex identities specialize to a finite field |
| `NccCert/Fourier.lean` | OpenAI circuits to linear DAGs over a finite field, and the cyclic identity |
| `NccCert/Main.lean` | `not_NCC_rate_one_of_exactFourier` |
| `NccCert/Unconditional.lean` | `not_NCC_rate_one` |
| `NccCert/UnboundedGap.lean` | `NCC_rate r` and `not_NCC_rate`: no flow of any rate r > 0 |
| `NccCert/ExactFourierDefs.lean` | imports OpenAI's `Core.lean` (the statement's definitions) |
| `NccCert/Check.lean` | axiom audit and printed statements |
| `OAI/Computability/FourierCircuit/` | OpenAI's proof, unmodified |
| `extras/ExactFourierDefs_standalone.lean.txt` | verbatim copy of the challenge definitions, for a light conditional-only build |
| `scripts/` | axiom check and vendored-code check |

## License and citation

Apache License 2.0; see `LICENSE` and `NOTICE`. The files under `OAI/` are OpenAI's, also under
Apache 2.0. To cite this work, see `CITATION.cff`, and please also cite OpenAI's result.
