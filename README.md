# Formal Verification of the Belnap–Stiefel Residual Bound

## Scope

This repository contains a machine-checked formalization, in Lean 4 over
Mathlib, of a subset of the geometric and algebraic claims underlying the
Belnap–Stiefel framework: the invariance of a Belnap-weighted Choi map under
global phase, the block decomposition identity induced by the Stinespring
dilation, and a lower bound on the residual distance of that map to the
identity channel on the complex Stiefel manifold St(d, rd).

No claim is made here regarding the Pullback Theorem connecting the
parameter-shift rule to Riemannian gradient descent on St(d, rd). That
result requires a differential-geometric infrastructure (tangent space,
retraction, Riemannian metric) not presently available in Mathlib, and is
explicitly out of scope for this formalization.

## Reproducibility and Falsifiability

Formal proofs are only as trustworthy as the means by which a third party
can check them. To minimize the distance between claim and verification,
every source file in this repository is written to compile, without
modification, in the browser-based Lean playground at
[live.lean-lang.org](https://live.lean-lang.org/), which runs the current
stable release of Mathlib server-side.

This choice is deliberate and methodologically motivated, not one of mere
convenience. It removes every dependency ordinarily required to check a
formal proof — local installation of Lean and Mathlib, package management,
compilation toolchains — reducing the verification procedure to a single
step: copy the source, paste it into the playground, and observe the
absence of errors and of the `sorry` placeholder. A proof that requires no
more than this to be checked leaves correspondingly less room for
undisclosed assumptions, silent axioms, or claims that do not, in fact,
typecheck. The playground's own documentation notes that it is not intended
for large, multi-file developments; the present repository observes this
constraint by keeping each result self-contained within a single file, so
that the reproducibility guarantee is not weakened by that limitation.

Each theorem below can therefore be verified independently, by any reader,
in under a minute, without trust in the author's toolchain or environment.

## Main Results

Let `V : Matrix (Fin (r*d)) (Fin d) ℂ` satisfy `Vᴴ * V = 1` (i.e. `V ∈
St(d, rd)`), partitioned into row blocks `V_T`, `V_F` of dimensions `rT*d`
and `rF*d` respectively, with `rT*d + rF*d = r*d`. Define the Belnap-weighted
Choi map
```
π(V) := μT • (V_Tᴴ * V_T) + μF • (V_Fᴴ * V_F).
```

The following are established without `sorry`:

| Theorem | Statement |
|---|---|
| `phase_invariant_scalar` | `conj(exp(iδ)) * exp(iδ) = 1` |
| `phase_invariant_matrix` | `(exp(iδ) • V)ᴴ * (exp(iδ) • V) = Vᴴ * V` |
| `choiMap_phase_invariant` | `π(exp(iδ) • V) = π(V)` |
| `muT_add_muF_eq_one` | `cos²(θ/2) + sin²(θ/2) = 1` |
| `muT_gt_muF` | `sin²(θ/2) < cos²(θ/2)` for `θ ∈ (0, π/2)` |
| `VT_dagger_VT_add_VF_dagger_VF` | `V_Tᴴ * V_T + V_Fᴴ * V_F = 1` |
| `trace_conjTranspose_mul_self_nonneg` | `0 ≤ Re(tr(Xᴴ * X))` |
| `R_min_bound` | `μF² * d ≤ Re(tr((μF • 1 + κ • B)ᴴ * (μF • 1 + κ • B)))` for `B` Hermitian, PSD-traced |
| `R_min_final` | `μF² * d ≤ Re(tr((π(V) - 1)ᴴ * (π(V) - 1)))` |

The last of these establishes the residual lower bound
`‖π(V) − I_d‖²_F ≥ μF² d` directly on the block-partitioned Choi map, without
recourse to spectral decomposition.

## Explicit Non-Claims

- `R_min_final` establishes a lower bound; it does not establish that the
  bound is attained. A separate constructive result would be required to
  demonstrate tightness.
- No result in this repository concerns the Pullback Theorem, the
  parameter-shift rule, or any physical gate realization (RBS, FBS, or
  Clements-type decompositions). These remain stated, but unformalized,
  elsewhere.
- No claim of novelty is made regarding the classical algebraic facts used
  as lemmas (e.g. non-negativity of `tr(Xᴴ X)`); the contribution lies in
  their composition toward the stated results on St(d, rd).

## File Structure

A single self-contained `.lean` file, intended to be pasted in full into
live.lean-lang.org. Partial pastes will fail to parse, as later
definitions depend on earlier ones via a shared `variable` context.
