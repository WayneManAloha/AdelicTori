# AdelicToriLean
[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/WayneManAloha/AdelicTori)

Development milestone v0.1.0-discrete-core: the discrete arithmetic results have been machine-checked in Lean. The full manuscript has not yet been formalized.
- 41 audited declarations (`audits/axioms.txt`) were checked in Lean: 22 for the discrete
  arithmetic core, 15 for phase (b) infrastructure toward Theorem `fdccg-adelic-tori`, and 4
  imported from the vendored Pontryagin duality library.
- The existence of a `DegreeOnePrimes K` sequence for every number field is now checked in Lean
  (`exists_degreeOnePrimes`), so the discrete results hold unconditionally
  (`exists_groupOfIntegers`).
- The manuscript's principal topological theorems are not yet formally checked in Lean here;
  phase (b) infrastructure is listed below.

Lean 4 companion to the paper **"Finite-Dimensional Protori Are Adelic Tori"** by Wayne Lewis,
[arXiv:2411.16000](https://arxiv.org/abs/2411.16000).

This repository contains machine-checked Lean proofs for the discrete algebraic core of the paper's number-field construction: the group of integers `B_K = Σ_k 𝔭_k⁻¹` attached to a number field `K`, its
endomorphism ring, and the structure of `B_K / 𝒪_K` underlying the statement that the
nonarchimedean dimension of every number field is `1`.

The topological parts of the paper (Pontryagin duality, adelic tori, delta-subgroups, the
adelic Lie algebra) are **not** formalized here. The status of each result is listed below.

## What does it mean that a proof has been checked by Lean?

**Lean is a computer program that checks mathematical proofs.**

A mathematician writes a theorem, its assumptions, and a proof in Lean's precise mathematical language. Lean then checks whether every step of the proof is logically justified.

If the proof passes, Lean has verified that **the stated conclusion follows from the stated assumptions**.

It does **not** mean that:
- A journal or mathematical institution has certified the result.
- Lean has checked every theorem in the accompanying paper.
- Lean has proved assumptions that the formal theorem explicitly takes for granted.
- The formal theorem necessarily says exactly what the author intended. That correspondence must also be checked by mathematicians.

### What has Lean checked in this repository?

The current version contains 22 machine-checked declarations concerning the arithmetic structure of \(B_K\), including its endomorphism ring and strong indecomposability, 15 declarations of phase (b) infrastructure (see the theorem map), and 4 imported duality declarations.

These results are stated for a particular infinite sequence of prime ideals, called `DegreeOnePrimes K`. **The existence of such a sequence for every number field has now been proved in Lean** (`exists_degreeOnePrimes`).

The manuscript's topological theorems have also not yet been checked in Lean.

The accompanying axiom audit confirms that the 41 checked declarations use only Lean's standard foundational axioms, with no missing proofs inserted using `sorry`.

### What does a successful build mean?

When `lake build` completes successfully, Lean has accepted the proofs included in that build.

This is a reproducible mathematical check, not a journal review or a guarantee about claims that have not been formalized.

**In short: Lean checks exactly what we tell it to prove, using exactly the assumptions we give it.**

## Verify the proofs in GitHub Codespaces

Click the "Open in GitHub Codespaces" button above.

Once the development environment is ready,
open a terminal and run:

    lake build
    lake env lean scripts/Audit.lean

The repository contains 41 audited Lean declarations.
See audits/axioms.txt for their axiom dependencies.

No local Lean installation is required.

## Status at a glance

| Category | Meaning |
|---|---|
| **Certified** | Checked in Lean, no `sorry`, no new axioms. The discrete theorems are stated for any `D : DegreeOnePrimes K`, and such `D` exists for every number field (`exists_degreeOnePrimes`). |
| **Paper only** | Established in the paper, not formalized in Lean. |

### The data `DegreeOnePrimes K`

```lean
structure DegreeOnePrimes (K) where
  q : ℕ → ℕ
  P : ℕ → Ideal (𝓞 K)
  q_prime : ∀ k, (q k).Prime
  q_inj : Function.Injective q
  norm_eq : ∀ k, Ideal.absNorm (P k) = q k
```

This is an infinite sequence of degree-one prime ideals `P k` of `𝒪_K`, lying over pairwise
distinct rational primes `q k`.
- **Existence is proved in Lean** (`Existence.lean`, `exists_degreeOnePrimes`), without
  Chebotarev: an integral primitive element `θ` (`exists_integral_primitive`), Schur's theorem on
  prime divisors of polynomial values (`schur`), a nonzero integer in the conductor of `ℤ[θ]`
  (`exponent_ne_zero`), and Mathlib's Kummer–Dedekind isomorphism `𝒪_K/p ≅ 𝔽_p[X]/(f̄)` composed
  with evaluation at a root of `f̄`.
- Every discrete theorem below holds for **every** such sequence.
- The data are weaker than the paper's: complete splitting and the paper's rotation of the
  index `i(k)` are not needed.

## Theorem-to-declaration map

Declarations are in namespace `AdelicToriLean`; `D : DegreeOnePrimes K`, `B_K = D.BK`.

### Paper Theorem *Adelic Realisation of a Group of Integers* (`zassenhaus-realisation`): discrete part

| Paper statement | Lean declaration | File | Status |
|---|---|---|---|
| `B_K = Σ_k 𝔭_k⁻¹` | `DegreeOnePrimes.BK` | `Basic.lean` | definition |
| `𝒪_K ⊆ B_K ⊆ K`, `ℚ B_K = K` | `BK_sandwich` | `Paper.lean` | certified |
| `End(B_K) = 𝒪_K` (ring isomorphism) | `endRingEquiv` | `Paper.lean` (`Endomorphisms.lean`) | certified |
| every additive endomorphism is multiplication by a unique `o ∈ 𝒪_K` | `end_eq_mul` | `Paper.lean` | certified |
| `ℚ End(B_K) ≅ K` | `qEnd_eq_mul` | `Paper.lean` (`EndRing.lean`) | certified |
| strongly indecomposable (idempotent quasi-endomorphisms are `0` or `1`) | `stronglyIndecomposable` | `Paper.lean` | certified |
| locally free: `(B_K)_(ℓ) ≅ ℤ_(ℓ)^n` for every prime `ℓ` | `locallyFree` | `Paper.lean` (`LocalFree.lean`) | certified |
| homogeneous of type `t(ℤ)` when `[K:ℚ] ≥ 2` | `homogeneous_tZ` | `Paper.lean` (`LocalFree.lean`) | certified |
| `(B_K/𝒪_K)_{q_k} = 𝔭_k⁻¹/𝒪_K` | `primary_component_q` | `Paper.lean` (`Quotient.lean`) | certified |
| `(B_K/𝒪_K)_ℓ = 0` for `ℓ ∉ {q_k}` | `primary_component_other` | `Paper.lean` (`Quotient.lean`) | certified |
| `𝔭_k⁻¹/𝒪_K` cyclic of prime order `q_k` | `primary_component_cyclic` | `Paper.lean` (`Quotient.lean`) | certified |
| existence of infinitely many suitable primes | `exists_degreeOnePrimes` | `Existence.lean` | certified |
| the discrete realisation for every number field | `exists_groupOfIntegers` | `Unconditional.lean` | certified |
| `T_K^∨` is a delta-subgroup of `B_K^∨`, density of the diagonal `𝒪_K`, the isomorphisms `B_K^∨ ≅ (T_K^∨ × ℝ·K)/𝒪_K ≅ (ℒ_n(B_K^∨) × ℝ·K)/K` | none | none | paper only (Pontryagin duality) |

### Paper Theorem *Nonarchimedean Line through a Number Field* (`nonarchimedean-line-number-field`)

| Paper statement | Lean declaration | Status |
|---|---|---|
| upper bound: `B_K/𝒪_K ≅ ⊕_k ℤ/q_k`, every primary component cyclic of prime order or trivial | `primary_component_q`, `primary_component_other`, `primary_component_cyclic` | certified (discrete side) |
| lower bound: a group of integers with no free summands has `B/𝒪_K` infinite | `free_of_finite_quotient` (if `B/𝒪_K` is finite, then `B` is free of rank `[K:ℚ]`) | certified (discrete side) |
| passage to `dim_n(B_K^∨) = 1` via the standard representation of `(B_K/𝒪_K)^∨` | none | paper only (Pontryagin duality, [Lewis 2019, Prop. 1, Lemma 6, Cor. 4]) |

### Theorem *Finite-Dimensional Compact Connected Groups Are Adelic Tori* (`fdccg-adelic-tori`): in progress

The theorem itself is **not yet** certified. Certified ingredients (AdelicTori's own proofs):

| Ingredient used in the paper's proof | Lean declaration | File |
|---|---|---|
| no small subgroups of the circle | `subgroup_le_centeredArc` | `Protorus.lean` |
| the dual of a compact abelian group is discrete | `discreteTopology_dual` | `Protorus.lean` |
| the dual of a connected abelian group is torsion-free | `dual_torsionFree` | `Protorus.lean` |
| `p`-adic fractional part `{·}_p : ℚ_p → ℝ/ℤ`, with `{r}_p = r` on `ℤ[1/p]` | `fractP`, `fractP_rat` | `PadicFract.lean` |
| kernel of `{·}_p` is `ℤ_p`; continuity | `fractP_eq_zero_iff`, `continuous_fractP` | `PadicFract.lean` |
| `∑_p {r}_p = r (mod 1)` for `r ∈ ℚ` | `sum_fract_rat` | `RatFract.lean` |
| standard character `ψ(u) = ∑_p {u_p}_p` on Mathlib's finite adeles `𝔸ᶠ[ℤ, ℚ]`, continuous | `psi`, `continuous_psi` | `FiniteAdeleChar.lean` |
| `ψ` vanishes on `∏_p ℤ_p` | `psi_eq_zero_of_integral` | `FiniteAdeleChar.lean` |
| diagonal identity `ψ(r) = r (mod 1)` | `psi_algebraMap` | `FiniteAdeleChar.lean` |
| `ℤ̂ = ∏_p ℤ_p` is compact | `isCompact_ZHat` | `StrongApprox.lean` |
| strong approximation `ℚ̂ = ℚ + ℤ̂` | `exists_rat_add_ZHat` | `StrongApprox.lean` |
| pairing `⟪(u, x), b⟫ = ∑_i (ψ(b_i u_i) - b_i x_i)` of `𝔸ⁿ` with `ℚⁿ`, continuous | `pairing`, `continuous_pairing` | `AdelicPairing.lean` |
| the diagonal `ℚⁿ ⊆ 𝔸ⁿ` is isotropic (`Λ̃ ⊆ Λ̃^⊥` on `ℚⁿ`) | `pairing_diag` | `AdelicPairing.lean` |
| annihilator of `ℤⁿ ⊆ S ⊆ ℚⁿ` in `𝔸ⁿ` is `C + Λ̃`, with `C ⊆ ℤ̂ⁿ` | `annihilator_eq`, `annC` | `AdelicKernel.lean` |
| Pontryagin reflexivity `G ≅ G^∨∨` | `PontryaginDual.toDoubleDual` | vendored (third-party) |

### Other results of the paper

These are all **paper only**:
- *Spectrum of Resolutions*;
- *Pontryagin Self-Dual Proper Short Exact Sequence*;
- Lemma `nala-periodic-lca`;
- *Symmetric Adelic Lie Algebra*;
- *Topological Characterisation via Nonarchimedean Exponential*;
- *Adelic Exponential Yields Lie Category*;
- *The Kumu*;
- Remark *Dense Subgroups and Dual Topologies*;
- Corollary *Five Equivalents*;
- the closing Example.

Mathlib defines the Pontryagin dual but does not provide the duality theorem; this project uses
the vendored `pontryagin` library for it (see below).

## Proof of `End(B_K) = 𝒪_K` in Lean

The Lean proof is different from, and shorter than, the paper's. It needs neither a Galois
closure nor the rotating index `i(k)`.

1. Let `φ` be a quasi-endomorphism preserving `B_K`. Scale it to `ψ` so that it also preserves
   `𝒪_K`. For `t ∈ 𝒪_K`, put `D_t = ψ ∘ (t·) − (t·) ∘ ψ`.
2. With `I_k = q_k 𝔭_k⁻¹` (`Cofactor.lean`) and `t ≡ c (mod 𝔭_k)` for some `c ∈ ℤ` (degree one),
   some `m` prime to `q_k` satisfies `m D_t(I_k) ⊆ q_k 𝒪_K` (`Commute.lean`).
3. Transpose `D_t` through the trace form. Mathlib's `FractionalIdeal.dual_eq_mul_inv` gives
   `m W_t(a) ∈ 𝒪_K^∨ · 𝔭_k` for `a ∈ 𝒪_K` (`Trace.lean`). After clearing denominators by a factor
   independent of `k`, a fixed element of `𝒪_K` lies in every `𝔭_k`, so it is `0`. Hence `D_t = 0`
   (`Kill.lean`).
4. So `φ` is multiplication by `α = φ(1)`. A multiplier of `B_K` has bounded denominators on all
   its powers, so it is integral (`EndRing.lean`).

## File layout

| File | Content |
|---|---|
| `AdelicToriLean/Basic.lean` | the data `DegreeOnePrimes`, `𝔭_k⁻¹`, `B_K` |
| `AdelicToriLean/Localization.lean` | elements of `B_K` are in `𝔭_k⁻¹` up to integers prime to `q_k` |
| `AdelicToriLean/Cofactor.lean` | `𝔭_k I_k = (q_k)`; residues of degree-one primes |
| `AdelicToriLean/Commute.lean` | the commutator `D_t` and the defect estimate |
| `AdelicToriLean/Trace.lean` | trace duality |
| `AdelicToriLean/Kill.lean` | `D_t = 0` |
| `AdelicToriLean/EndRing.lean` | `End = 𝒪_K`, `ℚ End = K` for `ℚ`-linear maps; multipliers are integral |
| `AdelicToriLean/Endomorphisms.lean` | additive endomorphisms; ring isomorphism; strong indecomposability |
| `AdelicToriLean/Quotient.lean` | primary components of `B_K / 𝒪_K` |
| `AdelicToriLean/LocalFree.lean` | local freeness; `t(ℤ)`-homogeneity; finite quotient ⇒ free |
| `AdelicToriLean/Paper.lean` | paper-facing statements |
| `AdelicToriLean/Existence.lean` | existence of `DegreeOnePrimes K` (Schur + Kummer–Dedekind) |
| `AdelicToriLean/Unconditional.lean` | unconditional discrete realisation |
| `AdelicToriLean/Protorus.lean` | duals of compact / connected abelian groups |
| `AdelicToriLean/PadicFract.lean` | `p`-adic fractional part |
| `AdelicToriLean/RatFract.lean` | `∑_p {r}_p = r (mod 1)` |
| `AdelicToriLean/FiniteAdeleChar.lean` | the standard character of `𝔸ᶠ[ℤ, ℚ]` |
| `AdelicToriLean/StrongApprox.lean` | `ℤ̂`, compactness, `ℚ̂ = ℚ + ℤ̂` |
| `AdelicToriLean/AdelicPairing.lean` | `𝔸 = ℚ̂ × ℝ`, the pairing with `ℚⁿ` |
| `AdelicToriLean/AdelicKernel.lean` | annihilator of a lattice in `𝔸ⁿ` |
| `scripts/Audit.lean` | `#print axioms` for the paper-facing statements and key lemmas |
| `audits/` | full build log and axiom audit output |
| `vendor/Pontryagin/` | third-party Pontryagin duality library (see below) |

## Build

Requires `elan`. The toolchain and Mathlib version are pinned (`lean-toolchain`, `lake-manifest.json`):

- Lean `leanprover/lean4:v4.34.0-rc2`
- Mathlib `v4.34.0-rc2` (commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`)

```
git clone https://github.com/WayneManAloha/AdelicTori.git
cd AdelicTori
lake exe cache get      # downloads the prebuilt Mathlib cache
lake build
lake env lean scripts/Audit.lean
```

**Continuous integration.** `.github/workflows/build.yml` builds the AdelicTori library and the
vendored Pontryagin library, fails on any warning in AdelicTori's own sources, rejects
`sorry`/`admit`/`native_decide`/`axiom` in all sources (including the vendored ones), and checks
that all 41 audited declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

**Codespaces.** `.devcontainer/devcontainer.json` installs `elan`, fetches the Mathlib cache and
builds on creation.

## Third-party library: Pontryagin duality

`vendor/Pontryagin/` contains the library `pontryagin` by **The pontryagin contributors**
(https://github.com/shosonoda/pontryagin, commit `4f72437124104369dc18ac380061bc2006f8e392`,
Apache License 2.0). It proves Pontryagin duality for locally compact Hausdorff abelian groups:

```lean
PontryaginDual.toDoubleDual : G ≃ₜ* PontryaginDual (PontryaginDual G)   -- toDoubleDual G g χ = χ g
```

These proofs are **not** the work of Wayne Lewis. The library was ported from Lean/Mathlib
`v4.32.0` to `v4.34.0-rc2` by five one-line proof edits and no change to any statement; see
`vendor/Pontryagin/PORTING.md`. Its own copyright headers, `LICENSE` and upstream README are kept.
Its Lean options (including `maxSynthPendingDepth = 3`) apply to that library only. Under
`v4.34.0-rc2` the vendored files emit 51 linter warnings (deprecations and style); they are left
unchanged to keep the diff from upstream minimal.

Audited third-party declarations: `PontryaginDual.toDoubleDual`, `PontryaginDual.toDoubleDual_apply`,
`PontryaginDual.eval_injective`, `PontryaginDual.eval_surjective`.

## License

AdelicTori: Apache License 2.0, copyright 2026 Wayne Lewis. See `LICENSE` and `NOTICE`.
The vendored library in `vendor/Pontryagin/` has its own Apache 2.0 license and authors.

## Verification record

- `lake build` completes with exit code 0 and 0 errors; AdelicTori's own sources produce 0
  warnings (`audits/FullBuild.log`).
- No source, original or vendored, contains `sorry`, `admit`, `native_decide` or `axiom`.
- `audits/axioms.txt` lists the axioms of 41 declarations: 37 from AdelicTori (every paper-facing
  statement and the key lemmas) and 4 from the vendored Pontryagin library. Each depends only on
  `propext`, `Classical.choice`, `Quot.sound`.
