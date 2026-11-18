# AdelicToriLean
[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/WayneManAloha/AdelicTori)

Development milestone v0.1.0-discrete-core: the discrete arithmetic results have been machine-checked in Lean. The full manuscript has not yet been formalized.
- 188 audited declarations (`audits/axioms.txt`) were checked in Lean: 22 for the discrete
  arithmetic core, 29 for Theorem `fdccg-adelic-tori` and its ingredients, 6 for Theorem
  `spectrum-resolutions`, 27 for Theorem `self-dual-pses` and its ingredients, 12 for Theorem
  `symmetric-adelic-lie-algebra` and the adelic exponential, 23 for Theorem
  `topological-characterisation-nonarchimedean-exponential` and its ingredients (the
  `ℤ̂`-action, delta-subgroups, `K_Δ ≅ Δ`), 4 for the existence of delta-subgroups, 6 for Lemma `nala-periodic-lca`, 10 for Theorem `adelic-exponential-lie-category`, 2 for the density of `exp_a(Hom(ℝ, G))`, 7 for Theorem `kumu`, 5 for Remark `dense-subgroups-dual-topologies`, 4 for the self-duality of `𝔸`, 5 for the closing Example `(𝔸/ℤ)^∨ ≅ ℤ̂ × ℚ`, 6 for `a(G)` (path component, divisible, fully invariant, `exp_a` not open), 8 for the topological half of Theorem `zassenhaus-realisation`, 8 for the nonarchimedean dimension (`dim_n`) and `dim_n(B_K^∨) = 1`, and 4 imported from the vendored Pontryagin duality library.
- The existence of a `DegreeOnePrimes K` sequence for every number field is now checked in Lean
  (`exists_degreeOnePrimes`), so the discrete results hold unconditionally
  (`exists_groupOfIntegers`).
- Most of the manuscript's topological theorems are now checked in Lean, among them
  `fdccg-adelic-tori`, `spectrum-resolutions`, `self-dual-pses`, the topological characterisation,
  `adelic-exponential-lie-category`, `kumu`, and the topological half of `zassenhaus-realisation`.
  The theorem map below lists what is still paper only (chiefly `dim_n` and its consequences) and
  what is cited.

Lean 4 companion to the paper **"Finite-Dimensional Protori Are Adelic Tori"** by Wayne Lewis,
[arXiv:2411.16000](https://arxiv.org/abs/2411.16000).

This repository contains machine-checked Lean proofs for the discrete algebraic core of the paper's number-field construction: the group of integers `B_K = Σ_k 𝔭_k⁻¹` attached to a number field `K`, its
endomorphism ring, and the structure of `B_K / 𝒪_K` underlying the statement that the
nonarchimedean dimension of every number field is `1`.

The topological parts of the paper (adelic tori, delta-subgroups, the adelic Lie algebra) are
formalized here using a vendored Pontryagin duality library. The status of each result is listed
below.

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

The current version contains 22 machine-checked declarations concerning the arithmetic structure of \(B_K\), including its endomorphism ring and strong indecomposability, 29 declarations for Theorem `fdccg-adelic-tori` and its ingredients, 6 for Theorem `spectrum-resolutions`, 27 for Theorem `self-dual-pses` and its ingredients, 12 for Theorem `symmetric-adelic-lie-algebra` and the adelic exponential, 23 for Theorem `topological-characterisation-nonarchimedean-exponential` and its ingredients, 4 for the existence of delta-subgroups, 6 for Lemma `nala-periodic-lca`, 10 for Theorem `adelic-exponential-lie-category`, 2 for the density of `exp_a(Hom(ℝ, G))`, 7 for Theorem `kumu`, 5 for Remark `dense-subgroups-dual-topologies` (see the theorem map), and 4 imported duality declarations.

These results are stated for a particular infinite sequence of prime ideals, called `DegreeOnePrimes K`. **The existence of such a sequence for every number field has now been proved in Lean** (`exists_degreeOnePrimes`).

The theorem map below gives the status of each topological theorem of the manuscript.

The accompanying axiom audit confirms that the 188 checked declarations use only Lean's standard foundational axioms, with no missing proofs inserted using `sorry`.

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

The repository contains 188 audited Lean declarations.
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

### Paper Theorem *Adelic Realisation of a Group of Integers* (`zassenhaus-realisation`)

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
| `B_K^∨` compact, connected, Hausdorff (so in **AT**) | `zassenhaus_topological`, `connectedSpace_of_rank` | `ZassenhausRealisation.lean` | certified |
| `T_K^∨ = 𝒪_K^⊥` (characters of `B_K` trivial on `𝒪_K`) is a delta-subgroup of `B_K^∨`, `B_K^∨/T_K^∨ ≅ (ℝ/ℤ)^[K:ℚ]` | `mem_TK_iff`, `Tperp_isDelta` | `ZassenhausRealisation.lean`, `ZassenhausTopology.lean` | certified |
| the projection of the diagonal `𝒪_K` into `T_K^∨` is dense | `dense_diag` | `ZassenhausTopology.lean` | certified |
| `B_K^∨ ≅ (T_K^∨ × ℝ·K)/𝒪_K`: `(δ, x) ↦ δ · exp_a(x)` is onto with kernel the diagonal `𝒪_K = ℤ^[K:ℚ]` | `resolutionEquiv`, `ker_resolution` | `ZassenhausTopology.lean` | certified |
| `B_K^∨ ≅ (ℒ_n(B_K^∨) × ℝ·K)/K` | none | none | paper only (instance of Theorem `adelic-exponential-lie-category`) |

### Paper Theorem *Nonarchimedean Line through a Number Field* (`nonarchimedean-line-number-field`)

| Paper statement | Lean declaration | Status |
|---|---|---|
| upper bound: `B_K/𝒪_K ≅ ⊕_k ℤ/q_k`, every primary component cyclic of prime order or trivial | `primary_component_q`, `primary_component_other`, `primary_component_cyclic` | certified (discrete side) |
| lower bound: a group of integers with no free summands has `B/𝒪_K` infinite | `free_of_finite_quotient` (if `B/𝒪_K` is finite, then `B` is free of rank `[K:ℚ]`) | certified (discrete side) |
| `dim_n` of `D = T^∨`, `T` discrete torsion: `min_{E ⊆ T finite} max_p rk_p(T/E)` (equal to the number of infinite factors of the standard representation, Lewis 2019 Prop. 1; the equality is a paper argument) | `dimN`, `prank` | certified definition (`NonarchDim.lean`) |
| `|(T/E)[p]| ≤ |T[p]|`; `dim_n` unchanged by finite quotients; independence of the delta-subgroup (Lewis 2019, Lemma 6, Cor. 4) in lattice form | `card_ptors_quot_le`, `dimN_quot`, `dimN_eq_of_finiteIndex` | certified |
| **`dim_n(B_K^∨) = dim_n(T_K^∨) = 1`**: `|T_K[p]| ≤ p` for all `p`, and every finite quotient of `T_K` keeps nonzero `q_k`-torsion | `card_ptors_TK_le`, `exists_prank_quot`, `dimN_TK` | certified (`NumberFieldDim.lean`) |
| lower bound `dim_n(B^∨) ≥ 1` for every group of integers `B`; correspondence of arbitrary delta-subgroups with lattices `F ⊆ B` | none | not yet in Lean |

### Theorem *Finite-Dimensional Compact Connected Groups Are Adelic Tori* (`fdccg-adelic-tori`): certified

**Paper:** if `G` is a protorus with `dim_a G = n`, then `G ≅ (𝔸ⁿ/C)/Λ` for a torsion-free profinite
group `C` and a discrete cocompact `Λ ≅ ℚⁿ`.

**Lean** (`Fdccg.lean`, `fdccg_adelic_tori`). Hypotheses: `[CommGroup G] [TopologicalSpace G]
[IsTopologicalGroup G] [CompactSpace G] [ConnectedSpace G] [T2Space G]` (a protorus) and
`[FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))]` (finite-dimensional), with
`n = dimA G = dim_ℚ (ℚ ⊗ G^∨)`. Conclusion: there is an injective `ι : G^∨ → ℚⁿ` whose image
contains `ℤⁿ` and a topological group isomorphism `G ≃ₜ* Multiplicative ((𝔸ⁿ ⧸ C) ⧸ Λ)`, where
`𝔸 = 𝔸ᶠ[ℤ, ℚ] × ℝ` (Mathlib's finite adeles), `C = Cadd ι` is the annihilator of `ι(G^∨)` in `ℤ̂ⁿ`,
and `Λ = Lam ι` is the image of the diagonal `ℚⁿ`. The properties of `C` and `Λ` are separate
declarations (they hold for every such `ι`):

| Paper claim | Lean declaration | File |
|---|---|---|
| `G ≅ (𝔸ⁿ/C)/Λ` | `fdccg_adelic_tori` | `Fdccg.lean` |
| `C ⊆ ℤ̂ⁿ × {0}` | `Cadd_le` | `AdelicTorusProps.lean` |
| `C` compact | `isCompact_Cadd` | `AdelicTorusProps.lean` |
| `C` totally disconnected (compact + totally disconnected: profinite) | `totallyDisconnected_Cadd` | `AdelicTorusProps.lean` |
| `C` torsion-free (`𝔸ⁿ` is torsion-free) | `An_torsionFree` | `AdelicTorusProps.lean` |
| `Λ̃ ∩ C = 0` | `diag_mem_Cadd_iff` | `AdelicTorusProps.lean` |
| `Λ ≅ ℚⁿ` | `lamEquiv` | `AdelicTorusProps.lean` |
| `Λ` discrete in `𝔸ⁿ/C` | `discreteTopology_Lam` | `AdelicTorusProps.lean` |
| `Λ` cocompact (`(𝔸ⁿ/C)/Λ` compact) | `compactSpace_adelicTorus` | `AdelicTorus.lean` |
| `ℤⁿ ⊆ G^∨ ⊆ ℚⁿ` (choice of `F ≅ ℤⁿ`) | `exists_rank_embedding`, `dual_additive_torsionFree` | `RankEmbedding.lean`, `Fdccg.lean` |

Ingredients of the proof (AdelicTori's own, except the last row):

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
| `Φ : 𝔸ⁿ → D^∨`, `Φ(a)(d) = e(⟪a, ι d⟫)`, continuous homomorphism | `Phi`, `continuous_Phi` | `AdelicModel.lean` |
| `ker Φ = C + Λ̃` | `ker_Phi` | `AdelicModel.lean` |
| `Φ` is surjective (closed image + vendored duality) | `Phi_surjective` | `AdelicModel.lean` |
| `(𝔸ⁿ / C) / Λ` is compact | `compactSpace_adelicTorus` | `AdelicTorus.lean` |
| **`(𝔸ⁿ / C) / Λ ≅ D^∨` as topological groups**, for discrete `ℤⁿ ⊆ D ⊆ ℚⁿ` | `adelicModelEquiv` | `AdelicTorus.lean` |
| Pontryagin reflexivity `G ≅ G^∨∨` | `PontryaginDual.toDoubleDual` | vendored (third-party) |

### Theorem *Spectrum of Resolutions* (`spectrum-resolutions`): certified

**Paper:** let `G` be a finite-dimensional protorus with `G ≅ (C' × ℝⁿ)/ℤⁿ` for a delta-subgroup
`C'`. If `ℤⁿ ⊆ B ⊆ ℚⁿ`, then `G ≅ (L_B × ℝⁿ)/B`, where `L_B = C' ⊕_{ℤⁿ} B` is the (periodic LCA)
pushout of `C'` along `ℤⁿ ↪ B`.

**Lean.** The isomorphism holds for any topological group `C'` and any `α : ℤⁿ → C'`
(`Spectrum.spectrumEquiv`, in the generality in which the paper's proof runs); the paper-facing
form is `spectrum_of_resolutions`: from `G ≃ₜ* (C' × ℝⁿ)/ℤⁿ` it produces `G ≃ₜ* (L_B × ℝⁿ)/B`. The
delta-subgroup hypothesis is used in the paper only to make `C'` profinite; the Lean statements
about `L_B` assume what they use (`C'` Hausdorff, resp. compact). Delta-subgroups are defined in `DeltaSubgroup.lean` (`IsDelta`) and exist by `exists_delta`.

| Paper claim | Lean declaration | File |
|---|---|---|
| `G ≅ (L_B × ℝⁿ)/B` | `spectrum_of_resolutions` (`Spectrum.spectrumEquiv`: `Φ̄_B`, `Ψ_B` inverse) | `SpectrumPaper.lean`, `SpectrumResolution.lean` |
| `{(α z, -z)}` closed, `L_B` Hausdorff | `t2Space_LB` (`Spectrum.isClosed_S`) | `SpectrumPaper.lean` |
| `0 → C' → L_B → B/ℤⁿ → 0` exact | `exact_LB` | `SpectrumPaper.lean` |
| `B/ℤⁿ` torsion | `torsion_B` | `SpectrumPaper.lean` |
| `L_B` periodic: `C'` compact open in `L_B`, every element in a compact open subgroup | `periodic_LB` | `SpectrumPaper.lean` |

### Theorem *Pontryagin Self-Dual Proper Short Exact Sequence* (`self-dual-pses`): certified

`self_dual_pses` (`SelfDualPSES.lean`): for a finite-dimensional protorus `G`, `n = dim_a G`, with
`ι : G^∨ → ℚⁿ` and `L = C^⊥/C`, the sequence `0 → G^∨ → L × ℝⁿ → G → 0` is exact, the first map is
injective with discrete image, the second is continuous, surjective and open, `L` is periodic,
`L × ℝⁿ ≅ (L × ℝⁿ)^∨` and `G ≅ (G^∨)^∨`.

| Ingredient | Lean declaration | File |
|---|---|---|
| `ℤ̂^⊥ = ℤ̂` in `ℚ̂` | `mem_ZHat_of_psi` | `QHatDual.lean` |
| nondegeneracy of `ψ(u v)` | `exists_psi_ne_zero` | `QHatDual.lean` |
| **`ℚ̂ ≅ ℚ̂^∨`**, `u ↦ e(ψ(u ·))` (injective, surjective) | `chi_injective`, `chi_surjective` | `QHatSelfDual.lean` |
| every character of `ℚ̂ⁿ` is `e(ψ(∑ wᵢ xᵢ))` | `charN_surjective` | `QHatnDual.lean` |
| double annihilator `C^⊥⊥ = C` for closed `C ⊆ ℚ̂ⁿ` | `perp_perp_eq` | `QHatnDual.lean` |
| **`C^⊥/C ≅ (C^⊥/C)^∨`** for closed isotropic `C` with `C^⊥` open | `perpQuotEquiv` (`thetaPQ_injective`, `thetaPQ_surjective`) | `PerpQuot.lean` |
| `ker ψ = ℤ̂` | `psi_eq_zero_iff` | `ModelLattice.lean` |
| `C = ι(G^∨)^⊥` and `C^⊥ ∩ ℚⁿ = ι(G^∨)` | `perp_emb_eq`, `rat_mem_perp_iff` | `ModelLattice.lean` |
| **`L ≅ L^∨`**, `L = C^⊥/C` | `modelL_selfDual` | `ModelLattice.lean` |
| exactness of `0 → G^∨ → L × ℝⁿ → (𝔸ⁿ/C)/Λ → 0` | `jMap_injective`, `FMap_comp_jMap`, `ker_FMap`, `FMap_surjective`, `continuous_FMap` | `ModelSequence.lean` |
| `L` periodic | `periodic_modelL` | `ModelProper.lean` |
| image of `G^∨` discrete; `L × ℝⁿ → G` open | `discrete_range_jMap`, `isOpenMap_FMap` | `ModelProper.lean` |
| characters of `ℝ`, `ℝⁿ`; **`ℝⁿ ≅ (ℝⁿ)^∨`** | `chiR_surjective`, `chiRn_surjective`, `realSelfDual` | `RealDual.lean` |
| `(X × Y)^∨ ≅ X^∨ × Y^∨` | `dualProd` | `DualProd.lean` |
| **`L × ℝⁿ ≅ (L × ℝⁿ)^∨`** | `middleSelfDual` | `SelfDualPSES.lean` |
| **Theorem `self-dual-pses`** | `self_dual_pses` | `SelfDualPSES.lean` |

### Lemma `nala-periodic-lca`: certified

`nala_periodic_lca` (`NalaPeriodic.lean`): for a finite-dimensional protorus `G`, `nala(G) = Hom(ℤ̂, G)`
with the compact-open topology is a periodic LCA group (Hausdorff, locally compact, every element in
a compact open subgroup), and evaluation at `1` is an algebraic isomorphism `nala(G) ≅ td(G)`.

| Ingredient | Lean declaration | File |
|---|---|---|
| `K_P ≅ P` compact for closed totally disconnected `P` | `isCompact_Kdelta` (`kdeltaEquiv`) | `NalaPeriodic.lean` |
| `K_Δ` compact open, hence `nala(G)` locally compact | `locallyCompact_nala` | `NalaPeriodic.lean` |
| `P = q⁻¹⟨q x⟩` closed, totally disconnected for torsion `q x` | `torsion_preimage` | `TopCharacterisation.lean` |
| `f ∈ K_P` when `f(1) ∈ P` | `mem_Kdelta_of_genZ` | `NalaPeriodic.lean` |
| every `f` in the compact open subgroup `K_P`, `P = q⁻¹⟨q(f 1)⟩` | `periodic_nala` | `NalaPeriodic.lean` |
| **Lemma `nala-periodic-lca`** | `nala_periodic_lca` | `NalaPeriodic.lean` |

### Theorem *Symmetric Adelic Lie Algebra* (`symmetric-adelic-lie-algebra`): certified except `dim_n`

For a commutative topological group `G`, with all hom-spaces in the compact-open topology,
`nala G = Hom(ℤ̂, G)`, `arla G = Hom(ℝ, G)`, `adla G = Hom(ℤ̂ × ℝ, G)`.

| Paper claim | Lean declaration | File |
|---|---|---|
| `Hom(X × Y, G) ≅ Hom(X, G) × Hom(Y, G)` (topological isomorphism) | `homProd` | `AdelicLieAlgebra.lean` |
| `adla(G) ≅ nala(G) × arla(G)` by restriction | `adlaEquiv`, `symmetric_adelic_lie_algebra` | `AdelicLieAlgebra.lean` |

| compact connected abelian groups are divisible | `pow_surjective` | `AdelicExp.lean` |
| `td(G)` and `nala(G)` divisible | `tdSet_divisible`, `nala_divisible` | `AdelicExp.lean` |
| adelic exponential `exp(f) = f(1,1)`, continuous; `exp(f) = exp_n(f|ℤ̂) · exp_a(f|ℝ)` | `expAd`, `continuous_expAd`, `expAd_eq` | `AdelicExp.lean` |
| **`arla(G) ≅ ℝⁿ`**, `n = dim_a G` | `arlaEquiv` (`psiA_injective`), `arla_real` | `ArlaReal.lean` |
| **Theorem `symmetric-adelic-lie-algebra`**: decomposition, `nala(G)` divisible periodic LCA, `arla(G) ≅ ℝⁿ`, adelic exponential | `symmetric_adelic_lie_algebra_fd` | `ArlaReal.lean` |

Not yet in Lean: `dim_n nala(G) = n = dim_a arla(G)` (needs `dim_n`, from Lewis 2019's standard
representation), and the uniqueness statements the paper cites from HHR Theorem 3.3.

### Theorem *Topological Characterisation via Nonarchimedean Exponential* (`topological-characterisation-nonarchimedean-exponential`): certified

`topological_characterisation` (`TopCharacterisation.lean`): for a nontrivial protorus `G` (compact,
connected, Hausdorff, abelian) and a delta-subgroup `Δ` (`IsDelta Δ n`: `Δ` closed, totally
disconnected, `G/Δ ≅ (ℝ/ℤ)ⁿ`), `exp_n(f) = f(1)` is a continuous algebraic isomorphism of
`nala(G)` onto `td(G)`; `td(G)` is not locally compact and `exp_n` is not open; `K_Δ` is open in
`nala(G)`, evaluation at `1` is a topological isomorphism `K_Δ ≅ Δ`, and `Δ` is compact and not
open in `td(G)`.

`td(G)` is the union of the compact totally disconnected subgroups of `G` (`tdSet`). Ingredients
(the first block holds for every commutative Hausdorff topological group `G`):

| Paper claim | Lean declaration | File |
|---|---|---|
| `ℤ` dense in `ℤ̂`; `dℤ̂` open | `denseRange_iZ`, `isOpen_nsmulZ` | `ZHatAction.lean` |
| canonical `ℤ̂`-action: `x ∈ P` profinite abelian gives a unique continuous `f : ℤ̂ → P`, `f 1 = x` | `exists_zhatHom`, `zhatHom_ext` | `ZHatAction.lean` |
| image of `ℤ̂` under a continuous homomorphism is totally disconnected | `range_totallyDisconnected` | `NonarchExp.lean` |
| `exp_n(f) = f(1)` continuous, injective | `continuous_expn`, `expn_injective` | `NonarchExp.lean` |
| image of `exp_n` = `td(G)`; `td(G)` a subgroup | `range_expn`, `td`, `mem_td_iff` | `NonarchExp.lean` |
| `td` fully invariant (functorial) | `map_td_le`, `td_fullyInvariant` | `NonarchExp.lean` |
| `exp_n : nala(G) → td(G)` continuous algebraic isomorphism | `nonarchimedean_exponential`, `expnEquiv` | `NonarchExp.lean` |
| the torus `(ℝ/ℤ)ⁿ` has no small subgroups; its torsion is dense | `torus_nss`, `dense_torsion_torus` | `DeltaSubgroup.lean` |
| the canonical `ℤ̂`-action is jointly continuous | `continuous_act` | `DeltaSubgroup.lean` |
| `K_Δ` open in `nala(G)` | `isOpen_Kdelta` | `DeltaSubgroup.lean` |
| **`K_Δ ≅ Δ`** by evaluation at `1`; `exp_n(K_Δ) = Δ` | `kdeltaEquiv`, `expn_image_Kdelta` | `DeltaSubgroup.lean` |
| `td(G) = q⁻¹(torsion of (ℝ/ℤ)ⁿ)`, `q : G → G/Δ` | `torsion_of_mem_tdSet`, `mem_tdSet_of_torsion` | `TopCharacterisation.lean` |
| `td(G)` dense in `G` | `dense_tdSet` | `TopCharacterisation.lean` |
| `Δ` not open in `td(G)`; `exp_n` not open; `td(G)` not locally compact | `not_isOpen_delta`, `not_isOpenMap_expn`, `not_locallyCompact_td` | `TopCharacterisation.lean` |
| **Theorem `topological-characterisation-nonarchimedean-exponential`** | `topological_characterisation` | `TopCharacterisation.lean` |

| **every finite-dimensional protorus has a delta-subgroup**, `G/Δ ≅ (ℝ/ℤ)^{dim_a G}` | `exists_delta` | `DeltaExistence.lean` |
| unconditional form: `td(G)` not locally compact, `exp_n` not open | `topological_characterisation_of_fd` | `DeltaExistence.lean` |

`exists_delta`: with `ι : G^∨ → ℚⁿ` injective, `ℤⁿ ⊆ ι(G^∨)`, and characters `d_j` with
`ι(d_j) = e_j`, `Δ = ker(g ↦ (d_j(g))_j)`. Surjectivity of `G → (ℝ/ℤ)ⁿ` comes from the adelic
characters `Φ_ι(a)` and double duality; `Δ` is totally disconnected because every character
maps `Δ` into a finite group of roots of unity.

### Theorem *Adelic Exponential Yields Lie Category* (`adelic-exponential-lie-category`): certified

`adelic_exponential_lie_category` (`LieCategory.lean`): for a finite-dimensional protorus `G`,
`n = dim_a G`, the adelic exponential `exp(f) = f(1, 1)`, read on `nala(G) × arla(G)` as
`E(f, g) = f(1) · g(1)`, is continuous, surjective and open, with discrete kernel isomorphic to
`ℚⁿ`. The paper cites \[DLLM, Theorem 15\]; the Lean proof is self-contained.

| Ingredient | Lean declaration | File |
|---|---|---|
| `Δ = ker(g ↦ (d_j(g))_j)` is a delta-subgroup | `ker_qmap_isDelta` | `DeltaExistence.lean` |
| `E` surjective: `x = (x v_θ(1)⁻¹) · v_θ(1)`, first factor in `Δ ⊆ td(G)` | `E_surjective` | `LieCategory.lean` |
| `v_θ(1) ∈ td(G)` iff `θ ∈ (2πℚ)ⁿ`; `exp θ` torsion iff `θ ∈ 2πℚ` | `vθ_one_mem_td_iff`, `circle_torsion_iff` | `LieCategory.lean` |
| **`ker E ≅ ℚⁿ`**; `ker E` discrete | `kerE_equiv`, `discrete_kerE` | `LieCategory.lean` |
| `nala(G)` σ-compact (torsion of the torus countable); `E` open (open mapping theorem) | `countable_torsion_torus`, `sigmaCompact_nala`, `E_isOpenMap` | `LieCategory.lean` |
| **Theorem `adelic-exponential-lie-category`** | `adelic_exponential_lie_category` | `LieCategory.lean` |
| **`exp_a(Hom(ℝ, G))` dense in `G`** (characters trivial on it vanish) | `dense_range_expa`, `exists_char_of_not_dense` | `ArcDense.lean` |

### Theorem *The Kumu* (`kumu`): certified

The **kumu** of `G` is `κ(G) = td(G) ∩ a(G)` (`kumu`). `kumu_theorem` (`Kumu.lean`): for a
torus-free finite-dimensional protorus `G`, `n = dim_a G`, the kumu is a dense, fully invariant
subgroup of `G`, algebraically isomorphic to `ℚⁿ`. The paper cites \[DLLM, Theorem 15\]; the Lean
proof is self-contained.

`a(G)` is the path component of `0`. In Lean `arcSub` is the image `exp_a(Hom(ℝ, G))`, and
`range_expa_eq_pathComponent` (`ArcComponent.lean`) proves it equals the path component of `0`
(Hofmann–Morris, *The Structure of Compact Groups*, 4th ed., Theorem 8.30, p. 430). The Lean proof
lifts `χ ∘ γ` through `exp : ℝ → 𝕋` for each character `χ` and path `γ`. Also certified:
`a(G)` is divisible (`arcSub_divisible`) and fully invariant (`map_arcSub_le`), and for torus-free
`G` with `dim_a G > 0` the continuous injective `exp_a` is not open (`not_isOpenMap_expa`). For a
torus `exp_a` is open and has nonzero kernel, so torus-freeness is needed there. `G` is torus-free (`TorusFree`) if no subgroup is topologically isomorphic to `(ℝ/ℤ)^k`,
`k ≥ 1`.

| Ingredient | Lean declaration | File |
|---|---|---|
| `κ(G)` functorial, hence fully invariant | `map_kumu_le` | `Kumu.lean` |
| torus-free forces `θ ↦ exp_a(v_θ)` injective (a period gives an injective `ℝ/ℤ → G`) | `not_torusFree_of_injective`, `expa_vθ_injective` | `Kumu.lean` |
| `x ∈ κ(G)` iff `x = exp_a(v_θ)`, `θ ∈ (2πℚ)ⁿ` | `mem_kumu_iff` | `Kumu.lean` |
| **`κ(G) ≅ ℚⁿ`**, `r ↦ exp_a(v_{2πr})`; `κ(G)` dense | `kumuEquiv`, `dense_kumu` | `Kumu.lean` |
| `a(G) = exp_a(Hom(ℝ, G))` is the path component of `0` | `range_expa_eq_pathComponent` | `ArcComponent.lean` |
| `a(G)` divisible, fully invariant; `exp_a` not open | `arcSub_divisible`, `map_arcSub_le`, `not_isOpenMap_expa` | `ArcComponent.lean` |
| **Theorem `kumu`** | `kumu_theorem` | `Kumu.lean` |

### Remark *Dense Subgroups and Dual Topologies* (`dense-subgroups-dual-topologies`): certified

`dense_subgroups_dual_topologies` (`DualTopology.lean`): for a discrete torsion-free `A` with
`ι : A → ℚⁿ` injective of full rank and `Hom(A, ℤ) = 0`, the archimedean exponential
`exp_a : ℝⁿ → A^∨`, `exp_a(x)(a) = e^{2πi⟨x, ι a⟩}`, is continuous and injective, and
`B = exp_a(ι(A)) ≅ A` is dense in the compact Hausdorff group `A^∨`, so `A^∨` is the completion
of `A` in its dual topology. `hom_eq_zero_of_noFreeSummand`: no free summands gives
`Hom(A, ℤ) = 0`. The Lean proof is by duality and does not use the structure theorem for closed
subgroups of `ℝⁿ`.

### Self-duality of the adeles: certified

`adeleSelfDual` (`AdelicDual.lean`): `𝔸 = ℚ̂ × ℝ` is a self-dual locally compact abelian group;
`(u, t) ∈ 𝔸` corresponds to the character `(x, y) ↦ e(ψ(u x)) · exp(i t y)`
(`adeleChar_injective`, `adeleChar_surjective`, packaged as `adele_self_dual`).

### Example `(𝔸/ℤ)^∨ ≅ ℤ̂ × ℚ`: certified

`closing_example` (`AdelicDual.lean`): the diagonal `ℤ` is closed in `𝔸` (`isClosed_Zd`),
`𝔸/ℤ` is locally compact Hausdorff, and `adeleModZDual : ℤ̂ × ℚ ≃ₜ* (𝔸/ℤ)^∨` with `ℤ̂` compact and
`ℚ` discrete; `(z, q)` goes to the character induced by `(z + q, -2πq) ∈ 𝔸`. The Lean proof
identifies the characters of `𝔸` trivial on `ℤ` directly, using strong approximation
`ℚ̂ = ℚ + ℤ̂`, rather than the paper's dual short exact sequence.

Corollary *Five Equivalents* (`G ≅ H`, `td(G) ≅ td(H)`, `κ(G) ≅ κ(H)`, `a(G) ≅ a(H)`, `G` homeomorphic
to `H`) is a **cited result**, not formalized: its proof rests on Dikranjan–Lewis–Loth–Mader
(Theorem 12, Proposition 9(3)) and Hofmann–Morris, *The Structure of Compact Groups*, Theorem 8.58.

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
| `AdelicToriLean/AdelicModel.lean` | the map `Φ : 𝔸ⁿ → D^∨`, kernel, surjectivity |
| `AdelicToriLean/AdelicTorus.lean` | `(𝔸ⁿ / C) / Λ ≅ D^∨` |
| `AdelicToriLean/RankEmbedding.lean` | `ℤⁿ ⊆ A ⊆ ℚⁿ` for torsion-free `A` of rank `n` |
| `AdelicToriLean/Fdccg.lean` | **Theorem `fdccg-adelic-tori`** |
| `AdelicToriLean/AdelicTorusProps.lean` | properties of `C` and `Λ` |
| `AdelicToriLean/SpectrumResolution.lean` | `(L_B × V)/B ≅ (C × V)/ℤⁿ`, general form |
| `AdelicToriLean/SpectrumPaper.lean` | **Theorem `spectrum-resolutions`**; `L_B` Hausdorff, exact, periodic |
| `AdelicToriLean/QHatDual.lean` | `ℚ̂` LCA; `ℤ̂^⊥ = ℤ̂`; nondegeneracy |
| `AdelicToriLean/QHatSelfDual.lean` | `ℚ̂ ≅ ℚ̂^∨` |
| `AdelicToriLean/QHatnDual.lean` | characters of `ℚ̂ⁿ`; `C^⊥⊥ = C` |
| `AdelicToriLean/DualityTools.lean` | surjectivity by duality; extension of characters |
| `AdelicToriLean/PerpQuot.lean` | `C^⊥/C` self-dual |
| `AdelicToriLean/ModelLattice.lean` | `L = C^⊥/C` of the adelic model, self-dual |
| `AdelicToriLean/ModelSequence.lean` | the exact sequence `0 → G^∨ → L × ℝⁿ → G → 0` |
| `AdelicToriLean/ModelProper.lean` | properness; `L` periodic |
| `AdelicToriLean/RealDual.lean` | `ℝⁿ ≅ (ℝⁿ)^∨` |
| `AdelicToriLean/DualProd.lean` | dual of a product |
| `AdelicToriLean/SelfDualPSES.lean` | **Theorem `self-dual-pses`** |
| `AdelicToriLean/AdelicLieAlgebra.lean` | `adla(G) ≅ nala(G) × arla(G)` |
| `AdelicToriLean/ZHatAction.lean` | density of `ℤ` in `ℤ̂`; the canonical `ℤ̂`-action |
| `AdelicToriLean/NonarchExp.lean` | `exp_n : nala(G) → td(G)` |
| `AdelicToriLean/DeltaSubgroup.lean` | delta-subgroups; `K_Δ` open; `K_Δ ≅ Δ` |
| `AdelicToriLean/TopCharacterisation.lean` | **Theorem `topological-characterisation-nonarchimedean-exponential`** |
| `AdelicToriLean/DeltaExistence.lean` | existence of delta-subgroups |
| `AdelicToriLean/NalaPeriodic.lean` | **Lemma `nala-periodic-lca`** |
| `AdelicToriLean/AdelicExp.lean` | divisibility; the adelic exponential |
| `AdelicToriLean/ArlaReal.lean` | `arla(G) ≅ ℝⁿ`; **Theorem `symmetric-adelic-lie-algebra`** |
| `AdelicToriLean/LieCategory.lean` | **Theorem `adelic-exponential-lie-category`** |
| `AdelicToriLean/ArcDense.lean` | `exp_a(Hom(ℝ, G))` dense |
| `AdelicToriLean/Kumu.lean` | **Theorem `kumu`** |
| `AdelicToriLean/DualTopology.lean` | **Remark `dense-subgroups-dual-topologies`** |
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
that all 188 audited declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

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
- `audits/axioms.txt` lists the axioms of 188 declarations: 184 from AdelicTori (every paper-facing
  statement and the key lemmas) and 4 from the vendored Pontryagin library. Each depends only on
  `propext`, `Classical.choice`, `Quot.sound`.
