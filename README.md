# AdelicToriLean
[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/WayneManAloha/AdelicTori)

**Complete formalization of all proved results:** Every original theorem, lemma, remark, and example in **"Finite-Dimensional Protori Are Adelic Tori"** by Wayne Lewis ([arXiv:2411.16000](https://arxiv.org/abs/2411.16000)) has been formalized and machine-checked in Lean 4 with Mathlib (Theorems 5, 6, 7, 10, 12, 13, 14, 17, and 19, Lemma 8, Remark 15, and Example 20). The sole unformalized statement is Corollary 16, whose proof follows directly from cited results in Dikranjan–Lewis–Loth–Mader and Hofmann–Morris.

- **234 audited declarations (`audits/axioms.txt`)** checked in Lean 4 (`v4.34.0-rc2`) using only standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero `sorry`, `admit`, `native_decide`, or custom axioms:
  - **22** for the discrete arithmetic core (`End(B_K) = 𝒪_K`, strong indecomposability, local freeness, `t(ℤ)`-homogeneity, and unconditional existence of `DegreeOnePrimes K` via `exists_degreeOnePrimes` and `exists_groupOfIntegers`);
  - **29** for **Theorem 5** (`fdccg-adelic-tori`) and its ingredients;
  - **6** for **Theorem 6** (`spectrum-resolutions`);
  - **27** for **Theorem 7** (`self-dual-pses`) and its ingredients;
  - **12** for **Theorem 10** (`symmetric-adelic-lie-algebra`) and the adelic exponential;
  - **23** for **Theorem 12** (`topological-characterisation-nonarchimedean-exponential`) and its ingredients (the canonical `ℤ̂`-action, delta-subgroups, `K_Δ ≅ Δ`);
  - **4** for the existence of delta-subgroups (`exists_delta`);
  - **6** for **Lemma 8** (`nala-periodic-lca`);
  - **10** for **Theorem 13** (`adelic-exponential-lie-category`, self-contained Lean proof);
  - **2** for the density of `exp_a(Hom(ℝ, G))`;
  - **7** for **Theorem 14** (`kumu`, self-contained Lean proof);
  - **5** for **Remark 15** (`dense-subgroups-dual-topologies`);
  - **4** for the Pontryagin self-duality of `𝔸`;
  - **5** for **Example 20** (`(𝔸/ℤ)^∨ ≅ ℤ̂ × ℚ`);
  - **6** for `a(G)` (path component, divisible, fully invariant, `exp_a` not open);
  - **29** for the topological and adelic Lie resolutions in **Theorem 17** (`zassenhaus-realisation`);
  - **21** for the nonarchimedean dimension (`dim_n`) and **Theorem 19** (`nonarchimedean-line-number-field`);
  - **12** for `dim_n ℒ_n(G) = n`, the adelic covering module, and the Arnold Theorem 0.2 calibration;
  - **4** imported from the vendored Pontryagin duality library.

## Paper-to-Lean master index

| Paper item | Statement | Primary Lean declaration(s) | File(s) | Status |
|---|---|---|---|---|
| **Theorem 5** (`fdccg-adelic-tori`) | Every finite-dimensional protorus is an adelic torus `(𝔸ⁿ/C)/Λ` | `fdccg_adelic_tori` | `Fdccg.lean` | **Certified** |
| **Theorem 6** (`spectrum-resolutions`) | Spectrum of resolutions `G ≅ (L_B × ℝⁿ)/B` | `spectrum_of_resolutions` | `SpectrumPaper.lean` | **Certified** |
| **Theorem 7** (`self-dual-pses`) | Pontryagin self-dual proper SES `0 → G^∨ → L × ℝⁿ → G → 0` | `self_dual_pses` | `SelfDualPSES.lean` | **Certified** |
| **Lemma 8** (`nala-periodic-lca`) | `ℒ_n(G) = Hom(ℤ̂, G)` is periodic LCA and `ev_1 : ℒ_n(G) ≅ td(G)` | `nala_periodic_lca` | `NalaPeriodic.lean` | **Certified** |
| **Theorem 10** (`symmetric-adelic-lie-algebra`) | `ℒ(G) ≅ ℒ_n(G) × ℒ_a(G)` with `(dim_n ℒ_n(G), dim_a ℒ_a(G)) = (n, n)` | `symmetric_adelic_lie_algebra_fd`, `symmetric_adelic_lie_algebra_dim` | `ArlaReal.lean`, `LieDim.lean` | **Certified** |
| **Theorem 12** (`topological-characterisation-nonarchimedean-exponential`) | `exp_n : ℒ_n(G) → td(G)` continuous algebraic iso, not open; `td(G)` not locally compact | `topological_characterisation`, `topological_characterisation_of_fd` | `TopCharacterisation.lean`, `DeltaExistence.lean` | **Certified** |
| **Theorem 13** (`adelic-exponential-lie-category`) | `exp : ℒ(G) → G` is continuous, surjective, open with discrete kernel `≅ ℚⁿ` | `adelic_exponential_lie_category` | `LieCategory.lean` | **Certified** |
| **Theorem 14** (`kumu`) | Kumu `κ(G) = td(G) ∩ a(G)` of torus-free `G` is dense, fully invariant, `≅ ℚⁿ` | `kumu_theorem` | `Kumu.lean` | **Certified** |
| **Remark 15** (`dense-subgroups-dual-topologies`) | Completion of `A` in its dual topology is `A^∨` | `dense_subgroups_dual_topologies` | `DualTopology.lean` | **Certified** |
| **Corollary 16** | Five equivalents of topological isomorphism for torus-free `G, H ∈ AT` | — (follows directly from `[DLLM, Thm. 12]` and `[HM, Thm. 8.58]`) | — | Paper only |
| **Theorem 17** (`zassenhaus-realisation`) | Adelic realisation of a group of integers `B_K` for every number field `K` | `exists_groupOfIntegers`, `zassenhaus_topological`, `resolutionEquiv`, `zassenhaus_lie` | `Unconditional.lean`, `ZassenhausRealisation.lean`, `ZassenhausTopology.lean`, `ZassenhausLie.lean` | **Certified** |
| **Theorem 19** (`nonarchimedean-line-number-field`) | Nonarchimedean dimension of any number field `K` is `dim_n K = 1` | `dimNK_eq_one` | `NumberFieldDimK.lean` | **Certified** |
| **Example 20** | Pontryagin dual `(𝔸/ℤ)^∨ ≅ ℤ̂ × ℚ` | `closing_example`, `adeleModZDual` | `AdelicDual.lean` | **Certified** |

## What does it mean that a proof has been checked by Lean?

**Lean is a computer program that checks mathematical proofs.**

A mathematician writes a theorem, its assumptions, and a proof in Lean's precise mathematical language. Lean then checks whether every step of the proof is logically justified.

If the proof passes, Lean has verified that **the stated conclusion follows from the stated assumptions**.

It does **not** mean that:
- A journal or mathematical institution has certified the result.
- Lean has proved assumptions that the formal theorem explicitly takes for granted.
- The formal theorem necessarily says exactly what the author intended. That correspondence must also be checked by mathematicians (the detailed theorem-to-declaration maps below document the exact formal hypotheses and conclusions for each result).

### What has Lean checked in this repository?

All 234 audited declarations—covering both the discrete algebraic core (`B_K = ∑_k 𝔭_k⁻¹`, `End(B_K) = 𝒪_K`, strong indecomposability, and `exists_degreeOnePrimes`) and the topological/adelic Lie theory (adelic tori, delta-subgroups, Pontryagin self-dual resolutions, `ℒ(G) ≅ ℒ_n(G) × ℒ_a(G)`, the adelic exponential, the kumu `κ(G)`, and `dim_n K = 1`)—have been verified in Lean 4 using a vendored Pontryagin duality library.

The accompanying axiom audit (`audits/axioms.txt`) confirms that all 234 checked declarations use only Lean's standard foundational axioms, with no missing proofs inserted using `sorry`.

### What does a successful build mean?

When `lake build` completes successfully, Lean has accepted the proofs included in that build.

**In short: Lean checks exactly what we tell it to prove, using exactly the assumptions we give it.**

## Verify the proofs in GitHub Codespaces

Click the "Open in GitHub Codespaces" button above.

Once the development environment is ready, open a terminal and run:

    lake build
    lake env lean scripts/Audit.lean

The repository contains 234 audited Lean declarations.
See `audits/axioms.txt` for their axiom dependencies.

No local Lean installation is required.

## Status at a glance

| Category | Meaning |
|---|---|
| **Certified** | Checked in Lean, no `sorry`, no new axioms. The discrete theorems are stated for any `D : DegreeOnePrimes K`, and such `D` exists for every number field (`exists_degreeOnePrimes`). |
| **Paper only** | Established in the paper from cited results, not formalized in Lean (Corollary 16 only). |

### The data `DegreeOnePrimes K`

```lean
structure DegreeOnePrimes (K) where
  q : ℕ → ℕ
  P : ℕ → Ideal (𝓞 K)
  q_prime : ∀ k, (q k).Prime
  q_inj : Function.Injective q
  norm_eq : ∀ k, Ideal.absNorm (P k) = q k
