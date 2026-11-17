# AdelicToriLean

**Release `v0.1.0-discrete-core`: an intermediate certified release.** This release does not
formalize the whole paper.
- The 18 audited declarations (`audits/axioms.txt`) are certified under the explicitly stated
  hypothesis `DegreeOnePrimes K`.
- The existence of a `DegreeOnePrimes K` sequence is not formally certified here.
- The manuscript's topological theorems are not formally certified here.

Lean 4 companion to the paper **"Finite-Dimensional Protori Are Adelic Tori"** by Wayne Lewis,
[arXiv:2411.16000](https://arxiv.org/abs/2411.16000).

This repository certifies the **discrete algebraic core** of the paper's number-field
construction: the group of integers `B_K = Σ_k 𝔭_k⁻¹` attached to a number field `K`, its
endomorphism ring, and the structure of `B_K / 𝒪_K` underlying the statement that the
nonarchimedean dimension of every number field is `1`.

The topological parts of the paper (Pontryagin duality, adelic tori, delta-subgroups, the
adelic Lie algebra) are **not** formalized here. The status of each result is listed below.

## Status at a glance

| Category | Meaning |
|---|---|
| **Certified (conditional on the external input)** | Proved in Lean from the hypothesis `DegreeOnePrimes K` described below. No `sorry`, no new axioms. |
| **External input** | One hypothesis, stated explicitly as a Lean structure and never proved here. |
| **Paper only** | Established in the paper, not formalized in Lean. |

### The external input

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
- Its existence is classical. For example, infinitely many rational primes split completely in a
  Galois closure of `K`, and each has a degree-one prime of `𝒪_K` above it. This existence is
  **not** proved in Lean.
- Every Lean theorem below holds for **every** such sequence.
- The hypothesis is weaker than the paper's: complete splitting and the paper's rotation of the
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
| existence of infinitely many suitable primes | input `DegreeOnePrimes K` | `Basic.lean` | external input |
| `T_K^∨` is a delta-subgroup of `B_K^∨`, density of the diagonal `𝒪_K`, the isomorphisms `B_K^∨ ≅ (T_K^∨ × ℝ·K)/𝒪_K ≅ (ℒ_n(B_K^∨) × ℝ·K)/K` | none | none | paper only (Pontryagin duality) |

### Paper Theorem *Nonarchimedean Line through a Number Field* (`nonarchimedean-line-number-field`)

| Paper statement | Lean declaration | Status |
|---|---|---|
| upper bound: `B_K/𝒪_K ≅ ⊕_k ℤ/q_k`, every primary component cyclic of prime order or trivial | `primary_component_q`, `primary_component_other`, `primary_component_cyclic` | certified (discrete side) |
| lower bound: a group of integers with no free summands has `B/𝒪_K` infinite | `free_of_finite_quotient` (if `B/𝒪_K` is finite, then `B` is free of rank `[K:ℚ]`) | certified (discrete side) |
| passage to `dim_n(B_K^∨) = 1` via the standard representation of `(B_K/𝒪_K)^∨` | none | paper only (Pontryagin duality, [Lewis 2019, Prop. 1, Lemma 6, Cor. 4]) |

### Other results of the paper

These are all **paper only**:
- Theorem *Finite-Dimensional Compact Connected Groups Are Adelic Tori*;
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

Mathlib defines the Pontryagin dual but does not yet provide the duality theorem for locally
compact abelian groups. Formalizing these results is planned for later work.

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
| `AdelicToriLean/Basic.lean` | external input `DegreeOnePrimes`, `𝔭_k⁻¹`, `B_K` |
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
| `scripts/Audit.lean` | `#print axioms` for the paper-facing statements and key lemmas |
| `audits/` | full build log and axiom audit output |

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

**Continuous integration.** `.github/workflows/build.yml` builds with `--wfail`, rejects
`sorry`/`admit`/`native_decide`/`axiom`, and checks that all 18 audited declarations depend only
on `propext`, `Classical.choice`, `Quot.sound`.

**Codespaces.** `.devcontainer/devcontainer.json` installs `elan`, fetches the Mathlib cache and
builds on creation.

## License

Apache License 2.0, copyright 2026 Wayne Lewis. See `LICENSE` and `NOTICE`.

## Verification record

- `lake build` completes with exit code 0, 0 errors, 0 warnings (`audits/FullBuild.log`).
- The source contains no `sorry`, `admit`, `native_decide` or `axiom`.
- `audits/axioms.txt` lists the axioms of 18 declarations: every paper-facing statement and the
  key lemmas. Each depends only on `propext`, `Classical.choice`, `Quot.sound`.
