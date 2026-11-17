import AdelicToriLean.LocalFree

/-!
# Paper-facing statements

Lean counterparts of the discrete algebraic content of *Finite-Dimensional Protori Are Adelic
Tori* (W. Lewis), Section 4, Theorem `zassenhaus-realisation` and Theorem
`nonarchimedean-line-number-field`.

Every statement below is proved for an arbitrary `D : DegreeOnePrimes K`: a sequence of ideals
`P k` of `𝓞 K` of absolute norm `q k`, the `q k` pairwise distinct primes. This is the only
external input. Existence of such a sequence (e.g. from infinitely many primes splitting
completely in a Galois closure of `K`) is classical and is NOT proved here.

The paper also uses Pontryagin duality to pass from these discrete statements to the adelic
torus `B_K^∨` (delta-subgroups, nonarchimedean dimension of `B_K^∨`); those steps are not
formalized.
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

/-- `𝓞 K ⊆ B_K ⊆ K` and `ℚ B_K = K`. -/
theorem BK_sandwich :
    D.OK ≤ D.BK ∧ ∀ x : K, ∃ n : ℤ, n ≠ 0 ∧ (n : K) * x ∈ D.BK := by
  refine ⟨D.OK_le_BK, fun x => ?_⟩
  obtain ⟨n, hn, o, ho⟩ := DegreeOnePrimes.exists_int_mul_mem x
  exact ⟨n, hn, by rw [← ho]; exact D.OK_le_BK (D.coe_mem_OK o)⟩

/-- `End_ℤ(B_K) ≅ 𝓞 K` as rings. -/
def endRingEquiv : Module.End ℤ D.BK ≃+* 𝓞 K := D.endEquiv

/-- Every additive endomorphism of `B_K` is multiplication by a unique element of `𝓞 K`. -/
theorem end_eq_mul (f : D.BK →+ D.BK) : ∃! o : 𝓞 K, ∀ x : D.BK, (f x : K) = (o : K) * x :=
  D.endo_eq_mul f

/-- `ℚ End(B_K) ≅ K`: every quasi-endomorphism of `B_K` is multiplication by an element of `K`. -/
theorem qEnd_eq_mul (φ : K →ₗ[ℚ] K) (n : ℕ) (hn : n ≠ 0)
    (hφ : ∀ x ∈ D.BK, (n : K) * φ x ∈ D.BK) : ∃ α : K, ∀ x : K, φ x = α * x :=
  D.quasiEnd_eq_mul φ n hn hφ

/-- Strong indecomposability: every idempotent quasi-endomorphism of `B_K` is `0` or `1`. -/
theorem stronglyIndecomposable (e : K →ₗ[ℚ] K) (n : ℕ) (hn : n ≠ 0)
    (he : ∀ x ∈ D.BK, (n : K) * e x ∈ D.BK) (hidem : e ∘ₗ e = e) :
    e = 0 ∨ e = LinearMap.id :=
  D.quasiIdempotent e n hn he hidem

/-- Local freeness: `(B_K)_(ℓ) ≅ ℤ_(ℓ)^[K:ℚ]` for every prime `ℓ`. -/
theorem locallyFree (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ L : Submodule ℤ K, L ≤ D.BK.restrictScalars ℤ ∧ Module.Free ℤ L ∧ Module.Finite ℤ L ∧
      Module.finrank ℤ L = Module.finrank ℚ K ∧
      ∀ x ∈ D.BK, ∃ e : ℕ, ¬ ℓ ∣ e ∧ (e : K) * x ∈ L :=
  D.locallyFree ℓ hℓ

/-- `t(ℤ)`-homogeneity, for `[K : ℚ] ≥ 2`. -/
theorem homogeneous_tZ (hn : 2 ≤ Module.finrank ℚ K) {x : K} (hx0 : x ≠ 0) :
    {ℓ : ℕ | ℓ.Prime ∧ ∃ y ∈ D.BK, x = (ℓ : K) * y}.Finite ∧
      ∀ ℓ : ℕ, ℓ.Prime → ∃ N : ℕ, ¬ ∃ y ∈ D.BK, x = ((ℓ ^ N : ℕ) : K) * y :=
  D.homogeneous hn hx0

/-- The `q_k`-primary component of `B_K / 𝓞 K` is `(P k)⁻¹ / 𝓞 K`. -/
theorem primary_component_q (k N : ℕ) {x : K} (hx : x ∈ D.BK)
    (hN : ((D.q k ^ N : ℕ) : K) * x ∈ D.OK) : x ∈ (D.Pinv k : Submodule (𝓞 K) K) :=
  D.primary_q k N hx hN

/-- For a prime `ℓ` different from every `q_k`, the `ℓ`-primary component of `B_K / 𝓞 K` is
trivial. -/
theorem primary_component_other {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ∀ k, D.q k ≠ ℓ) (N : ℕ) {x : K}
    (hx : x ∈ D.BK) (hN : ((ℓ ^ N : ℕ) : K) * x ∈ D.OK) : x ∈ D.OK :=
  D.primary_other hℓ hℓq N hx hN

/-- `(P k)⁻¹ / 𝓞 K` is cyclic of prime order `q_k`. -/
theorem primary_component_cyclic (k : ℕ) :
    Nat.card (D.PinvQuot k) = D.q k ∧ IsAddCyclic (D.PinvQuot k) :=
  ⟨D.card_PinvQuot k, D.isAddCyclic_PinvQuot k⟩

/-- Lower bound used for `dim_n K ≥ 1`: if `𝓞 K ≤ B ≤ K` and `B / 𝓞 K` is finite, then `B` is free
of rank `[K : ℚ]` (so it is its own free summand). Hence every group of integers without free
summands has `B / 𝓞 K` infinite. -/
theorem free_of_finite_quotient (B : Submodule ℤ K) (hOB : D.OZ ≤ B)
    [Finite (B ⧸ (D.OZ.comap B.subtype))] :
    Module.Free ℤ B ∧ Module.Finite ℤ B ∧ Module.finrank ℤ B = Module.finrank ℚ K :=
  D.freeOfFiniteQuot B hOB

end AdelicToriLean
