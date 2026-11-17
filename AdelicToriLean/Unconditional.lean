import AdelicToriLean.Paper
import AdelicToriLean.Existence

/-!
# Unconditional group of integers

With `exists_degreeOnePrimes`, the discrete realisation holds for every number field, with no
external input.
-/

open NumberField

noncomputable section

namespace AdelicToriLean

variable (K : Type*) [Field K] [NumberField K]

/-- **Discrete part of Theorem `zassenhaus-realisation`, unconditional.** Every number field `K`
has a subgroup `𝓞 K ⊆ B ⊆ K` with `ℚ B = K` such that:
* every additive endomorphism of `B` is multiplication by a unique element of `𝓞 K`;
* every quasi-endomorphism of `B` is multiplication by an element of `K`;
* `B` is locally free of rank `[K : ℚ]` at every prime;
* each primary component of `B / 𝓞 K` is cyclic of prime order or trivial, and infinitely many
  are nontrivial. -/
theorem exists_groupOfIntegers :
    ∃ D : DegreeOnePrimes K,
      D.OK ≤ D.BK ∧ (∀ x : K, ∃ n : ℤ, n ≠ 0 ∧ (n : K) * x ∈ D.BK) ∧
      (∀ f : D.BK →+ D.BK, ∃! o : 𝓞 K, ∀ x : D.BK, (f x : K) = (o : K) * x) ∧
      (∀ (φ : K →ₗ[ℚ] K) (n : ℕ), n ≠ 0 → (∀ x ∈ D.BK, (n : K) * φ x ∈ D.BK) →
        ∃ α : K, ∀ x : K, φ x = α * x) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ∃ L : Submodule ℤ K, L ≤ D.BK.restrictScalars ℤ ∧ Module.Free ℤ L ∧
        Module.Finite ℤ L ∧ Module.finrank ℤ L = Module.finrank ℚ K ∧
        ∀ x ∈ D.BK, ∃ e : ℕ, ¬ ℓ ∣ e ∧ (e : K) * x ∈ L) ∧
      (∀ k, Nat.card (D.PinvQuot k) = D.q k ∧ IsAddCyclic (D.PinvQuot k)) := by
  obtain ⟨D⟩ := exists_degreeOnePrimes (K := K)
  exact ⟨D, (BK_sandwich D).1, (BK_sandwich D).2, end_eq_mul D,
    fun φ n hn hφ => qEnd_eq_mul D φ n hn hφ, locallyFree D, primary_component_cyclic D⟩

end AdelicToriLean
