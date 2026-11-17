import AdelicToriLean.AdelicTorusProps
import Pontryagin.Duality

/-!
# Self-duality of the finite adeles `ℚ̂`

* `T2Space QHat`, `LocallyCompactSpace QHat`;
* `psi_single`: `ψ` of an adele supported at one place is that place's fractional part;
* `mem_ZHat_of_psi`: if `ψ(u z) = 0` for all `z ∈ ℤ̂` then `u ∈ ℤ̂` (`ℤ̂^⊥ = ℤ̂`);
* `exists_psi_ne_zero`: for `u ≠ 0` some `v` has `ψ(u v) ≠ 0`.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum Topology

noncomputable section

open Classical in
attribute [local instance] Classical.decEq

namespace AdelicToriLean

instance : T2Space QHat :=
  T2Space.of_injective_continuous (fun _ _ h => Subtype.ext h)
    (RestrictedProduct.continuous_coe (R := fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
      (A := fun v => (v.adicCompletionIntegers ℚ)) (𝓕 := Filter.cofinite))

instance : LocallyCompactSpace QHat :=
  isCompact_ZHat.locallyCompactSpace_of_mem_nhds_of_addGroup
    (isOpen_ZHat.mem_nhds ZHat.zero_mem)

/-- The adele supported at `v` with value `x`. -/
def singleAt (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) : QHat :=
  RestrictedProduct.single (fun w : HeightOneSpectrum ℤ => (w.adicCompletionIntegers ℚ)) v x

theorem singleAt_apply (v w : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    singleAt v x w = Pi.single v x w := rfl

theorem frV_eq_zero_iff {v : HeightOneSpectrum ℤ} (x : v.adicCompletion ℚ) :
    frV v x = 0 ↔ x ∈ v.adicCompletionIntegers ℚ := by
  have : Fact ((primesEquiv v : ℕ).Prime) := ⟨(primesEquiv v).prop⟩
  rw [mem_integers_iff]
  exact fractP_eq_zero_iff _ _

theorem psi_singleAt (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    psi (singleAt v x) = frV v x := by
  rw [psi_apply, finsum_eq_single _ v]
  · rw [singleAt_apply, Pi.single_eq_same]
  · intro w hw
    rw [singleAt_apply, Pi.single_eq_of_ne hw, map_zero]

theorem mul_singleAt (u : QHat) (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    u * singleAt v x = singleAt v (u v * x) := by
  apply FiniteAdeleRing.ext
  intro w
  show u w * singleAt v x w = singleAt v (u v * x) w
  rw [singleAt_apply, singleAt_apply]
  by_cases h : w = v
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem singleAt_one_mem_ZHat (v : HeightOneSpectrum ℤ) : singleAt v 1 ∈ ZHat := by
  rw [mem_ZHat]
  intro w
  rw [singleAt_apply]
  by_cases h : w = v
  · subst h; rw [Pi.single_eq_same]; exact (w.adicCompletionIntegers ℚ).one_mem
  · rw [Pi.single_eq_of_ne h]; exact (w.adicCompletionIntegers ℚ).zero_mem

/-- **`ℤ̂^⊥ = ℤ̂`.** -/
theorem mem_ZHat_of_psi {u : QHat} (h : ∀ z ∈ ZHat, psi (u * z) = 0) : u ∈ ZHat := by
  rw [mem_ZHat]
  intro v
  have := h _ (singleAt_one_mem_ZHat v)
  rw [mul_singleAt, mul_one, psi_singleAt, frV_eq_zero_iff] at this
  exact this

/-- `p⁻¹` at `v` has nonzero fractional part. -/
theorem frV_inv_p_ne_zero (v : HeightOneSpectrum ℤ) :
    frV v (algebraMap ℚ (v.adicCompletion ℚ) ((primesEquiv v : ℕ) : ℚ)⁻¹) ≠ 0 := by
  rw [Ne, frV_eq_zero_iff, rat_mem_integers_iff]
  have : Fact ((primesEquiv v : ℕ).Prime) := ⟨(primesEquiv v).prop⟩
  push_cast
  rw [norm_inv, Padic.norm_p]
  simp only [inv_inv, not_le]
  exact_mod_cast (primesEquiv v).prop.one_lt

/-- **Nondegeneracy.** For `u ≠ 0` there is `v` with `ψ(u v) ≠ 0`. -/
theorem exists_psi_ne_zero {u : QHat} (hu : u ≠ 0) : ∃ v : QHat, psi (u * v) ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w, u w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (FiniteAdeleRing.ext _ h)
  refine ⟨singleAt w ((u w)⁻¹ * algebraMap ℚ (w.adicCompletion ℚ) ((primesEquiv w : ℕ) : ℚ)⁻¹), ?_⟩
  rw [mul_singleAt, ← mul_assoc, mul_inv_cancel₀ hw, one_mul, psi_singleAt]
  exact frV_inv_p_ne_zero w

end AdelicToriLean
