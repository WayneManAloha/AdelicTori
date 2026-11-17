import AdelicToriLean.AdelicPairing

/-!
# The annihilator of a lattice `ℤⁿ ⊆ S ⊆ ℚⁿ` in `𝔸ⁿ`

Let `S ⊆ ℚⁿ` contain the standard basis vectors. In the paper's proof of
Theorem `fdccg-adelic-tori`, the annihilator of `S` in `𝔸ⁿ` is `C + Λ̃`, where
`Λ̃ = {(q, q)}` is the diagonal and `C ⊆ ℤ̂ⁿ` is the annihilator of `S` in the finite part.

* `annC S`: `C = {u ∈ ℤ̂ⁿ | ∑_i ψ(b_i u_i) = 0 for all b ∈ S}`;
* `pairing_finPart`: on `(u, 0)` the pairing is `∑_i ψ(b_i u_i)`;
* `annihilator_eq`: `⟪a, b⟫ = 0` for all `b ∈ S` iff `a = (u, 0) + diag r` with `u ∈ C`, `r ∈ ℚⁿ`.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

noncomputable section

namespace AdelicToriLean

variable {n : ℕ}

/-- `(u, 0) ∈ 𝔸ⁿ` for `u ∈ ℚ̂ⁿ`. -/
def finPart : (Fin n → QHat) →+ An n where
  toFun u i := (u i, 0)
  map_zero' := by ext i <;> simp
  map_add' u v := by ext i <;> simp

theorem finPart_apply (u : Fin n → QHat) (i : Fin n) : finPart u i = (u i, 0) := rfl

theorem pairing_finPart (b : Fin n → ℚ) (u : Fin n → QHat) :
    pairing b (finPart u) = ∑ i, finChar (b i) (u i) := by
  rw [pairing_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finPart_apply, pair1_apply]
  simp [realChar]

/-- **The profinite group `C`**: the annihilator of `S` in `ℤ̂ⁿ`. -/
def annC (S : Set (Fin n → ℚ)) : AddSubgroup (Fin n → QHat) where
  carrier := {u | (∀ i, u i ∈ ZHat) ∧ ∀ b ∈ S, ∑ i, finChar (b i) (u i) = 0}
  add_mem' {u v} hu hv := ⟨fun i => ZHat.add_mem (hu.1 i) (hv.1 i), fun b hb => by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib, hu.2 b hb, hv.2 b hb, add_zero]⟩
  zero_mem' := ⟨fun i => ZHat.zero_mem, fun b _ => by simp⟩
  neg_mem' {u} hu := ⟨fun i => ZHat.neg_mem (hu.1 i), fun b hb => by
    simp only [Pi.neg_apply, map_neg, Finset.sum_neg_distrib, hu.2 b hb, neg_zero]⟩

theorem mem_annC {S : Set (Fin n → ℚ)} {u : Fin n → QHat} :
    u ∈ annC S ↔ (∀ i, u i ∈ ZHat) ∧ ∀ b ∈ S, ∑ i, finChar (b i) (u i) = 0 :=
  ⟨fun h => h, fun h => h⟩

/-- `ψ` vanishes on `ℤ̂`. -/
theorem psi_ZHat {z : QHat} (hz : z ∈ ZHat) : psi z = 0 :=
  psi_eq_zero_of_integral (mem_ZHat.mp hz)

/-- Integers are integral adeles. -/
theorem algebraMap_int_mem_ZHat (m : ℤ) : algebraMap ℚ QHat (m : ℚ) ∈ ZHat := by
  rw [mem_ZHat]
  intro v
  rw [show (algebraMap ℚ QHat (m : ℚ)) v = algebraMap ℚ (v.adicCompletion ℚ) (m : ℚ) from rfl,
    rat_mem_integers_iff]
  push_cast
  exact Padic.norm_int_le_one m

theorem finChar_one (u : QHat) : finChar 1 u = psi u := by simp [finChar]

theorem finChar_zero (u : QHat) : finChar 0 u = 0 := by simp [finChar]

theorem pair1_zero (a : Adele) : pair1 0 a = 0 := by
  rw [pair1_apply, finChar_zero]; simp [realChar]

/-- The pairing with a standard basis vector reads one coordinate. -/
theorem pairing_single (j : Fin n) (a : An n) : pairing (Pi.single j 1) a = pair1 1 (a j) := by
  rw [pairing_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij; rw [Pi.single_eq_of_ne hij, pair1_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **Annihilator of a lattice containing `ℤⁿ`.** If `S ⊆ ℚⁿ` contains the standard basis, then
`a ∈ 𝔸ⁿ` pairs to zero with all of `S` iff `a = (u, 0) + diag r` with `u ∈ C(S)` and `r ∈ ℚⁿ`. -/
theorem annihilator_eq {S : Set (Fin n → ℚ)} (hS : ∀ j, Pi.single j 1 ∈ S) (a : An n) :
    (∀ b ∈ S, pairing b a = 0) ↔ ∃ u ∈ annC S, ∃ r : Fin n → ℚ, a = finPart u + diag r := by
  constructor
  · intro ha
    -- strong approximation in each coordinate
    have hsa : ∀ i, ∃ r : ℚ, ∃ z ∈ ZHat, (a i).1 = algebraMap ℚ QHat r + z :=
      fun i => exists_rat_add_ZHat (a i).1
    choose r z hz hrz using hsa
    -- the real parts after subtracting `r` are integers
    have hint : ∀ j, ∃ m : ℤ, (a j).2 - (r j : ℝ) = m := by
      intro j
      have h := ha _ (hS j)
      rw [pairing_single, pair1_apply, finChar_one, hrz j, map_add, psi_algebraMap,
        psi_ZHat (hz j), add_zero] at h
      simp only [realChar, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
        QuotientAddGroup.mk'_apply, Rat.cast_one, one_mul] at h
      rw [← AddCircle.coe_sub] at h
      obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
      exact ⟨-m, by rw [zsmul_one] at hm; push_cast; linarith⟩
    choose m hm using hint
    set r' : Fin n → ℚ := fun i => r i + m i
    set u : Fin n → QHat := fun i => z i - algebraMap ℚ QHat (m i : ℚ)
    have hdecomp : a = finPart u + diag r' := by
      funext i
      refine Prod.ext ?_ ?_
      · show (a i).1 = u i + algebraMap ℚ QHat (r' i)
        simp only [u, r', map_add, hrz i]; ring
      · show (a i).2 = 0 + ((r' i : ℚ) : ℝ)
        simp only [r', zero_add]; push_cast; linarith [hm i]
    refine ⟨u, ⟨fun i => ZHat.sub_mem (hz i) (algebraMap_int_mem_ZHat (m i)), fun b hb => ?_⟩,
      r', hdecomp⟩
    have := ha b hb
    rw [hdecomp, map_add, pairing_diag, add_zero, pairing_finPart] at this
    exact this
  · rintro ⟨u, hu, r, rfl⟩ b hb
    rw [map_add, pairing_diag, add_zero, pairing_finPart]
    exact (mem_annC.mp hu).2 b hb

end AdelicToriLean
