import AdelicToriLean.QHatSelfDual

/-!
# Characters of `ℚ̂ⁿ` and the double annihilator

* `prA u v = ψ(∑ uᵢ vᵢ)`, the symmetric pairing on `ℚ̂ⁿ`;
* `charN_surjective`: every continuous character of `ℚ̂ⁿ` is `x ↦ e(prA w x)`;
* `perp S`: the annihilator of `S ⊆ ℚ̂ⁿ`;
* `perp_perp_eq`: for a closed subgroup `C`, `C^⊥⊥ = C`.
-/

open IsDedekindDomain Topology

noncomputable section

namespace AdelicToriLean

variable {n : ℕ}

instance : T2Space (Multiplicative (Fin n → QHat)) := inferInstanceAs (T2Space (Fin n → QHat))
instance : LocallyCompactSpace (Multiplicative (Fin n → QHat)) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → QHat))

/-- `prA u v = ψ(∑ uᵢ vᵢ)`. -/
def prA (u v : Fin n → QHat) : AddCircle (1 : ℝ) := psi (∑ i, u i * v i)

theorem prA_comm (u v : Fin n → QHat) : prA u v = prA v u := by
  simp [prA, mul_comm]

theorem prA_add_left (u u' v : Fin n → QHat) : prA (u + u') v = prA u v + prA u' v := by
  simp [prA, add_mul, Finset.sum_add_distrib]

theorem prA_add_right (u v v' : Fin n → QHat) : prA u (v + v') = prA u v + prA u v' := by
  rw [prA_comm, prA_add_left, prA_comm, prA_comm v']

theorem prA_neg_right (u v : Fin n → QHat) : prA u (-v) = -prA u v := by
  simp [prA, Finset.sum_neg_distrib]

theorem prA_zero_right (u : Fin n → QHat) : prA u 0 = 0 := by simp [prA]

theorem continuous_prA (w : Fin n → QHat) : Continuous (prA w) :=
  continuous_psi.comp (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_apply i))

theorem toCircle_sum {ι : Type*} (s : Finset ι) (f : ι → AddCircle (1 : ℝ)) :
    AddCircle.toCircle (∑ i ∈ s, f i) = ∏ i ∈ s, AddCircle.toCircle (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddCircle.toCircle_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddCircle.toCircle_add, ih]

/-- The character `x ↦ e(prA w x)` of `ℚ̂ⁿ`. -/
def chiN (w : Fin n → QHat) : PontryaginDual (Multiplicative (Fin n → QHat)) :=
  ⟨{ toFun := fun x => AddCircle.toCircle (prA w (Multiplicative.toAdd x))
     map_one' := by simp [prA_zero_right]
     map_mul' := fun x y => by simp [prA_add_right, AddCircle.toCircle_add] },
    AddCircle.continuous_toCircle.comp ((continuous_prA w).comp continuous_toAdd)⟩

theorem chiN_apply (w : Fin n → QHat) (x : Multiplicative (Fin n → QHat)) :
    chiN w x = AddCircle.toCircle (prA w (Multiplicative.toAdd x)) := rfl

/-- **Characters of `ℚ̂ⁿ`.** -/
theorem charN_surjective : Function.Surjective (chiN (n := n)) := by
  classical
  intro χ
  -- restrict to each coordinate
  have hcoord : ∀ i, ∃ w : QHat, ∀ x : QHat,
      χ (Multiplicative.ofAdd (Pi.single i x)) = AddCircle.toCircle (psi (w * x)) := by
    intro i
    let χi : PontryaginDual (Multiplicative QHat) :=
      ⟨{ toFun := fun x => χ (Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd x)))
         map_one' := by simp
         map_mul' := fun x y => by
           simp only [toAdd_mul, Pi.single_add, ofAdd_add, map_mul] },
        χ.continuous.comp (continuous_ofAdd.comp
          ((continuous_single i).comp continuous_toAdd))⟩
    obtain ⟨w, hw⟩ := chi_surjective χi
    exact ⟨w, fun x => by
      have := congrArg (fun φ : PontryaginDual (Multiplicative QHat) =>
        φ (Multiplicative.ofAdd x)) hw
      exact this.symm⟩
  choose w hw using hcoord
  refine ⟨w, PontryaginDual.ext fun x => ?_⟩
  have hx : x = ∏ i, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd x i)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    simp only [toAdd_ofAdd]
    exact (Finset.univ_sum_single _).symm
  rw [chiN_apply]
  conv_rhs => rw [hx, map_prod]
  simp only [hw, prA]
  rw [map_sum, toCircle_sum]

/-- The annihilator of `S ⊆ ℚ̂ⁿ` for `prA`. -/
def perp (S : Set (Fin n → QHat)) : AddSubgroup (Fin n → QHat) where
  carrier := {v | ∀ u ∈ S, prA u v = 0}
  add_mem' hv hv' u hu := by rw [prA_add_right, hv u hu, hv' u hu, add_zero]
  zero_mem' u _ := prA_zero_right u
  neg_mem' hv u hu := by rw [prA_neg_right, hv u hu, neg_zero]

theorem mem_perp {S : Set (Fin n → QHat)} {v : Fin n → QHat} :
    v ∈ perp S ↔ ∀ u ∈ S, prA u v = 0 := ⟨fun h => h, fun h => h⟩

/-- **Double annihilator.** For a closed subgroup `C ⊆ ℚ̂ⁿ`, `C^⊥⊥ = C`. -/
theorem perp_perp_eq (C : AddSubgroup (Fin n → QHat)) (hC : IsClosed (C : Set (Fin n → QHat))) :
    (perp (perp (C : Set (Fin n → QHat)) : Set (Fin n → QHat)) : Set (Fin n → QHat)) = C := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxC
    -- separate `x` from `C` by a character of `ℚ̂ⁿ / C`
    let Cm : Subgroup (Multiplicative (Fin n → QHat)) := AddSubgroup.toSubgroup C
    have hCm : IsClosed (Cm : Set (Multiplicative (Fin n → QHat))) := hC
    have hne : (QuotientGroup.mk (Multiplicative.ofAdd x) :
        Multiplicative (Fin n → QHat) ⧸ Cm) ≠ 1 := by
      rw [Ne, QuotientGroup.eq_one_iff]; exact hxC
    have hinj := PontryaginDual.eval_injective (Multiplicative (Fin n → QHat) ⧸ Cm)
    obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual (Multiplicative (Fin n → QHat) ⧸ Cm),
        χ (QuotientGroup.mk (Multiplicative.ofAdd x)) ≠ 1 := by
      by_contra hall
      push Not at hall
      apply hne
      apply hinj
      rw [map_one]
      exact PontryaginDual.ext fun χ => by
        rw [PontryaginDual.eval_apply, hall χ, PontryaginDual.one_apply]
    let φ : PontryaginDual (Multiplicative (Fin n → QHat)) :=
      ⟨χ.toMonoidHom.comp (QuotientGroup.mk' Cm), χ.continuous.comp continuous_quot_mk⟩
    obtain ⟨w, hw⟩ := charN_surjective φ
    have hwC : w ∈ perp (C : Set (Fin n → QHat)) := by
      intro c hc
      have h1 : φ (Multiplicative.ofAdd c) = 1 := by
        show χ (QuotientGroup.mk (Multiplicative.ofAdd c)) = 1
        rw [(QuotientGroup.eq_one_iff _).mpr hc, map_one]
      rw [← hw, chiN_apply, ← AddCircle.toCircle_zero] at h1
      rw [prA_comm]
      exact AddCircle.injective_toCircle one_ne_zero h1
    apply hχ
    have h2 := hx w hwC
    show φ (Multiplicative.ofAdd x) = 1
    rw [← hw, chiN_apply, toAdd_ofAdd, h2, AddCircle.toCircle_zero]
  · intro c hc v hv
    rw [prA_comm]
    exact hv c hc

end AdelicToriLean
