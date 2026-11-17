import AdelicToriLean.DualityTools
import AdelicToriLean.Protorus
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# `ℝⁿ ≅ (ℝⁿ)^∨`

* `chiR_surjective`: every continuous character of `ℝ` is `x ↦ exp(i t x)`;
* `chiRn_surjective`: every continuous character of `ℝⁿ` is `x ↦ exp(i ∑ wⱼ xⱼ)`;
* `realSelfDual`: the topological isomorphism `ℝⁿ ≅ (ℝⁿ)^∨`.
-/

open Topology Real Circle

noncomputable section

namespace AdelicToriLean

/-- `x ↦ exp(i t x)`. -/
def chiR (t : ℝ) : PontryaginDual (Multiplicative ℝ) :=
  ⟨{ toFun := fun x => Circle.exp (t * Multiplicative.toAdd x)
     map_one' := by simp
     map_mul' := fun x y => by simp [mul_add, Circle.exp_add] },
    Circle.exp.continuous.comp (continuous_const.mul continuous_toAdd)⟩

theorem chiR_apply (t : ℝ) (x : Multiplicative ℝ) :
    chiR t x = Circle.exp (t * Multiplicative.toAdd x) := rfl

theorem continuous_chiR : Continuous chiR := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × Multiplicative ℝ =>
    Circle.exp (p.1 * Multiplicative.toAdd p.2))
  exact Circle.exp.continuous.comp (continuous_fst.mul (continuous_toAdd.comp continuous_snd))

/-- `chiR` as a homomorphism. -/
def chiRHom : Multiplicative ℝ →* PontryaginDual (Multiplicative ℝ) where
  toFun t := chiR (Multiplicative.toAdd t)
  map_one' := PontryaginDual.ext fun x => by simp [chiR_apply]
  map_mul' s t := PontryaginDual.ext fun x => by
    show Circle.exp ((Multiplicative.toAdd s + Multiplicative.toAdd t) * Multiplicative.toAdd x) =
      Circle.exp (Multiplicative.toAdd s * Multiplicative.toAdd x) *
        Circle.exp (Multiplicative.toAdd t * Multiplicative.toAdd x)
    rw [add_mul, Circle.exp_add]

theorem exp_half_pi_notMem (s : ℝ) (hs : |s| = π / 2) : Circle.exp s ∉ centeredArc (π / 2) := by
  rw [mem_centeredArc (by linarith [Real.pi_pos])]
  have h1 : -π < s := by
    have := neg_abs_le s; rw [hs] at this; linarith [Real.pi_pos]
  have h2 : s ≤ π := by
    have := le_abs_self s; rw [hs] at this; linarith [Real.pi_pos]
  rw [Circle.arg_exp h1 h2, hs]
  exact lt_irrefl _

/-- `[-1, 1]` in `Multiplicative ℝ`. -/
def unitIcc : Set (Multiplicative ℝ) := Multiplicative.ofAdd '' Set.Icc (-1 : ℝ) 1

theorem isCompact_unitIcc : IsCompact unitIcc := isCompact_Icc.image continuous_ofAdd

/-- Characters close to `1` on `[-1, 1]`. -/
def WR : Set (PontryaginDual (Multiplicative ℝ)) :=
  {χ | Set.MapsTo (ContinuousMonoidHom.toContinuousMap χ) unitIcc (centeredArc (π / 2))}

theorem isOpen_WR : IsOpen WR :=
  (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_unitIcc (isOpen_centeredArc (r := π / 2))).preimage
    (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous

theorem one_mem_WR : (1 : PontryaginDual (Multiplicative ℝ)) ∈ WR := by
  intro x _
  exact ⟨0, by simp [Real.pi_pos], by rw [Circle.exp_zero]; exact (PontryaginDual.one_apply x).symm⟩

theorem abs_le_of_mem_WR {t : ℝ} (h : chiR t ∈ WR) : |t| ≤ π / 2 := by
  by_contra hlt
  push Not at hlt
  have ht0 : 0 < |t| := lt_trans (by positivity) hlt
  set x := (π / 2) / |t|
  have hx1 : x ∈ Set.Icc (-1 : ℝ) 1 := by
    have : x ≤ 1 := by rw [div_le_one ht0]; exact hlt.le
    exact ⟨by have : 0 ≤ x := by positivity
              linarith, this⟩
  have hmem := h (show Multiplicative.ofAdd x ∈ unitIcc from ⟨x, hx1, rfl⟩)
  apply exp_half_pi_notMem (t * x) _ hmem
  rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < π / 2), abs_abs]
  field_simp

theorem isClosed_range_chiRHom :
    IsClosed ((chiRHom).range : Set (PontryaginDual (Multiplicative ℝ))) := by
  apply isClosed_of_compact_nhds _ ((isCompact_Icc (a := -(π / 2)) (b := π / 2)).image continuous_chiR)
  · rintro _ ⟨t, _, rfl⟩; exact ⟨Multiplicative.ofAdd t, rfl⟩
  · exact isOpen_WR
  · exact one_mem_WR
  · rintro _ ⟨⟨t, rfl⟩, hW⟩
    exact ⟨Multiplicative.toAdd t, abs_le.mp (abs_le_of_mem_WR hW), rfl⟩

/-- **Characters of `ℝ`.** -/
theorem chiR_surjective : Function.Surjective chiR := by
  have := surjective_of_isClosed_range chiRHom isClosed_range_chiRHom (by
    intro x hx
    refine ⟨Multiplicative.ofAdd (π / Multiplicative.toAdd x), ?_⟩
    have hx0 : Multiplicative.toAdd x ≠ 0 := hx
    show Circle.exp (π / Multiplicative.toAdd x * Multiplicative.toAdd x) ≠ 1
    rw [div_mul_cancel₀ _ hx0]
    intro h
    obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp h
    have : (1 : ℝ) = 2 * m := by
      have := Real.pi_pos
      field_simp at hm
      nlinarith
    have hm' : (1 : ℤ) = 2 * m := by exact_mod_cast this
    omega)
  intro χ
  obtain ⟨t, ht⟩ := this χ
  exact ⟨Multiplicative.toAdd t, ht⟩

variable {n : ℕ}

theorem exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    Circle.exp (∑ i ∈ s, f i) = ∏ i ∈ s, Circle.exp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, Circle.exp_add, ih]

/-- `x ↦ exp(i ∑ wⱼ xⱼ)` on `ℝⁿ`. -/
def chiRn : Multiplicative (Fin n → ℝ) →* PontryaginDual (Multiplicative (Fin n → ℝ)) where
  toFun w :=
    ⟨{ toFun := fun x => Circle.exp (∑ i, Multiplicative.toAdd w i * Multiplicative.toAdd x i)
       map_one' := by simp
       map_mul' := fun x y => by
         simp only [toAdd_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib, Circle.exp_add] },
      Circle.exp.continuous.comp (continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).comp continuous_toAdd))⟩
  map_one' := PontryaginDual.ext fun x => by
    show Circle.exp (∑ i, Multiplicative.toAdd (1 : Multiplicative (Fin n → ℝ)) i *
      Multiplicative.toAdd x i) = 1
    simp
  map_mul' w w' := PontryaginDual.ext fun x => by
    show Circle.exp (∑ i, (Multiplicative.toAdd w i + Multiplicative.toAdd w' i) *
      Multiplicative.toAdd x i) = Circle.exp (∑ i, Multiplicative.toAdd w i * Multiplicative.toAdd x i) *
      Circle.exp (∑ i, Multiplicative.toAdd w' i * Multiplicative.toAdd x i)
    rw [← Circle.exp_add, ← Finset.sum_add_distrib]
    simp only [add_mul]

theorem chiRn_apply (w x : Multiplicative (Fin n → ℝ)) :
    chiRn w x = Circle.exp (∑ i, Multiplicative.toAdd w i * Multiplicative.toAdd x i) := rfl

theorem continuous_chiRn : Continuous (chiRn (n := n)) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : Multiplicative (Fin n → ℝ) × Multiplicative (Fin n → ℝ) =>
    Circle.exp (∑ i, Multiplicative.toAdd p.1 i * Multiplicative.toAdd p.2 i))
  exact Circle.exp.continuous.comp (continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp (continuous_toAdd.comp continuous_fst)).mul
      ((continuous_apply i).comp (continuous_toAdd.comp continuous_snd)))

theorem chiRn_injective : Function.Injective (chiRn (n := n)) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, Multiplicative.toAdd w j ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Multiplicative.toAdd.injective (funext h))
  have := congrArg (fun χ : PontryaginDual (Multiplicative (Fin n → ℝ)) =>
    χ (Multiplicative.ofAdd (Pi.single j (π / Multiplicative.toAdd w j)))) hw
  simp only [chiRn_apply, PontryaginDual.one_apply, toAdd_ofAdd] at this
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, mul_zero]) (by simp),
    Pi.single_eq_same, mul_div_cancel₀ _ hj] at this
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp this
  have h1 : (1 : ℝ) = 2 * m := by
    have := Real.pi_pos
    field_simp at hm
    nlinarith
  have hm' : (1 : ℤ) = 2 * m := by exact_mod_cast h1
  omega

/-- **Characters of `ℝⁿ`.** -/
theorem chiRn_surjective : Function.Surjective (chiRn (n := n)) := by
  classical
  intro χ
  have hcoord : ∀ i, ∃ w : ℝ, ∀ x : ℝ,
      χ (Multiplicative.ofAdd (Pi.single i x)) = Circle.exp (w * x) := by
    intro i
    let χi : PontryaginDual (Multiplicative ℝ) :=
      ⟨{ toFun := fun x => χ (Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd x)))
         map_one' := by simp
         map_mul' := fun x y => by
           simp only [toAdd_mul, Pi.single_add, ofAdd_add, map_mul] },
        χ.continuous.comp (continuous_ofAdd.comp
          ((continuous_single i).comp continuous_toAdd))⟩
    obtain ⟨w, hw⟩ := chiR_surjective χi
    exact ⟨w, fun x => by
      have := congrArg (fun φ : PontryaginDual (Multiplicative ℝ) => φ (Multiplicative.ofAdd x)) hw
      exact this.symm⟩
  choose w hw using hcoord
  refine ⟨Multiplicative.ofAdd w, PontryaginDual.ext fun x => ?_⟩
  have hx : x = ∏ i, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd x i)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    simp only [toAdd_ofAdd]
    exact (Finset.univ_sum_single _).symm
  rw [chiRn_apply]
  conv_rhs => rw [hx, map_prod]
  simp only [hw, toAdd_ofAdd]
  rw [exp_sum]

/-- **`ℝⁿ ≅ (ℝⁿ)^∨`.** -/
def realSelfDual : Multiplicative (Fin n → ℝ) ≃ₜ* PontryaginDual (Multiplicative (Fin n → ℝ)) := by
  haveI : SigmaCompactSpace (Multiplicative (Fin n → ℝ)) :=
    inferInstanceAs (SigmaCompactSpace (Fin n → ℝ))
  haveI : LocallyCompactSpace (Multiplicative (Fin n → ℝ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → ℝ))
  haveI : BaireSpace (PontryaginDual (Multiplicative (Fin n → ℝ))) :=
    BaireSpace.of_t2Space_locallyCompactSpace
  have hbij : Function.Bijective (chiRn (n := n)) := ⟨chiRn_injective, chiRn_surjective⟩
  have hom : IsOpenMap (chiRn (n := n)) :=
    MonoidHom.isOpenMap_of_sigmaCompact _ hbij.2 continuous_chiRn
  let h := (Equiv.ofBijective _ hbij).toHomeomorphOfContinuousOpen continuous_chiRn hom
  exact { MulEquiv.ofBijective (chiRn (n := n)) hbij with
    continuous_toFun := continuous_chiRn
    continuous_invFun := h.symm.continuous }

end AdelicToriLean
