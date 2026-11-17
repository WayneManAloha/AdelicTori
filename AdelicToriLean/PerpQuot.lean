import AdelicToriLean.QHatnDual
import AdelicToriLean.DualityTools
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Self-duality of `C^⊥ / C`

For a closed isotropic subgroup `C ⊆ ℚ̂ⁿ` (`C ⊆ C^⊥`) whose annihilator `C^⊥` is open, the pairing
`([w], [h]) ↦ e(ψ(∑ wᵢ hᵢ))` identifies `C^⊥ / C` with its Pontryagin dual (`perpQuotEquiv`).
-/

open IsDedekindDomain Topology

noncomputable section

namespace AdelicToriLean

variable {n : ℕ}

theorem continuous_prA2 : Continuous fun p : (Fin n → QHat) × (Fin n → QHat) => prA p.1 p.2 :=
  continuous_psi.comp (continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd))

theorem prA_neg_left (u v : Fin n → QHat) : prA (-u) v = -prA u v := by
  rw [prA_comm, prA_neg_right, prA_comm]

theorem toCircle_surjective : Function.Surjective (AddCircle.toCircle (T := (1 : ℝ))) := by
  intro z
  obtain ⟨x, hx⟩ := (AddCircle.homeomorphCircle (one_ne_zero (α := ℝ))).surjective z
  exact ⟨x, by rw [← AddCircle.homeomorphCircle_apply one_ne_zero, hx]⟩

theorem toCircle_eq_one_iff (x : AddCircle (1 : ℝ)) : AddCircle.toCircle x = 1 ↔ x = 0 := by
  rw [← AddCircle.toCircle_zero]
  exact (AddCircle.injective_toCircle one_ne_zero).eq_iff

instance : SigmaCompactSpace QHat := by
  rw [← isSigmaCompact_univ_iff]
  have : (Set.univ : Set QHat) = ⋃ r : ℚ, (fun z => algebraMap ℚ QHat r + z) '' (ZHat : Set QHat) := by
    ext a
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    obtain ⟨r, z, hz, rfl⟩ := exists_rat_add_ZHat a
    exact ⟨r, z, hz, rfl⟩
  rw [this]
  exact isSigmaCompact_iUnion_of_isCompact _ fun r =>
    isCompact_ZHat.image (continuous_const.add continuous_id)

section

variable (C : AddSubgroup (Fin n → QHat))

/-- `C^⊥` as an additive subgroup. -/
abbrev Hp : AddSubgroup (Fin n → QHat) := perp (C : Set (Fin n → QHat))

/-- `C` inside `C^⊥`. -/
abbrev Cp : AddSubgroup (Hp C) := C.addSubgroupOf (Hp C)

/-- `C^⊥ / C`. -/
abbrev PQ := Hp C ⧸ Cp C

theorem prA_wd (a a' b b' : Hp C) (ha : -a + a' ∈ Cp C) (hb : -b + b' ∈ Cp C) :
    prA (a : Fin n → QHat) b = prA (a' : Fin n → QHat) b' := by
  rw [AddSubgroup.mem_addSubgroupOf] at ha hb
  have ea : (a' : Fin n → QHat) = a + ((-a + a' : Hp C) : Fin n → QHat) := by simp
  have eb : (b' : Fin n → QHat) = b + ((-b + b' : Hp C) : Fin n → QHat) := by simp
  rw [ea, eb, prA_add_left, prA_add_right, prA_add_right]
  have h1 : prA ((-a + a' : Hp C) : Fin n → QHat) (b : Fin n → QHat) = 0 := b.2 _ ha
  have h2 : prA ((-a + a' : Hp C) : Fin n → QHat) ((-b + b' : Hp C) : Fin n → QHat) = 0 :=
    (-b + b').2 _ ha
  have h3 : prA (a : Fin n → QHat) ((-b + b' : Hp C) : Fin n → QHat) = 0 := by
    rw [prA_comm]; exact a.2 _ hb
  rw [h1, h2, h3]; simp

/-- The pairing on `C^⊥ / C`. -/
def pq (x y : PQ C) : AddCircle (1 : ℝ) :=
  Quotient.liftOn₂' x y (fun a b => prA (a : Fin n → QHat) b) fun a b a' b' ha hb => by
    apply prA_wd
    · exact QuotientAddGroup.leftRel_apply.mp ha
    · exact QuotientAddGroup.leftRel_apply.mp hb

theorem pq_mk (a b : Hp C) :
    pq C (QuotientAddGroup.mk a) (QuotientAddGroup.mk b) = prA (a : Fin n → QHat) b := rfl

theorem pq_add_left (x x' y : PQ C) : pq C (x + x') y = pq C x y + pq C x' y := by
  induction x using QuotientAddGroup.induction_on
  induction x' using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  rw [← QuotientAddGroup.mk_add, pq_mk, pq_mk, pq_mk, AddSubgroup.coe_add, prA_add_left]

theorem pq_add_right (x y y' : PQ C) : pq C x (y + y') = pq C x y + pq C x y' := by
  induction x using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  induction y' using QuotientAddGroup.induction_on
  rw [← QuotientAddGroup.mk_add, pq_mk, pq_mk, pq_mk, AddSubgroup.coe_add, prA_add_right]

theorem pq_zero_right (x : PQ C) : pq C x 0 = 0 := by
  have := pq_add_right C x 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem pq_zero_left (y : PQ C) : pq C 0 y = 0 := by
  have := pq_add_left C 0 0 y
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem continuous_pq : Continuous fun p : PQ C × PQ C => pq C p.1 p.2 := by
  rw [← (QuotientAddGroup.isOpenQuotientMap_mk.prodMap
    QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff]
  have h : Continuous (Prod.map (Subtype.val : Hp C → Fin n → QHat) (Subtype.val : Hp C → _)) :=
    continuous_subtype_val.prodMap continuous_subtype_val
  refine (continuous_prA2.comp h).congr fun p => ?_
  exact (pq_mk C p.1 p.2).symm

/-- The self-duality map `C^⊥ / C → (C^⊥ / C)^∨`. -/
def thetaPQ : Multiplicative (PQ C) →* PontryaginDual (Multiplicative (PQ C)) where
  toFun x :=
    ⟨{ toFun := fun y => AddCircle.toCircle (pq C (Multiplicative.toAdd x) (Multiplicative.toAdd y))
       map_one' := by simp [pq_zero_right]
       map_mul' := fun y y' => by
         simp only [toAdd_mul, pq_add_right, AddCircle.toCircle_add] },
      AddCircle.continuous_toCircle.comp ((continuous_pq C).comp
        (continuous_const.prodMk continuous_toAdd))⟩
  map_one' := PontryaginDual.ext fun y => by
    show AddCircle.toCircle (pq C 0 (Multiplicative.toAdd y)) = 1
    rw [pq_zero_left, AddCircle.toCircle_zero]
  map_mul' x x' := PontryaginDual.ext fun y => by
    show AddCircle.toCircle (pq C (Multiplicative.toAdd x + Multiplicative.toAdd x')
      (Multiplicative.toAdd y)) = AddCircle.toCircle (pq C (Multiplicative.toAdd x)
      (Multiplicative.toAdd y)) * AddCircle.toCircle (pq C (Multiplicative.toAdd x')
      (Multiplicative.toAdd y))
    rw [pq_add_left, AddCircle.toCircle_add]

theorem thetaPQ_apply (x y : Multiplicative (PQ C)) :
    thetaPQ C x y = AddCircle.toCircle (pq C (Multiplicative.toAdd x) (Multiplicative.toAdd y)) :=
  rfl

theorem continuous_thetaPQ : Continuous (thetaPQ C) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : Multiplicative (PQ C) × Multiplicative (PQ C) =>
    AddCircle.toCircle (pq C (Multiplicative.toAdd p.1) (Multiplicative.toAdd p.2)))
  exact AddCircle.continuous_toCircle.comp ((continuous_pq C).comp
    ((continuous_toAdd.comp continuous_fst).prodMk (continuous_toAdd.comp continuous_snd)))

variable (hC : IsClosed (C : Set (Fin n → QHat)))
include hC

theorem thetaPQ_injective : Function.Injective (thetaPQ C) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using Multiplicative.rec with | ofAdd x => ?_
  induction x using QuotientAddGroup.induction_on with | H w => ?_
  have hw : ∀ h ∈ Hp C, prA (w : Fin n → QHat) h = 0 := by
    intro h hh
    have := congrArg (fun φ : PontryaginDual (Multiplicative (PQ C)) =>
      φ (Multiplicative.ofAdd (QuotientAddGroup.mk ⟨h, hh⟩))) hx
    simp only [thetaPQ_apply, toAdd_ofAdd, pq_mk, PontryaginDual.one_apply] at this
    exact (toCircle_eq_one_iff _).mp this
  have hwC : (w : Fin n → QHat) ∈ C := by
    rw [← SetLike.mem_coe, ← perp_perp_eq C hC]
    intro h hh
    rw [prA_comm]
    exact hw h hh
  show Multiplicative.ofAdd (QuotientAddGroup.mk w : PQ C) = 1
  rw [ofAdd_eq_one, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact hwC

omit hC in
theorem thetaPQ_surjective (hiso : C ≤ Hp C) (hopen : IsOpen (Hp C : Set (Fin n → QHat))) :
    Function.Surjective (thetaPQ C) := by
  intro χ
  let e := AddCircle.homeomorphCircle (one_ne_zero (α := ℝ))
  have he : ∀ x, e x = AddCircle.toCircle x := AddCircle.homeomorphCircle_apply one_ne_zero
  let f : Hp C → AddCircle (1 : ℝ) := fun h =>
    e.symm (χ (Multiplicative.ofAdd (QuotientAddGroup.mk h)))
  have hf : ∀ h, AddCircle.toCircle (f h) = χ (Multiplicative.ofAdd (QuotientAddGroup.mk h)) := by
    intro h; rw [← he]; exact e.apply_symm_apply _
  let φ0 : Hp C →+ AddCircle (1 : ℝ) :=
    { toFun := f
      map_zero' := by
        apply AddCircle.injective_toCircle one_ne_zero
        rw [hf, AddCircle.toCircle_zero, QuotientAddGroup.mk_zero, ofAdd_zero, map_one]
      map_add' := fun a b => by
        apply AddCircle.injective_toCircle one_ne_zero
        rw [AddCircle.toCircle_add, hf, hf, hf, QuotientAddGroup.mk_add, ofAdd_add, map_mul] }
  obtain ⟨Φ, hΦ⟩ := extend_char (Hp C) φ0
  have hΦc : Continuous Φ := by
    apply continuous_of_open_subgroup (Hp C) hopen Φ
    have : (fun h : Hp C => Φ h) = f := funext hΦ
    rw [this]
    exact e.symm.continuous.comp (χ.continuous.comp (continuous_ofAdd.comp continuous_quot_mk))
  let ξ : PontryaginDual (Multiplicative (Fin n → QHat)) :=
    ⟨{ toFun := fun x => AddCircle.toCircle (Φ (Multiplicative.toAdd x))
       map_one' := by simp
       map_mul' := fun x y => by simp [AddCircle.toCircle_add] },
      AddCircle.continuous_toCircle.comp (hΦc.comp continuous_toAdd)⟩
  obtain ⟨w, hw⟩ := charN_surjective ξ
  have hwx : ∀ x : Fin n → QHat, prA w x = Φ x := by
    intro x
    have := congrArg (fun φ : PontryaginDual (Multiplicative (Fin n → QHat)) =>
      φ (Multiplicative.ofAdd x)) hw
    exact AddCircle.injective_toCircle one_ne_zero this
  have hwH : w ∈ Hp C := by
    intro c hc
    rw [prA_comm, hwx, hΦ ⟨c, hiso hc⟩]
    apply AddCircle.injective_toCircle one_ne_zero
    show AddCircle.toCircle (f ⟨c, hiso hc⟩) = AddCircle.toCircle 0
    rw [hf, AddCircle.toCircle_zero]
    have : (QuotientAddGroup.mk ⟨c, hiso hc⟩ : PQ C) = 0 := by
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]; exact hc
    rw [this, ofAdd_zero, map_one]
  refine ⟨Multiplicative.ofAdd (QuotientAddGroup.mk ⟨w, hwH⟩), PontryaginDual.ext fun y => ?_⟩
  induction y using Multiplicative.rec with | ofAdd y => ?_
  induction y using QuotientAddGroup.induction_on with | H h => ?_
  rw [thetaPQ_apply, toAdd_ofAdd, toAdd_ofAdd, pq_mk, hwx, hΦ h]
  exact hf h

/-- **`C^⊥ / C` is Pontryagin self-dual.** -/
def perpQuotEquiv (hiso : C ≤ Hp C) (hopen : IsOpen (Hp C : Set (Fin n → QHat))) :
    Multiplicative (PQ C) ≃ₜ* PontryaginDual (Multiplicative (PQ C)) := by
  have hHc : IsClosed (Hp C : Set (Fin n → QHat)) := AddSubgroup.isClosed_of_isOpen _ hopen
  haveI : LocallyCompactSpace (Hp C) := hopen.locallyCompactSpace
  haveI : SigmaCompactSpace (Hp C) := hHc.sigmaCompactSpace
  haveI : IsClosed (Cp C : Set (Hp C)) := hC.preimage continuous_subtype_val
  haveI : SigmaCompactSpace (PQ C) := by
    rw [← isSigmaCompact_univ_iff, ← (QuotientAddGroup.mk_surjective (s := Cp C)).range_eq]
    exact isSigmaCompact_range continuous_quot_mk
  haveI : SigmaCompactSpace (Multiplicative (PQ C)) := inferInstanceAs (SigmaCompactSpace (PQ C))
  haveI : LocallyCompactSpace (Multiplicative (PQ C)) :=
    inferInstanceAs (LocallyCompactSpace (PQ C))
  haveI : T2Space (Multiplicative (PQ C)) := inferInstanceAs (T2Space (PQ C))
  haveI : LocallyCompactSpace (PontryaginDual (Multiplicative (PQ C))) := inferInstance
  haveI : T2Space (PontryaginDual (Multiplicative (PQ C))) := inferInstance
  haveI : BaireSpace (PontryaginDual (Multiplicative (PQ C))) :=
    BaireSpace.of_t2Space_locallyCompactSpace
  have hbij : Function.Bijective (thetaPQ C) :=
    ⟨thetaPQ_injective C hC, thetaPQ_surjective C hiso hopen⟩
  have hom : IsOpenMap (thetaPQ C) :=
    MonoidHom.isOpenMap_of_sigmaCompact _ hbij.2 (continuous_thetaPQ C)
  let h := (Equiv.ofBijective _ hbij).toHomeomorphOfContinuousOpen (continuous_thetaPQ C) hom
  exact { MulEquiv.ofBijective (thetaPQ C) hbij with
    continuous_toFun := (continuous_thetaPQ C)
    continuous_invFun := h.symm.continuous }

theorem perpQuotEquiv_apply (hiso : C ≤ Hp C) (hopen : IsOpen (Hp C : Set (Fin n → QHat)))
    (a b : Hp C) :
    perpQuotEquiv C hC hiso hopen (Multiplicative.ofAdd (QuotientAddGroup.mk a))
      (Multiplicative.ofAdd (QuotientAddGroup.mk b)) =
      AddCircle.toCircle (prA (a : Fin n → QHat) b) := rfl

end

end AdelicToriLean
