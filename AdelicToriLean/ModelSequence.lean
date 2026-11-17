import AdelicToriLean.ModelLattice

/-!
# The exact sequence `0 → D → L × ℝⁿ → (𝔸ⁿ / C) / Λ → 0`

For `ι : D → ℚⁿ` injective with `ℤⁿ ⊆ ι(D)`, `L = C^⊥ / C`:

* `jMap d = ([ι d], ι d)`, `FMap ([h], x) = [(h, x)]`;
* `FMap_comp_jMap`, `jMap_injective`, `FMap_surjective`, `ker_FMap` (exactness);
* `continuous_jMap`, `continuous_FMap`.
-/

open IsDedekindDomain Topology

noncomputable section

namespace AdelicToriLean

variable {n : ℕ} {D : Type*} [CommGroup D] (ι : Additive D →+ (Fin n → ℚ))

/-- `ℚⁿ → ℝⁿ`. -/
def ratReal : (Fin n → ℚ) →+ (Fin n → ℝ) where
  toFun r i := (r i : ℝ)
  map_zero' := by ext1 i; simp
  map_add' r s := by ext1 i; simp

theorem ratReal_injective : Function.Injective (ratReal (n := n)) := by
  intro r s h
  funext i
  have : ((r i : ℚ) : ℝ) = s i := congrFun h i
  exact_mod_cast this

/-- `𝔸ⁿ → (𝔸ⁿ / C) / Λ`. -/
def toT : An n →+ AdelicTorus ι := (QuotientAddGroup.mk' (Lam ι)).comp (QuotientAddGroup.mk' (Cadd ι))

theorem continuous_toT : Continuous (toT ι) := continuous_quot_mk.comp continuous_quot_mk

/-- `(h, x) ↦ (hᵢ, xᵢ)ᵢ`. -/
def pairUp : (Fin n → QHat) × (Fin n → ℝ) →+ An n where
  toFun p i := (p.1 i, p.2 i)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_pairUp : Continuous (pairUp (n := n)) :=
  continuous_pi fun i => ((continuous_apply i).comp continuous_fst).prodMk
    ((continuous_apply i).comp continuous_snd)

theorem toT_eq_zero_iff (a : An n) : toT ι a = 0 ↔ ∃ r : Fin n → ℚ, a - diag r ∈ Cadd ι := by
  constructor
  · intro h
    have h' : (QuotientAddGroup.mk a : An n ⧸ Cadd ι) ∈ Lam ι :=
      (QuotientAddGroup.eq_zero_iff _).mp h
    obtain ⟨_, ⟨r, rfl⟩, hr⟩ := AddSubgroup.mem_map.mp h'
    refine ⟨r, ?_⟩
    have := (QuotientAddGroup.eq).mp hr
    rwa [sub_eq_add_neg, add_comm]
  · rintro ⟨r, hr⟩
    show QuotientAddGroup.mk (QuotientAddGroup.mk a : An n ⧸ Cadd ι) = (0 : AdelicTorus ι)
    rw [QuotientAddGroup.eq_zero_iff]
    refine AddSubgroup.mem_map.mpr ⟨diag r, ⟨r, rfl⟩, ?_⟩
    show (QuotientAddGroup.mk (diag r) : An n ⧸ Cadd ι) = QuotientAddGroup.mk a
    rw [QuotientAddGroup.eq]
    rwa [sub_eq_add_neg, add_comm] at hr

theorem pairUp_emb (r : Fin n → ℚ) : pairUp (emb r, ratReal r) = diag r := by
  funext i; rfl

theorem pairUp_fin (c : Fin n → QHat) : pairUp (c, 0) = finPart c := by
  funext i; rfl

theorem toT_pairUp_C {c : Fin n → QHat} (hc : c ∈ Cm ι) : toT ι (pairUp (c, 0)) = 0 := by
  rw [toT_eq_zero_iff]
  refine ⟨0, ?_⟩
  rw [map_zero, sub_zero, pairUp_fin]
  exact AddSubgroup.mem_map.mpr ⟨c, hc, rfl⟩

/-- The map `C^⊥ × ℝⁿ → (𝔸ⁿ / C) / Λ`. -/
def F0 : Hp (Cm ι) × (Fin n → ℝ) →+ AdelicTorus ι :=
  ((toT ι).comp pairUp).comp ((Hp (Cm ι)).subtype.prodMap (AddMonoidHom.id _))

theorem F0_apply (h : Hp (Cm ι)) (x : Fin n → ℝ) :
    F0 ι (h, x) = toT ι (pairUp ((h : Fin n → QHat), x)) := rfl

/-- `[h] ↦ [(h, 0)]` on `L`. -/
def F1 : ModelL ι →+ AdelicTorus ι :=
  QuotientAddGroup.lift (Cp (Cm ι)) ((F0 ι).comp (AddMonoidHom.inl _ _)) (by
      intro c hc
      have hc' : (c : Fin n → QHat) ∈ Cm ι := AddSubgroup.mem_addSubgroupOf.mp hc
      show F0 ι (c, 0) = 0
      rw [F0_apply]; exact toT_pairUp_C ι hc')

theorem F1_mk (h : Hp (Cm ι)) : F1 ι (QuotientAddGroup.mk h) = F0 ι (h, 0) := rfl

/-- `F([h], x) = [(h, x)]` on `L × ℝⁿ`. -/
def FMap : ModelL ι × (Fin n → ℝ) →+ AdelicTorus ι where
  toFun p := F1 ι p.1 + F0 ι (0, p.2)
  map_zero' := by
    show F1 ι 0 + F0 ι (0, 0) = 0
    rw [map_zero, show ((0 : Hp (Cm ι)), (0 : Fin n → ℝ)) = 0 from rfl, map_zero]
    exact add_zero (0 : AdelicTorus ι)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    rw [show ((0 : Hp (Cm ι)), p.2 + q.2) = ((0 : Hp (Cm ι)), p.2) + (0, q.2) by simp, map_add]
    abel

theorem FMap_mk (h : Hp (Cm ι)) (x : Fin n → ℝ) :
    FMap ι (QuotientAddGroup.mk h, x) = toT ι (pairUp ((h : Fin n → QHat), x)) := by
  show F1 ι (QuotientAddGroup.mk h) + F0 ι (0, x) = _
  rw [F1_mk, ← map_add]
  simp [F0_apply]

theorem continuous_FMap : Continuous (FMap ι) := by
  have h1 : Continuous (F1 ι) := by
    rw [(QuotientAddGroup.isOpenQuotientMap_mk (N := Cp (Cm ι))).isQuotientMap.continuous_iff]
    exact (continuous_toT ι).comp (continuous_pairUp.comp
      ((continuous_subtype_val).prodMk continuous_const))
  have h2 : Continuous fun x : Fin n → ℝ => F0 ι (0, x) :=
    (continuous_toT ι).comp (continuous_pairUp.comp (continuous_const.prodMk continuous_id))
  exact (h1.comp continuous_fst).add (h2.comp continuous_snd)

variable (hZ : ∀ j : Fin n, Pi.single j 1 ∈ Set.range ι)
include hZ

/-- `ι d` as an element of `C^⊥`. -/
def embH : Additive D →+ Hp (Cm ι) :=
  AddMonoidHom.codRestrict (emb.comp ι) (Hp (Cm ι)) fun d =>
    (rat_mem_perp_iff ι hZ (ι d)).mpr ⟨d, rfl⟩

/-- `j d = ([ι d], ι d)`. -/
def jMap : Additive D →+ ModelL ι × (Fin n → ℝ) :=
  ((QuotientAddGroup.mk' (Cp (Cm ι))).comp (embH ι hZ)).prod (ratReal.comp ι)

theorem FMap_comp_jMap (d : Additive D) : FMap ι (jMap ι hZ d) = 0 := by
  show FMap ι (QuotientAddGroup.mk (embH ι hZ d), ratReal (ι d)) = 0
  rw [FMap_mk]
  show toT ι (pairUp (emb (ι d), ratReal (ι d))) = 0
  rw [pairUp_emb, toT_eq_zero_iff]
  exact ⟨ι d, by rw [sub_self]; exact (Cadd ι).zero_mem⟩

omit hZ in
theorem FMap_surjective : Function.Surjective (FMap ι) := by
  intro y
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
  have hsa : ∀ i, ∃ r : ℚ, ∃ z ∈ ZHat, (a i).1 = algebraMap ℚ QHat r + z :=
    fun i => exists_rat_add_ZHat (a i).1
  choose r z hz hrz using hsa
  have hzH : z ∈ Hp (Cm ι) := ZHatn_le_perp ι (mem_ZHatn.mpr hz)
  refine ⟨(QuotientAddGroup.mk ⟨z, hzH⟩, fun i => (a i).2 - (r i : ℝ)), ?_⟩
  rw [FMap_mk]
  show toT ι (pairUp (z, fun i => (a i).2 - (r i : ℝ))) = toT ι a
  have key : toT ι (pairUp (z, fun i => (a i).2 - (r i : ℝ)) - a) = 0 := by
    rw [toT_eq_zero_iff]
    refine ⟨-r, ?_⟩
    have : pairUp (z, fun i => (a i).2 - (r i : ℝ)) - a - diag (-r) = 0 := by
      funext i
      simp only [Pi.sub_apply, map_neg, Pi.neg_apply, diag_apply, Pi.zero_apply]
      rw [show pairUp (z, fun i => (a i).2 - (r i : ℝ)) i = (z i, (a i).2 - (r i : ℝ)) from rfl]
      ext
      · simp [hrz i]
      · simp
    rw [this]; exact (Cadd ι).zero_mem
  rw [show pairUp (z, fun i => (a i).2 - (r i : ℝ)) =
    a + (pairUp (z, fun i => (a i).2 - (r i : ℝ)) - a) by abel, map_add, key]
  exact add_zero (toT ι a)

theorem ker_FMap (p : ModelL ι × (Fin n → ℝ)) (hp : FMap ι p = 0) :
    ∃ d, jMap ι hZ d = p := by
  obtain ⟨x, y⟩ := p
  obtain ⟨h, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [FMap_mk, toT_eq_zero_iff] at hp
  obtain ⟨r, hr⟩ := hp
  obtain ⟨c, hc, hce⟩ := AddSubgroup.mem_map.mp hr
  have hcoord : ∀ i, c i = (h : Fin n → QHat) i - algebraMap ℚ QHat (r i) ∧
      0 = y i - (r i : ℝ) := by
    intro i
    have := congrFun hce i
    rw [finPart_apply] at this
    simp only [Pi.sub_apply, diag_apply] at this
    rw [show pairUp ((h : Fin n → QHat), y) i = ((h : Fin n → QHat) i, y i) from rfl] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hrH : emb r ∈ Hp (Cm ι) := by
    have : emb r = (h : Fin n → QHat) - c := by
      funext i; rw [emb_apply, Pi.sub_apply, (hcoord i).1]; abel
    rw [this]; exact sub_mem h.2 (Cm_le_perp ι hc)
  obtain ⟨d, hd⟩ := (rat_mem_perp_iff ι hZ r).mp hrH
  refine ⟨d, ?_⟩
  show (QuotientAddGroup.mk (embH ι hZ d), ratReal (ι d)) = (QuotientAddGroup.mk h, y)
  refine Prod.ext ?_ ?_
  · show (QuotientAddGroup.mk (embH ι hZ d) : ModelL ι) = QuotientAddGroup.mk h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have : ((-embH ι hZ d + h : Hp (Cm ι)) : Fin n → QHat) = c := by
      funext i
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
      rw [(hcoord i).1, show ((embH ι hZ d : Hp (Cm ι)) : Fin n → QHat) i =
        algebraMap ℚ QHat (r i) by rw [← hd]; rfl]
      abel
    rw [this]; exact hc
  · funext i
    show ((ι d i : ℚ) : ℝ) = y i
    rw [hd]; linarith [(hcoord i).2]

theorem jMap_injective (hι : Function.Injective ι) : Function.Injective (jMap ι hZ) := by
  intro d e h
  exact hι (ratReal_injective (congrArg Prod.snd h))

end AdelicToriLean
