import AdelicToriLean.FiniteAdeleChar
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# `ℤ̂` and strong approximation in `ℚ̂`

* `ZHat`: the integral finite adeles `∏_v ℤ_v ⊆ ℚ̂`, an open additive subgroup;
* `isCompact_ZHat`: `ℤ̂` is compact;
* `exists_rat_add_ZHat`: **strong approximation** `ℚ̂ = ℚ + ℤ̂`.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

noncomputable section

namespace AdelicToriLean

/-- `x ∈ ℤ_v` iff its image in `ℚ_p` has norm `≤ 1`. -/
theorem mem_integers_iff {v : HeightOneSpectrum ℤ} (x : v.adicCompletion ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ↔ ‖adicCompletion.padicEquiv v x‖ ≤ 1 := by
  constructor
  · intro hx; exact (adicCompletion.padicEquiv_bijOn v).mapsTo hx
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (adicCompletion.padicEquiv_bijOn v).surjOn hx
    rw [(adicCompletion.padicEquiv v).injective hxy] at hy
    exact hy

/-- A rational `r` lies in `ℤ_v` iff `‖r‖_p ≤ 1`. -/
theorem rat_mem_integers_iff {v : HeightOneSpectrum ℤ} (r : ℚ) :
    algebraMap ℚ (v.adicCompletion ℚ) r ∈ v.adicCompletionIntegers ℚ ↔
      ‖(r : ℚ_[primesEquiv v])‖ ≤ 1 := by
  rw [mem_integers_iff, show adicCompletion.padicEquiv v (algebraMap ℚ (v.adicCompletion ℚ) r) =
      algebraMap ℚ ℚ_[primesEquiv v] r from (adicCompletion.padicEquiv v).commutes r, eq_ratCast]

/-- The integral finite adeles `ℤ̂ = ∏_v ℤ_v`. -/
def ZHat : AddSubgroup QHat where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers ℚ}
  add_mem' {a b} ha hb v := by
    show a v + b v ∈ v.adicCompletionIntegers ℚ
    exact (v.adicCompletionIntegers ℚ).add_mem _ _ (ha v) (hb v)
  zero_mem' v := (v.adicCompletionIntegers ℚ).zero_mem
  neg_mem' {a} ha v := by
    show -(a v) ∈ v.adicCompletionIntegers ℚ
    exact (v.adicCompletionIntegers ℚ).neg_mem _ (ha v)

theorem mem_ZHat {a : QHat} : a ∈ ZHat ↔ ∀ v, a v ∈ v.adicCompletionIntegers ℚ :=
  ⟨fun h => h, fun h => h⟩

theorem coe_ZHat : (ZHat : Set QHat) = {a | ∀ v, a v ∈ v.adicCompletionIntegers ℚ} :=
  Set.ext fun _ => mem_ZHat

theorem isOpen_ZHat : IsOpen (ZHat : Set QHat) := by
  rw [coe_ZHat]; exact isOpen_integral

/-- `ℤ_v` is compact: it is the image of the closed unit ball of `ℚ_p`. -/
theorem isCompact_integers (v : HeightOneSpectrum ℤ) :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  have h : (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) =
      (adicCompletion.padicEquiv v).symm '' Metric.closedBall 0 1 := by
    ext x
    constructor
    · intro hx
      refine ⟨adicCompletion.padicEquiv v x, ?_, by simp⟩
      simpa using (mem_integers_iff x).mp hx
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_integers_iff]
      simpa using hy
  rw [h]
  exact (isCompact_closedBall 0 1).image (adicCompletion.padicEquiv v).symm.continuous

instance (v : HeightOneSpectrum ℤ) :
    CompactSpace (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
  isCompact_iff_compactSpace.mp (isCompact_integers v)

/-- `ℤ̂` is compact. -/
theorem isCompact_ZHat : IsCompact (ZHat : Set QHat) := by
  have hAopen : ∀ v : HeightOneSpectrum ℤ,
      IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    fun _ ↦ Valued.isOpen_valuationSubring _
  have hemb := RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (A := fun v => (v.adicCompletionIntegers ℚ)) (𝓕 := Filter.cofinite)
  have hrange : (ZHat : Set QHat) =
      Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
        (fun v => (v.adicCompletionIntegers ℚ)) Filter.cofinite) := by
    ext a
    rw [RestrictedProduct.range_structureMap]
    exact mem_ZHat
  rw [hrange, ← Set.image_univ]
  exact (isCompact_univ.image hemb.continuous)

/-- **Strong approximation.** Every finite adele is a rational plus an integral adele. -/
theorem exists_rat_add_ZHat (a : QHat) : ∃ r : ℚ, ∃ z ∈ ZHat, a = algebraMap ℚ QHat r + z := by
  classical
  -- the finitely many places where `a` is not integral
  have hfin : {v : HeightOneSpectrum ℤ | a v ∉ v.adicCompletionIntegers ℚ}.Finite := by
    have h : ∀ᶠ v in Filter.cofinite, a v ∈ v.adicCompletionIntegers ℚ := a.eventually
    rwa [Filter.eventually_cofinite] at h
  set S := hfin.toFinset
  -- local representatives
  have hloc : ∀ v : HeightOneSpectrum ℤ, ∃ s : ℚ, s ∈ zInvP (primesEquiv v) ∧
      -(s : ℚ_[primesEquiv v]) + adicCompletion.padicEquiv v (a v) ∈ zP (primesEquiv v) := by
    intro v
    obtain ⟨⟨s, hs⟩, hsx⟩ := toQuot_surjective (primesEquiv v)
      (QuotientAddGroup.mk' (zP (primesEquiv v)) (adicCompletion.padicEquiv v (a v)))
    exact ⟨s, hs, QuotientAddGroup.eq.mp hsx⟩
  choose s hsmem hsr using hloc
  set r : ℚ := ∑ w ∈ S, s w
  refine ⟨r, -algebraMap ℚ QHat r + a, ?_, by abel⟩
  rw [mem_ZHat]
  intro v
  rw [mem_integers_iff]
  -- image of the `v`-component in `ℚ_p`
  have himg : adicCompletion.padicEquiv v ((-algebraMap ℚ QHat r + a) v) =
      -(r : ℚ_[primesEquiv v]) + adicCompletion.padicEquiv v (a v) := by
    have hc : adicCompletion.padicEquiv v (algebraMap ℚ (v.adicCompletion ℚ) r) =
        (r : ℚ_[primesEquiv v]) := by
      rw [show adicCompletion.padicEquiv v (algebraMap ℚ (v.adicCompletion ℚ) r) =
        algebraMap ℚ ℚ_[primesEquiv v] r from (adicCompletion.padicEquiv v).commutes r, eq_ratCast]
    rw [show (-algebraMap ℚ QHat r + a) v = -(algebraMap ℚ (v.adicCompletion ℚ) r) + a v from rfl,
      map_add, map_neg, hc]
  rw [himg]
  -- the other representatives are `p`-adic integers
  have hother : ∀ w ∈ S, w ≠ v → ((s w : ℚ) : ℚ_[primesEquiv v]) ∈ zP (primesEquiv v) := by
    intro w _ hwv
    refine mem_zP_of_mem_zInvP (p := primesEquiv w) (q := primesEquiv v) ?_ (hsmem w)
    intro h
    exact hwv ((primesEquiv (R := ℤ)).injective (Subtype.ext h))
  show _ ∈ zP (primesEquiv v)
  by_cases hv : v ∈ S
  · have : -(r : ℚ_[primesEquiv v]) + adicCompletion.padicEquiv v (a v) =
        (-(s v : ℚ_[primesEquiv v]) + adicCompletion.padicEquiv v (a v)) -
          ∑ w ∈ S.erase v, ((s w : ℚ) : ℚ_[primesEquiv v]) := by
      simp only [r, Rat.cast_sum]
      rw [← Finset.add_sum_erase S _ hv]
      ring
    rw [this]
    exact (zP _).sub_mem (hsr v) ((zP _).sum_mem fun w hw =>
      hother w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw))
  · have hav : adicCompletion.padicEquiv v (a v) ∈ zP (primesEquiv v) := by
      have : a v ∈ v.adicCompletionIntegers ℚ := by
        by_contra h; exact hv (hfin.mem_toFinset.mpr h)
      exact (mem_integers_iff _).mp this
    have : -(r : ℚ_[primesEquiv v]) + adicCompletion.padicEquiv v (a v) =
        adicCompletion.padicEquiv v (a v) - ∑ w ∈ S, ((s w : ℚ) : ℚ_[primesEquiv v]) := by
      simp only [r, Rat.cast_sum]; ring
    rw [this]
    exact (zP _).sub_mem hav ((zP _).sum_mem fun w hw =>
      hother w hw (fun h => hv (h ▸ hw)))

end AdelicToriLean
