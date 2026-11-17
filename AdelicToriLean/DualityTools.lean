import Pontryagin.Duality
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Duality tools

* `surjective_of_isClosed_range`: a continuous `Θ : X →* X^∨` with closed image whose pairing is
  nondegenerate is surjective (via the vendored duality theorem);
* `isClosed_of_compact_nhds`: a subgroup with a compact neighbourhood of `1` is closed;
* `extend_char`: an additive character on a subgroup extends (the circle is divisible, hence
  injective);
* `continuous_extend_of_isOpen`: an extension of a continuous character on an open subgroup is
  continuous.
-/

open Topology

noncomputable section

namespace AdelicToriLean

/-- **Surjectivity by duality.** -/
theorem surjective_of_isClosed_range {X : Type*} [CommGroup X] [TopologicalSpace X]
    [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X] (Θ : X →* PontryaginDual X)
    (hclosed : IsClosed (Θ.range : Set (PontryaginDual X)))
    (hnd : ∀ x : X, x ≠ 1 → ∃ y : X, Θ y x ≠ 1) : Function.Surjective Θ := by
  classical
  intro ξ
  by_contra hξ
  set H := Θ.range
  have : IsClosed (H : Set (PontryaginDual X)) := hclosed
  have hξH : ξ ∉ H := by rintro ⟨a, rfl⟩; exact hξ ⟨a, rfl⟩
  have hne : (QuotientGroup.mk ξ : PontryaginDual X ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have hinj := PontryaginDual.eval_injective (PontryaginDual X ⧸ H)
  obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual (PontryaginDual X ⧸ H), χ (QuotientGroup.mk ξ) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne
    apply hinj
    rw [map_one]
    exact PontryaginDual.ext fun χ => by
      rw [PontryaginDual.eval_apply, hall χ, PontryaginDual.one_apply]
  let ψ : PontryaginDual (PontryaginDual X) :=
    ⟨χ.toMonoidHom.comp (QuotientGroup.mk' H), χ.continuous.comp continuous_quot_mk⟩
  have hψH : ∀ y, ψ (Θ y) = 1 := by
    intro y
    show χ (QuotientGroup.mk (Θ y)) = 1
    rw [(QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨y, rfl⟩), map_one]
  obtain ⟨x, hx⟩ := PontryaginDual.eval_surjective X ψ
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hχ
    show ψ ξ = 1
    rw [← hx, map_one, PontryaginDual.one_apply]
  obtain ⟨y, hy⟩ := hnd x hx1
  apply hy
  have := hψH y
  rwa [← hx, PontryaginDual.eval_apply] at this

/-- A subgroup containing a compact set which is a neighbourhood of `1` in the subgroup is
closed. -/
theorem isClosed_of_compact_nhds {Y : Type*} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [T2Space Y] (H : Subgroup Y) {K : Set Y} (hK : IsCompact K) (hKH : K ⊆ H)
    {W : Set Y} (hW : IsOpen W) (h1 : (1 : Y) ∈ W) (hWK : (H : Set Y) ∩ W ⊆ K) :
    IsClosed (H : Set Y) := by
  have hcpt : IsCompact (Subtype.val ⁻¹' K : Set H) := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    rwa [Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_eq_left.mpr hKH]
  have hnhds : (Subtype.val ⁻¹' K : Set H) ∈ 𝓝 (1 : H) := by
    refine Filter.mem_of_superset ((hW.preimage continuous_subtype_val).mem_nhds h1) ?_
    intro h hh
    exact hWK ⟨h.2, hh⟩
  have : LocallyCompactSpace H := hcpt.locallyCompactSpace_of_mem_nhds_of_group hnhds
  exact Subgroup.isClosed_of_locallyCompactSpace H

/-- **Extension of characters.** The circle `ℝ/ℤ` is divisible, hence an injective `ℤ`-module, so
an additive character on a subgroup extends. -/
theorem extend_char {G : Type} [AddCommGroup G] (H : AddSubgroup G) (φ : H →+ AddCircle (1 : ℝ)) :
    ∃ Φ : G →+ AddCircle (1 : ℝ), ∀ h : H, Φ h = φ h := by
  have hinj : Module.Injective ℤ (AddCircle (1 : ℝ)) :=
    (Module.Baer.of_divisible (AddCircle (1 : ℝ))).injective
  obtain ⟨Φ, hΦ⟩ := hinj.out H.subtype.toIntLinearMap Subtype.val_injective φ.toIntLinearMap
  exact ⟨Φ.toAddMonoidHom, fun h => hΦ h⟩

/-- An additive homomorphism which is continuous on an open subgroup is continuous. -/
theorem continuous_of_open_subgroup {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (H : AddSubgroup G) (hH : IsOpen (H : Set G))
    (Φ : G →+ AddCircle (1 : ℝ)) (hΦ : Continuous fun h : H => Φ h) : Continuous Φ := by
  refine continuous_of_continuousAt_zero Φ ?_
  have hemb : IsOpenEmbedding (Subtype.val : H → G) := hH.isOpenEmbedding_subtypeVal
  have h0 : ContinuousAt ((Φ : G → AddCircle (1 : ℝ)) ∘ Subtype.val) (0 : H) := hΦ.continuousAt
  have := hemb.continuousAt_iff.mp h0
  simpa using this

end AdelicToriLean
