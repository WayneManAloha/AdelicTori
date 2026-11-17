import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Separation.Connected

/-!
# Basic facts on protori

A *protorus* is a compact connected Hausdorff abelian topological group. This file proves two
standard facts used in the paper's proof of Theorem `fdccg-adelic-tori`:

* `subgroup_le_centeredArc`: a subgroup of the circle inside the open arc `|arg z| < π/2` is
  trivial ("no small subgroups");
* `discreteTopology_dual`: the Pontryagin dual of a compact abelian group is discrete;
* `dual_torsionFree`: the Pontryagin dual of a connected abelian group is torsion-free.
-/

open Circle Real

namespace AdelicToriLean

/-- **No small subgroups.** A subgroup of the circle contained in the open arc `|arg z| < π/2` is
trivial. -/
theorem subgroup_le_centeredArc (H : Subgroup Circle) (hH : (H : Set Circle) ⊆ centeredArc (π / 2)) :
    H = ⊥ := by
  have key : ∀ k : ℕ, ∀ w ∈ H, w ∈ centeredArc (π / 2 / 2 ^ k) := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hH hw
    | succ k ih =>
      intro w hw
      have h2 : w ^ 2 ∈ centeredArc (π / 2 / 2 ^ k) := ih _ (H.pow_mem hw 2)
      have h1 : w ∈ centeredArc (π / (2 : ℕ)) := by simpa using hH hw
      have := mem_centeredArc_div (n := 2)
        (div_le_self (div_nonneg Real.pi_pos.le (by norm_num)) (one_le_pow₀ (by norm_num))
          |>.trans (div_le_self Real.pi_pos.le (by norm_num))) h1 h2
      rwa [Nat.cast_ofNat, div_div, ← pow_succ] at this
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  have harg : Complex.arg w = 0 := by
    by_contra hne
    have hpos : 0 < |Complex.arg w| := abs_pos.mpr hne
    obtain ⟨k, hk⟩ : ∃ k : ℕ, π / 2 / 2 ^ k < |Complex.arg w| := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hpos (by positivity : (0:ℝ) < π / 2))
        (by norm_num : (1 / 2 : ℝ) < 1)
      refine ⟨k, ?_⟩
      rw [one_div, inv_pow, lt_div_iff₀ (by positivity : (0:ℝ) < π / 2)] at hk
      rw [div_lt_iff₀ (by positivity)]
      calc π / 2 = π / 2 * 1 := by ring
        _ = π / 2 * ((2 ^ k)⁻¹ * 2 ^ k) := by rw [inv_mul_cancel₀ (by positivity)]
        _ = (2 ^ k)⁻¹ * (π / 2) * 2 ^ k := by ring
        _ < |Complex.arg w| * 2 ^ k := by gcongr
    have hle : π / 2 / 2 ^ k ≤ π :=
      (div_le_self (div_nonneg Real.pi_pos.le (by norm_num)) (one_le_pow₀ (by norm_num))).trans
        (div_le_self Real.pi_pos.le (by norm_num))
    have := (mem_centeredArc hle).mp (key k w hw)
    linarith
  rw [← exp_arg w, harg, Circle.exp_zero]

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- A character is trivial iff its values lie in the arc `|arg z| < π/2`. -/
theorem eq_one_iff_mapsTo_arc (χ : PontryaginDual G) :
    χ = 1 ↔ Set.MapsTo (ContinuousMonoidHom.toContinuousMap χ) Set.univ (centeredArc (π / 2)) := by
  constructor
  · rintro rfl g _
    exact ⟨0, by simp [Real.pi_pos], by rw [Circle.exp_zero]; exact (PontryaginDual.one_apply g).symm⟩
  · intro h
    have hbot := subgroup_le_centeredArc χ.toMonoidHom.range (by
      rintro _ ⟨g, rfl⟩; exact h (Set.mem_univ g))
    ext g
    have : χ g ∈ χ.toMonoidHom.range := ⟨g, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    rw [PontryaginDual.one_apply]; exact congrArg Subtype.val this

omit [IsTopologicalGroup G] in
/-- The Pontryagin dual of a compact abelian group is discrete. -/
theorem discreteTopology_dual [CompactSpace G] : DiscreteTopology (PontryaginDual G) := by
  apply discreteTopology_of_isOpen_singleton_one
  have h1 : IsOpen {f : C(G, Circle) | Set.MapsTo f Set.univ (centeredArc (π / 2))} :=
    ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ (Circle.isOpen_centeredArc (r := π / 2))
  have hU := h1.preimage (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
  have heq : ({1} : Set (PontryaginDual G)) = ContinuousMonoidHom.toContinuousMap ⁻¹'
      {f : C(G, Circle) | Set.MapsTo f Set.univ (centeredArc (π / 2))} := by
    apply Set.ext
    intro χ
    simp only [Set.mem_singleton_iff]
    exact eq_one_iff_mapsTo_arc χ
  rw [heq]; exact hU

omit [IsTopologicalGroup G] in
/-- The Pontryagin dual of a connected abelian group is torsion-free: a character of finite order
is trivial. -/
theorem dual_torsionFree [ConnectedSpace G] (χ : PontryaginDual G) {m : ℕ} (hm : 0 < m)
    (hχ : χ ^ m = 1) : χ = 1 := by
  have hroots : {z : Circle | z ^ m = 1}.Finite := by
    refine ((Polynomial.nthRoots m (1 : ℂ)).toFinset.finite_toSet.preimage
      (f := fun z : Circle => (z : ℂ)) Circle.coe_injective.injOn).subset ?_
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots hm]
    rw [← Circle.coe_pow, hz, Circle.coe_one]
  have hfin : (Set.range χ).Finite := hroots.subset (by
    rintro _ ⟨g, rfl⟩
    have := congrArg (fun ψ : PontryaginDual G => ψ g) hχ
    simp only [PontryaginDual.one_apply] at this
    rw [show (χ ^ m) g = χ g ^ m from ContinuousMonoidHom.pow_apply χ m g] at this
    exact this)
  have hconn : IsPreconnected (Set.range χ) := isPreconnected_range χ.continuous
  have hsub : (Set.range χ).Subsingleton := by
    by_contra hnt
    exact (hconn.infinite_of_nontrivial (Set.not_subsingleton_iff.mp hnt)) hfin
  ext g
  have h1 : (1 : Circle) ∈ Set.range χ := ⟨1, map_one χ⟩
  rw [PontryaginDual.one_apply]
  exact congrArg Subtype.val (hsub ⟨g, rfl⟩ h1)

end AdelicToriLean
