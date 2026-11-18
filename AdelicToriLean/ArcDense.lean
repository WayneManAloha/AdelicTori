import AdelicToriLean.LieCategory

/-!
# `exp_a(Hom(ℝ, G))` is dense in `G`

For a finite-dimensional protorus `G`, the image of the archimedean exponential
`exp_a : arla(G) → G`, `g ↦ g(1)`, is dense (`dense_range_expa`).

Proof by duality: a character `χ` trivial on the closure satisfies
`χ(v_θ(1)) = exp(∑ⱼ ι(χ)_j θ_j) = 1` for every `θ ∈ ℝⁿ`, so `ι(χ) = 0` and `χ = 1`.
-/

open Topology TensorProduct Real

noncomputable section

namespace AdelicToriLean

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]

omit [T2Space G] in
/-- A character of `G` trivial on a subgroup `H` whose closure is proper is still nontrivial
somewhere outside `H`: characters separate `G` from the closure of `H`. -/
theorem exists_char_of_not_dense {H : Subgroup G} (hH : ¬ Dense (H : Set G)) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ ≠ 1 := by
  set C := H.topologicalClosure
  have hCc : IsClosed (C : Set G) := H.isClosed_topologicalClosure
  obtain ⟨x, hx⟩ : ∃ x, x ∉ C := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hH
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    exact h x
  have : IsClosed (C : Set G) := hCc
  have hne : (x : G ⧸ C) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : PontryaginDual (G ⧸ C), ψ x ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hne
    apply PontryaginDual.eval_injective (G ⧸ C)
    ext ψ
    simp [PontryaginDual.eval_apply, h ψ]
  refine ⟨ψ.comp ⟨QuotientGroup.mk' C, continuous_quot_mk⟩, fun h hh => ?_, fun h1 => ?_⟩
  · show ψ ((h : G) : G ⧸ C) = 1
    rw [(QuotientGroup.eq_one_iff _).mpr (H.le_topologicalClosure hh), map_one]
  · apply hψ
    have := DFunLike.congr_fun h1 x
    rw [PontryaginDual.one_apply] at this
    exact this

section Data

variable [DiscreteTopology (PontryaginDual G)] {n : ℕ}
  {ι : Additive (PontryaginDual G) →+ (Fin n → ℚ)} (hι : Function.Injective ι)

omit [CompactSpace G] [T2Space G] [DiscreteTopology (PontryaginDual G)] in
theorem circle_exp_mul_eq_one {c : ℝ} (h : ∀ s : ℝ, Circle.exp (s * c) = 1) : c = 0 := by
  by_contra hc
  have := h (π / c)
  rw [div_mul_cancel₀ _ hc, Circle.exp_eq_one] at this
  obtain ⟨m, hm⟩ := this
  have hm' : (1 : ℝ) = 2 * m := by
    have := pi_pos
    field_simp at hm
    nlinarith
  have : (2 * m : ℤ) = 1 := by exact_mod_cast hm'.symm
  omega

include hι in
/-- **`exp_a(Hom(ℝ, G))` is dense in `G`.** -/
theorem dense_range_expa_of : Dense (Set.range (expa G)) := by
  by_contra hden
  have hH : ¬ Dense ((expa G).range : Set G) := by
    rwa [MonoidHom.coe_range]
  obtain ⟨χ, hχ, hχ1⟩ := exists_char_of_not_dense hH
  apply hχ1
  -- `coef θ χ` vanishes identically
  have hcoef : ∀ j, ((ι (Additive.ofMul χ) j : ℚ) : ℝ) = 0 := by
    intro j
    refine circle_exp_mul_eq_one fun s => ?_
    set θ : Fin n → ℝ := Pi.single j s
    have h1 := hχ _ ⟨vθ ι θ, rfl⟩
    have h2 : χ (expa G (vθ ι θ)) =
        Circle.exp (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℝ)) * coef ι θ χ) :=
      congrArg (fun φ : PontryaginDual (PontryaginDual G) => φ χ)
        (toDoubleDual_vθ ι θ (Multiplicative.ofAdd 1))
    rw [h2, toAdd_ofAdd, one_mul, coef, Finset.sum_eq_single j] at h1
    · simpa [θ, mul_comm] using h1
    · intro i _ hij; simp [θ, Pi.single_eq_of_ne hij]
    · intro h; exact absurd (Finset.mem_univ j) h
  have h0 : ι (Additive.ofMul χ) = 0 := by
    funext j; exact_mod_cast hcoef j
  have : Additive.ofMul χ = 0 := hι (by rw [h0, map_zero])
  exact congrArg Additive.toMul this

end Data

variable (G) in
/-- **`exp_a(Hom(ℝ, G))` is dense** in a finite-dimensional protorus `G`. -/
theorem dense_range_expa [ConnectedSpace G]
    [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    Dense (Set.range (expa G)) := by
  have : DiscreteTopology (PontryaginDual G) := discreteTopology_dual
  obtain ⟨ι, hι, hZ⟩ := exists_rank_embedding (dual_additive_torsionFree G)
  exact dense_range_expa_of hι

end AdelicToriLean
