import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# A torsion-free group of finite rank lies between `ℤⁿ` and `ℚⁿ`

The paper's proof of Theorem `fdccg-adelic-tori` begins: "Since `G^∨` is torsion-free of rank `n`,
choose a full-rank free subgroup `F ≅ ℤⁿ` of `G^∨` and identify `ℤⁿ = F ⊆ G^∨ ⊆ ℚⁿ`." Here, for a
torsion-free abelian group `A` with `rk A = dim_ℚ (ℚ ⊗ A) = n`:

* `exists_rank_embedding`: an injective `ι : A → ℚⁿ` whose image contains the standard basis.
-/

open TensorProduct

noncomputable section

namespace AdelicToriLean

variable {A : Type*} [AddCommGroup A]

/-- For a torsion-free `A`, the map `A → ℚ ⊗ A`, `a ↦ 1 ⊗ a`, is injective. -/
theorem tmul_injective (htf : ∀ (m : ℕ) (a : A), 0 < m → m • a = 0 → a = 0) :
    Function.Injective (TensorProduct.mk ℤ ℚ A 1) := by
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ A 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).mpr
      (TensorProduct.isBaseChange ℤ A ℚ)
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ A 1)).mp ha
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsa' : s • a = 0 := hsa
  apply htf s.natAbs a (Int.natAbs_pos.mpr hs0)
  rcases Int.natAbs_eq s with h | h
  · rw [← natCast_zsmul, ← h]; exact hsa'
  · rw [← natCast_zsmul, show ((s.natAbs : ℕ) : ℤ) = -s by omega, neg_zsmul, hsa', neg_zero]

/-- **Rank embedding.** A torsion-free abelian group of rank `n` embeds in `ℚⁿ` with the standard
basis vectors in its image. -/
theorem exists_rank_embedding (htf : ∀ (m : ℕ) (a : A), 0 < m → m • a = 0 → a = 0)
    [FiniteDimensional ℚ (ℚ ⊗[ℤ] A)] :
    ∃ ι : A →+ (Fin (Module.finrank ℚ (ℚ ⊗[ℤ] A)) → ℚ),
      Function.Injective ι ∧ ∀ j, Pi.single j 1 ∈ Set.range ι := by
  classical
  set V := ℚ ⊗[ℤ] A
  set f := TensorProduct.mk ℤ ℚ A 1
  -- the image of `A` spans `V`
  have hspan : Submodule.span ℚ (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    induction v using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul q a =>
      have : q ⊗ₜ[ℤ] a = q • f a := by simp [f, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ q (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy => exact add_mem hx hy
  obtain ⟨t, ht, htspan, htli⟩ := exists_linearIndependent ℚ (Set.range f)
  rw [hspan] at htspan
  let b : Module.Basis t ℚ V :=
    Module.Basis.mk htli (by rw [Subtype.range_coe_subtype]; exact htspan.ge)
  let _ : Fintype t := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card t = Module.finrank ℚ V := by
    rw [Module.finrank_eq_card_basis b]
  let e : t ≃ Fin (Module.finrank ℚ V) := Fintype.equivFinOfCardEq hcard
  let b' : Module.Basis (Fin (Module.finrank ℚ V)) ℚ V := b.reindex e
  refine ⟨(b'.equivFun.toLinearMap.restrictScalars ℤ ∘ₗ f).toAddMonoidHom, ?_, ?_⟩
  · intro x y hxy
    exact tmul_injective htf (b'.equivFun.injective hxy)
  · intro j
    obtain ⟨a, ha⟩ := ht (e.symm j).2
    refine ⟨a, ?_⟩
    show b'.equivFun (f a) = Pi.single j 1
    have : f a = b' j := by
      simp only [b', Module.Basis.reindex_apply, b, Module.Basis.coe_mk]
      exact ha
    rw [this]
    ext k
    simp [Pi.single_apply, eq_comm]

end AdelicToriLean
