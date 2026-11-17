import AdelicToriLean.AdelicTorus
import AdelicToriLean.Protorus
import AdelicToriLean.RankEmbedding

/-!
# Theorem `fdccg-adelic-tori`: finite-dimensional protori are adelic tori

A *protorus* is a compact connected Hausdorff abelian topological group `G`. Its *archimedean
dimension* is `dim_a G = rk G^∨ = dim_ℚ (ℚ ⊗ G^∨)`, and `G` is *finite-dimensional* when this is
finite.

* `dimA G`: the archimedean dimension;
* `fdccg_adelic_tori`: **`G ≅ (𝔸ⁿ / C) / Λ`** for `n = dim_a G`, where `C = C(ι) ⊆ ℤ̂ⁿ` is the
  annihilator of an embedding `ι : ℤⁿ ⊆ G^∨ ⊆ ℚⁿ` and `Λ` is the image of the diagonal `ℚⁿ`.

The properties of `C` and `Λ` asserted in the paper (torsion-free profinite; discrete,
cocompact, `≅ ℚⁿ`) are separate declarations in `AdelicToriLean.AdelicTorusProps`.
-/

open IsDedekindDomain TensorProduct

noncomputable section

namespace AdelicToriLean

/-- The archimedean dimension `dim_a G = rk G^∨ = dim_ℚ (ℚ ⊗ G^∨)`. -/
abbrev dimA (G : Type*) [CommGroup G] [TopologicalSpace G] : ℕ :=
  Module.finrank ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [ConnectedSpace G] [T2Space G]

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
/-- The dual of a protorus, written additively, is torsion-free. -/
theorem dual_additive_torsionFree :
    ∀ (m : ℕ) (a : Additive (PontryaginDual G)), 0 < m → m • a = 0 → a = 0 := by
  intro m a hm h
  have : (Additive.toMul a) ^ m = 1 := by
    have := congrArg Additive.toMul h
    simpa [toMul_nsmul] using this
  have := dual_torsionFree (Additive.toMul a) hm this
  exact Additive.toMul.injective (by simpa using this)

/-- **Theorem `fdccg-adelic-tori`.** Every finite-dimensional protorus `G`, `dim_a G = n`, is
topologically isomorphic to the adelic torus `(𝔸ⁿ / C) / Λ`: here `ι : G^∨ → ℚⁿ` is an injective
homomorphism whose image contains `ℤⁿ`, `C = Cadd ι` is the annihilator of `ι(G^∨)` in `ℤ̂ⁿ`, and
`Λ = Lam ι` is the image of the diagonal `ℚⁿ`. -/
theorem fdccg_adelic_tori [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    ∃ ι : Additive (PontryaginDual G) →+ (Fin (dimA G) → ℚ),
      Function.Injective ι ∧ (∀ j, Pi.single j 1 ∈ Set.range ι) ∧
      Nonempty (G ≃ₜ* Multiplicative (AdelicTorus ι)) := by
  have : DiscreteTopology (PontryaginDual G) := discreteTopology_dual
  obtain ⟨ι, hι, hZ⟩ := exists_rank_embedding (dual_additive_torsionFree G)
  exact ⟨ι, hι, hZ, ⟨(PontryaginDual.toDoubleDual G).trans (adelicModelEquiv ι hι hZ).symm⟩⟩

end AdelicToriLean
