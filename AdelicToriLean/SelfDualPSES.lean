import AdelicToriLean.ModelProper
import AdelicToriLean.DualProd
import AdelicToriLean.Fdccg

/-!
# Theorem `self-dual-pses`: the Pontryagin self-dual proper short exact sequence

For a finite-dimensional protorus `G` with `dim_a G = n`, with `ι : G^∨ → ℚⁿ` from
Theorem `fdccg-adelic-tori` and `L = C^⊥ / C`:

`0 → G^∨ —j→ L × ℝⁿ —F→ G → 0`

is exact, `j` is injective with discrete image, `F` is continuous, surjective and open, `L` is
periodic, `L × ℝⁿ ≅ (L × ℝⁿ)^∨`, and `G ≅ (G^∨)^∨`.
-/

open IsDedekindDomain Topology TensorProduct

noncomputable section

namespace AdelicToriLean

variable {n : ℕ} {D : Type*} [CommGroup D] (ι : Additive D →+ (Fin n → ℚ))

theorem locallyCompact_modelL : LocallyCompactSpace (ModelL ι) := by
  have : LocallyCompactSpace (Hp (Cm ι)) := (isOpen_perp ι).locallyCompactSpace
  infer_instance

/-- **`L × ℝⁿ ≅ (L × ℝⁿ)^∨`.** -/
def middleSelfDual :
    Multiplicative (ModelL ι × (Fin n → ℝ)) ≃ₜ*
      PontryaginDual (Multiplicative (ModelL ι × (Fin n → ℝ))) := by
  have : LocallyCompactSpace (ModelL ι) := locallyCompact_modelL ι
  have : LocallyCompactSpace (Multiplicative (ModelL ι)) :=
    inferInstanceAs (LocallyCompactSpace (ModelL ι))
  have : LocallyCompactSpace (Multiplicative (Fin n → ℝ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → ℝ))
  exact (multProd _ _).trans ((prodCongrT (modelL_selfDual ι) realSelfDual).trans
    ((dualProd _ _).trans (dualCongr _ _ (multProd _ _))))

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [ConnectedSpace G] [T2Space G]

/-- **Theorem `self-dual-pses`** (Pontryagin self-dual proper short exact sequence). -/
theorem self_dual_pses [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    ∃ ι : Additive (PontryaginDual G) →+ (Fin (dimA G) → ℚ),
    ∃ _hι : Function.Injective ι, ∃ hZ : (∀ j, Pi.single j 1 ∈ Set.range ι),
      -- `L` is periodic
      (∀ l : ModelL ι, ∃ K : AddSubgroup (ModelL ι), IsCompact (K : Set (ModelL ι)) ∧
        IsOpen (K : Set (ModelL ι)) ∧ l ∈ K) ∧
      -- exactness
      Function.Injective (jMap ι hZ) ∧
      (∀ p, FMap ι p = 0 ↔ ∃ d, jMap ι hZ d = p) ∧
      Function.Surjective (FMap ι) ∧
      -- properness
      DiscreteTopology (jMap ι hZ).range ∧ Continuous (FMap ι) ∧ IsOpenMap (FMap ι) ∧
      -- the right-hand term is `G`
      Nonempty (G ≃ₜ* Multiplicative (AdelicTorus ι)) ∧
      -- self-duality
      Nonempty (Multiplicative (ModelL ι × (Fin (dimA G) → ℝ)) ≃ₜ*
        PontryaginDual (Multiplicative (ModelL ι × (Fin (dimA G) → ℝ)))) ∧
      Nonempty (G ≃ₜ* PontryaginDual (PontryaginDual G)) := by
  have : DiscreteTopology (PontryaginDual G) := discreteTopology_dual
  obtain ⟨ι, hι, hZ⟩ := exists_rank_embedding (dual_additive_torsionFree G)
  refine ⟨ι, hι, hZ, periodic_modelL ι, jMap_injective ι hZ hι, fun p => ⟨ker_FMap ι hZ p, ?_⟩,
    FMap_surjective ι, discrete_range_jMap ι hZ, continuous_FMap ι, isOpenMap_FMap ι hι hZ,
    ⟨(PontryaginDual.toDoubleDual G).trans (adelicModelEquiv ι hι hZ).symm⟩,
    ⟨middleSelfDual ι⟩, ⟨PontryaginDual.toDoubleDual G⟩⟩
  rintro ⟨d, rfl⟩
  exact FMap_comp_jMap ι hZ d

end AdelicToriLean
