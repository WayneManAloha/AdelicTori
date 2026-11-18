import AdelicToriLean.DualProd
import AdelicToriLean.StrongApprox

/-!
# Theorem `symmetric-adelic-lie-algebra`

For a commutative topological group `G`, with all hom-spaces in the compact-open topology:

* `nala G = Hom(ℤ̂, G)`, the nonarchimedean Lie algebra;
* `arla G = Hom(ℝ, G)`, the archimedean Lie algebra;
* `adla G = Hom(𝔸_ℤ, G)`, `𝔸_ℤ = ℤ̂ × ℝ`, the adelic Lie algebra.

`symmetric_adelic_lie_algebra`: `adla G ≃ₜ* nala G × arla G`, via `f ↦ (f|_ℤ̂, f|_ℝ)` with inverse
`(u, v) ↦ ((z, x) ↦ u z + v x)`.
-/

open Topology

noncomputable section

namespace AdelicToriLean

instance : CompactSpace ZHat := isCompact_iff_compactSpace.mp isCompact_ZHat

/-- **Hom out of a product.** `Hom(X × Y, G) ≃ₜ* Hom(X, G) × Hom(Y, G)` for locally compact `X, Y`. -/
def homProd (X Y G : Type*) [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
    [LocallyCompactSpace X] [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [LocallyCompactSpace Y] [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ContinuousMonoidHom (X × Y) G ≃ₜ* ContinuousMonoidHom X G × ContinuousMonoidHom Y G where
  toFun φ := (φ.comp (ContinuousMonoidHom.inl X Y), φ.comp (ContinuousMonoidHom.inr X Y))
  invFun p := p.1.coprod p.2
  left_inv φ := ContinuousMonoidHom.ext fun xy => by
    show φ (xy.1, 1) * φ (1, xy.2) = φ xy
    rw [← map_mul]
    simp
  right_inv p := by
    refine Prod.ext (ContinuousMonoidHom.ext fun x => ?_) (ContinuousMonoidHom.ext fun y => ?_)
    · show p.1 x * p.2 1 = p.1 x
      rw [map_one, mul_one]
    · show p.1 1 * p.2 y = p.2 y
      rw [map_one, one_mul]
  map_mul' φ ψ := rfl
  continuous_toFun :=
    (ContinuousMonoidHom.continuous_comp_left _).prodMk
      (ContinuousMonoidHom.continuous_comp_left _)
  continuous_invFun := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    change Continuous (fun q : (ContinuousMonoidHom X G × ContinuousMonoidHom Y G) × (X × Y) =>
      q.1.1 q.2.1 * q.1.2 q.2.2)
    exact (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))).mul
      (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd)))

/-- Contravariance of `Hom(-, G)` on topological isomorphisms. -/
def homCongr {X Y : Type*} (G : Type*) [CommGroup X] [TopologicalSpace X] [CommGroup Y]
    [TopologicalSpace Y] [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : X ≃ₜ* Y) : ContinuousMonoidHom Y G ≃ₜ* ContinuousMonoidHom X G where
  toFun χ := χ.comp ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩
  invFun χ := χ.comp ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩
  left_inv χ := ContinuousMonoidHom.ext fun y => by
    show χ (e (e.symm y)) = χ y
    rw [ContinuousMulEquiv.apply_symm_apply]
  right_inv χ := ContinuousMonoidHom.ext fun x => by
    show χ (e.symm (e x)) = χ x
    rw [ContinuousMulEquiv.symm_apply_apply]
  map_mul' _ _ := rfl
  continuous_toFun := ContinuousMonoidHom.continuous_comp_left _
  continuous_invFun := ContinuousMonoidHom.continuous_comp_left _

/-- The integral adeles `𝔸_ℤ = ℤ̂ × ℝ`. -/
abbrev AZ := ZHat × ℝ

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The nonarchimedean Lie algebra `nala(G) = Hom(ℤ̂, G)` (compact-open topology). -/
abbrev nala := ContinuousMonoidHom (Multiplicative ZHat) G

/-- The archimedean Lie algebra `arla(G) = Hom(ℝ, G)` (compact-open topology). -/
abbrev arla := ContinuousMonoidHom (Multiplicative ℝ) G

/-- The adelic Lie algebra `adla(G) = Hom(𝔸_ℤ, G)` (compact-open topology). -/
abbrev adla := ContinuousMonoidHom (Multiplicative AZ) G

/-- The decomposition map `adla G ≃ₜ* nala G × arla G`. -/
def adlaEquiv : adla G ≃ₜ* nala G × arla G :=
  (homCongr G (multProd ZHat ℝ).symm).trans
    (homProd (Multiplicative ZHat) (Multiplicative ℝ) G)

theorem adlaEquiv_apply (f : adla G) :
    adlaEquiv G f = (f.comp ⟨⟨⟨fun z => Multiplicative.ofAdd (Multiplicative.toAdd z, 0), rfl⟩,
        fun _ _ => by simp [← ofAdd_add]⟩,
        continuous_ofAdd.comp (continuous_toAdd.prodMk continuous_const)⟩,
      f.comp ⟨⟨⟨fun x => Multiplicative.ofAdd (0, Multiplicative.toAdd x), rfl⟩,
        fun _ _ => by simp [← ofAdd_add]⟩,
        continuous_ofAdd.comp (continuous_const.prodMk continuous_toAdd)⟩) := rfl

/-- **Theorem `symmetric-adelic-lie-algebra`.** The adelic Lie algebra of `G` decomposes in the
compact-open topology as `adla(G) ≅ nala(G) × arla(G)`, by restriction to `ℤ̂` and to `ℝ`. -/
theorem symmetric_adelic_lie_algebra : Nonempty (adla G ≃ₜ* nala G × arla G) :=
  ⟨adlaEquiv G⟩

end AdelicToriLean
