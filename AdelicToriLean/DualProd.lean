import Pontryagin.Duality

/-!
# Dual of a product

`dualProd X Y : X^∨ × Y^∨ ≃ₜ* (X × Y)^∨`, `(χ, ψ) ↦ ((x, y) ↦ χ x ψ y)`, for locally compact `X, Y`.
-/

open Topology

noncomputable section

namespace AdelicToriLean

variable (X Y : Type*) [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
  [LocallyCompactSpace X] [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
  [LocallyCompactSpace Y]

instance (Z : Type*) [CommGroup Z] [TopologicalSpace Z] [IsTopologicalGroup Z]
    [LocallyCompactSpace Z] : ContinuousEval (PontryaginDual Z) Z Circle :=
  inferInstanceAs (ContinuousEval (ContinuousMonoidHom Z Circle) Z Circle)

/-- **Dual of a product.** -/
def dualProd : PontryaginDual X × PontryaginDual Y ≃ₜ* PontryaginDual (X × Y) where
  toFun p := p.1.coprod p.2
  invFun φ := (φ.comp (ContinuousMonoidHom.inl X Y), φ.comp (ContinuousMonoidHom.inr X Y))
  left_inv p := by
    refine Prod.ext (PontryaginDual.ext fun x => ?_) (PontryaginDual.ext fun y => ?_)
    · show p.1 x * p.2 1 = p.1 x
      rw [map_one, mul_one]
    · show p.1 1 * p.2 y = p.2 y
      rw [map_one, one_mul]
  right_inv φ := PontryaginDual.ext fun xy => by
    show φ (xy.1, 1) * φ (1, xy.2) = φ xy
    rw [← map_mul]
    simp
  map_mul' p q := PontryaginDual.ext fun xy => by
    show (p.1 xy.1 * q.1 xy.1) * (p.2 xy.2 * q.2 xy.2) =
      (p.1 xy.1 * p.2 xy.2) * (q.1 xy.1 * q.2 xy.2)
    exact mul_mul_mul_comm _ _ _ _
  continuous_toFun := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    change Continuous (fun q : (PontryaginDual X × PontryaginDual Y) × (X × Y) =>
      q.1.1 q.2.1 * q.1.2 q.2.2)
    exact (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))).mul
      (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd)))
  continuous_invFun :=
    (ContinuousMonoidHom.continuous_comp_left _).prodMk
      (ContinuousMonoidHom.continuous_comp_left _)

omit [IsTopologicalGroup X] [LocallyCompactSpace X] [IsTopologicalGroup Y]
  [LocallyCompactSpace Y] in
/-- Contravariance of the dual on topological isomorphisms. -/
def dualCongr (e : X ≃ₜ* Y) : PontryaginDual Y ≃ₜ* PontryaginDual X where
  toFun χ := χ.comp ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩
  invFun χ := χ.comp ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩
  left_inv χ := PontryaginDual.ext fun y => by
    show χ (e (e.symm y)) = χ y
    rw [ContinuousMulEquiv.apply_symm_apply]
  right_inv χ := PontryaginDual.ext fun x => by
    show χ (e.symm (e x)) = χ x
    rw [ContinuousMulEquiv.symm_apply_apply]
  map_mul' _ _ := rfl
  continuous_toFun := ContinuousMonoidHom.continuous_comp_left _
  continuous_invFun := ContinuousMonoidHom.continuous_comp_left _

/-- `Multiplicative (A × B) ≃ₜ* Multiplicative A × Multiplicative B`. -/
def multProd (A B : Type*) [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
    [TopologicalSpace B] : Multiplicative (A × B) ≃ₜ* Multiplicative A × Multiplicative B where
  toFun p := (Multiplicative.ofAdd (Multiplicative.toAdd p).1,
    Multiplicative.ofAdd (Multiplicative.toAdd p).2)
  invFun q := Multiplicative.ofAdd (Multiplicative.toAdd q.1, Multiplicative.toAdd q.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_ofAdd.comp (continuous_fst.comp continuous_toAdd)).prodMk
    (continuous_ofAdd.comp (continuous_snd.comp continuous_toAdd))
  continuous_invFun := continuous_ofAdd.comp ((continuous_toAdd.comp continuous_fst).prodMk
    (continuous_toAdd.comp continuous_snd))

/-- Product of two topological isomorphisms. -/
def prodCongrT {A B A' B' : Type*} [Mul A] [TopologicalSpace A] [Mul B] [TopologicalSpace B]
    [Mul A'] [TopologicalSpace A'] [Mul B'] [TopologicalSpace B'] (e : A ≃ₜ* A') (f : B ≃ₜ* B') :
    A × B ≃ₜ* A' × B' where
  toFun p := (e p.1, f p.2)
  invFun q := (e.symm q.1, f.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_mul' p q := by simp
  continuous_toFun := (e.continuous.comp continuous_fst).prodMk (f.continuous.comp continuous_snd)
  continuous_invFun :=
    (e.symm.continuous.comp continuous_fst).prodMk (f.symm.continuous.comp continuous_snd)

end AdelicToriLean
