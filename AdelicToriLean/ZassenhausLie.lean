import AdelicToriLean.ZassenhausRealisation
import AdelicToriLean.LieCategory
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Theorem `zassenhaus-realisation`: `B_K^∨ ≅ (Lie_n(B_K^∨) × ℝ·K)/K`

With `G = B_K^∨`, `n = [K : ℚ]`, and `ℝ·K ≅ ℝⁿ`, `K ≅ ℚⁿ` through the integral basis
(`basisK`):

* `lieResolutionEquiv`: `E(f, g) = f(1) · g(1)` induces `(Lie_n(G) × Lie_a(G))/ker E ≅ G`
  topologically, with `Lie_a(G) ≅ ℝⁿ = ℝ·K`;
* `diagK`: **the diagonal copy of `K`**, `K ≃ ker E`; its archimedean coordinate is explicit:
  `k ↦ 2π·(coordinates of k)` in `ℝ·K` (`diagK_arch`), and its nonarchimedean coordinate is the
  unique `f ∈ Lie_n(G)` with `f(1) = exp_a(·)⁻¹`; `ker E` is discrete;
* `diagonalK`: in the tensor model the real coordinate is `1 ⊗ k` and the finite coordinate
  is determined by evaluation at `1 ∈ ℚ̂` (`diagK_finite`);
* `zassenhausLieEquiv`: the topological isomorphism with the quotient by the range of `diagonalK`.
-/

open Topology NumberField Real TensorProduct

noncomputable section

namespace AdelicToriLean

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

/-- `B_K^∨`. -/
abbrev GK := PontryaginDual (Multiplicative (BKd D))

instance : DiscreteTopology (PontryaginDual (GK D)) := discreteTopology_dual

theorem iotaGK_injective : Function.Injective (iotaG (iotaK D)) :=
  iotaG_injective (iotaK_injective D)

theorem iotaGK_d (j : Fin (Module.finrank ℚ K)) :
    iotaG (iotaK D) (dG (dK D) j) = Pi.single j 1 :=
  iotaG_dG (iotaK_dK D) j

private def quotientExpEquiv {A H : Type*} [CommGroup A] [CommGroup H]
    [TopologicalSpace A] [TopologicalSpace H] {f : A →* H}
    (hq : IsOpenQuotientMap f) : A ⧸ f.ker ≃ₜ* H := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hq.surjective
  have hc : Continuous e :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hq.continuous
  have hc' : Continuous e.symm := by
    rw [← hq.continuous_comp_iff]
    refine continuous_quot_mk.congr fun p => ?_
    apply e.injective
    rw [Function.comp_apply, MulEquiv.apply_symm_apply]
    rfl
  exact { e with continuous_toFun := hc, continuous_invFun := hc' }

/-- **`(Lie_n(G) × Lie_a(G))/ker E ≅ G`** topologically, `G = B_K^∨`. -/
def lieResolutionEquiv :
    (nala (GK D) × arla (GK D)) ⧸ (Eexp (GK D)).ker ≃ₜ* GK D :=
  quotientExpEquiv ⟨E_surjective (iotaGK_injective D) (iotaGK_d D),
    continuous_Eexp (GK D), E_isOpenMap (iotaGK_injective D) (iotaGK_d D)⟩

/-- Coordinates of `K` in the integral basis, `K ≅ ℚⁿ`. -/
def coordsK : Multiplicative K ≃* Multiplicative (Fin (Module.finrank ℚ K) → ℚ) :=
  AddEquiv.toMultiplicative (basisK K).equivFun.toAddEquiv

/-- **The diagonal copy of `K`** in `Lie_n(G) × Lie_a(G)`: `K ≅ ker E`. -/
def diagK : Multiplicative K ≃* (Eexp (GK D)).ker :=
  (coordsK (K := K)).trans (kerE_equiv (iotaGK_injective D) (iotaGK_d D)).symm

theorem twoPiRat_kerE (x : (Eexp (GK D)).ker) :
    twoPiRat (kerE_equiv (iotaGK_injective D) (iotaGK_d D) x) =
      kerCoord (iotaGK_injective D) (iotaGK_d D) x := by
  simp only [kerE_equiv, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
    MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

/-- **The archimedean coordinate of the diagonal `K`**: `k ↦ 2π·coords(k) ∈ ℝ·K ≅ ℝⁿ`. -/
theorem diagK_arch (k : K) :
    arlaEquiv (iotaGK_d D) (iotaGK_injective D) (diagK D (Multiplicative.ofAdd k)).1.2 =
      Multiplicative.ofAdd fun j => 2 * π * ((basisK K).equivFun k j : ℝ) := by
  have := twoPiRat_kerE D (diagK D (Multiplicative.ofAdd k))
  rw [diagK, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at this
  exact this.symm

/-- Evaluation at `1 ∈ ℚ̂` determines the finite coordinate of the diagonal. -/
theorem diagK_finite (k : K) (f : nala (GK D)) :
    f = (diagK D (Multiplicative.ofAdd k)).1.1 ↔
      expn (GK D) f =
        (expa (GK D) (vθ (iotaG (iotaK D))
          (fun j => 2 * π * ((basisK K).equivFun k j : ℝ))))⁻¹ := by
  have hg := congrArg (arlaEquiv (iotaGK_d D) (iotaGK_injective D)).symm (diagK_arch D k)
  rw [ContinuousMulEquiv.symm_apply_apply] at hg
  have h := (diagK D (Multiplicative.ofAdd k)).2
  rw [MonoidHom.mem_ker, Eexp_apply, hg] at h
  have hf := eq_inv_of_mul_eq_one_left h
  change expn (GK D) _ = (expa (GK D) (vθ (iotaG (iotaK D)) _))⁻¹ at hf
  exact ⟨fun he => he ▸ hf, fun he => expn_injective (GK D) (he.trans hf.symm)⟩

/-- Real scalar extension in the integral basis. -/
def realTensorCoords : (ℝ ⊗[ℚ] K) ≃ₗ[ℝ] (Fin (Module.finrank ℚ K) → ℝ) :=
  ((basisK K).baseChange ℝ).equivFun

/-- The usual finite-dimensional real vector-space topology on `ℝ ⊗[ℚ] K`. -/
instance instRealTensorTopology : TopologicalSpace (ℝ ⊗[ℚ] K) :=
  TopologicalSpace.induced (realTensorCoords (K := K)) inferInstance

instance instRealTensorTopologicalAddGroup : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) :=
  topologicalAddGroup_induced (realTensorCoords (K := K)).toLinearMap

/-- Convert real tensor coordinates to angles in the archimedean Lie algebra. -/
def tensorToArla : Multiplicative (ℝ ⊗[ℚ] K) ≃ₜ* arla (GK D) := by
  let e := realTensorCoords (K := K)
  let scale : (Fin (Module.finrank ℚ K) → ℝ) ≃ₗ[ℝ] _ :=
    LinearEquiv.smulOfNeZero ℝ _ (2 * π) (by positivity)
  let h := e.toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩
  let s := scale.toContinuousLinearEquiv.toHomeomorph
  let m : Multiplicative (ℝ ⊗[ℚ] K) ≃* Multiplicative (Fin (Module.finrank ℚ K) → ℝ) :=
    (e.trans scale).toAddEquiv.toMultiplicative
  exact (show Multiplicative (ℝ ⊗[ℚ] K) ≃ₜ* Multiplicative (Fin (Module.finrank ℚ K) → ℝ) from
    ⟨m, s.continuous.comp h.continuous, h.symm.continuous.comp s.symm.continuous⟩).trans
      (arlaEquiv (iotaGK_d D) (iotaGK_injective D)).symm

/-- The normalization by `2π` sends `1 ⊗ k` to the archimedean coordinate of `diagK k`. -/
theorem tensorToArla_one_tmul (k : K) :
    tensorToArla D (Multiplicative.ofAdd ((1 : ℝ) ⊗ₜ[ℚ] k)) =
      (diagK D (Multiplicative.ofAdd k)).1.2 := by
  apply (arlaEquiv (iotaGK_d D) (iotaGK_injective D)).injective
  rw [diagK_arch]
  change (arlaEquiv (iotaGK_d D) (iotaGK_injective D))
    ((arlaEquiv (iotaGK_d D) (iotaGK_injective D)).symm
      (Multiplicative.ofAdd ((2 * π) • realTensorCoords ((1 : ℝ) ⊗ₜ[ℚ] k)))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  congr 1
  funext j
  simp [realTensorCoords, Pi.smul_apply, smul_eq_mul, Rat.smul_def]

private def tensorToLie :
    nala (GK D) × Multiplicative (ℝ ⊗[ℚ] K) ≃ₜ* nala (GK D) × arla (GK D) :=
  let h := (Homeomorph.refl _).prodCongr (tensorToArla D).toHomeomorph
  ⟨(MulEquiv.refl _).prodCongr (tensorToArla D).toMulEquiv, h.continuous, h.symm.continuous⟩

/-- Transport the adelic exponential from Lie coordinates to the real tensor product. -/
def tensorExp : nala (GK D) × Multiplicative (ℝ ⊗[ℚ] K) →* GK D :=
  (Eexp (GK D)).comp ((tensorToLie D).toMulEquiv : _ →* _)

/-- The diagonal map in the product with the real tensor factor. -/
def diagonalK : Multiplicative K →* nala (GK D) × Multiplicative (ℝ ⊗[ℚ] K) :=
  ((tensorToLie D).toMulEquiv.symm : _ →* _).comp
    ((Eexp (GK D)).ker.subtype.comp (diagK D).toMonoidHom)

/-- In the real tensor factor the diagonal map is the scalar extension `k ↦ 1 ⊗ k`. -/
theorem diagonalK_apply (k : K) :
    diagonalK D (Multiplicative.ofAdd k) =
      ((diagK D (Multiplicative.ofAdd k)).1.1, Multiplicative.ofAdd ((1 : ℝ) ⊗ₜ[ℚ] k)) := by
  refine Prod.ext rfl ?_
  apply (tensorToArla D).injective
  exact ((tensorToArla D).apply_symm_apply _).trans (tensorToArla_one_tmul D k).symm

theorem diagonalK_injective : Function.Injective (diagonalK D) :=
  (tensorToLie D).symm.injective.comp (Subtype.val_injective.comp (diagK D).injective)

/-- The kernel of the adelic exponential in tensor coordinates is exactly the diagonal copy of `K`. -/
theorem diagonalK_range : (diagonalK D).range = (tensorExp D).ker := by
  rw [diagonalK, tensorExp, MonoidHom.ker_comp_mulEquiv (Eexp (GK D)) (tensorToLie D).toMulEquiv,
    MonoidHom.range_comp,
    MonoidHom.range_comp, (diagK D).toMonoidHom.range_eq_top_of_surjective (diagK D).surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- The adelic Lie quotient of `B_K^∨`, with the diagonal `K` as its denominator. -/
def zassenhausLieEquiv :
    GK D ≃ₜ* (nala (GK D) × Multiplicative (ℝ ⊗[ℚ] K)) ⧸ (diagonalK D).range := by
  rw [diagonalK_range]
  have hs : Function.Surjective (tensorExp D) :=
    (E_surjective (iotaGK_injective D) (iotaGK_d D)).comp (tensorToLie D).surjective
  have hc : Continuous (tensorExp D) := (continuous_Eexp (GK D)).comp (tensorToLie D).continuous
  have ho : IsOpenMap (tensorExp D) :=
    (E_isOpenMap (iotaGK_injective D) (iotaGK_d D)).comp (tensorToLie D).toHomeomorph.isOpenMap
  exact (quotientExpEquiv ⟨hs, hc, ho⟩).symm
/-- **Theorem `zassenhaus-realisation`: `B_K^∨ ≅ (Lie_n(B_K^∨) × ℝ·K)/K`.** The adelic
exponential `E(f, g) = f(1) · g(1)` induces a topological isomorphism from
`(Lie_n(G) × Lie_a(G))/ker E` onto `G = B_K^∨`, `Lie_a(G) ≅ ℝ^[K:ℚ] = ℝ·K`, and `ker E` is the
discrete diagonal copy of `K`, whose archimedean coordinate is `k ↦ 2π·coords(k)`. -/
theorem zassenhaus_lie :
    Nonempty (GK D ≃ₜ* (nala (GK D) × Multiplicative (ℝ ⊗[ℚ] K)) ⧸ (diagonalK D).range) ∧
      Nonempty ((nala (GK D) × arla (GK D)) ⧸ (Eexp (GK D)).ker ≃ₜ* GK D) ∧
      Nonempty (arla (GK D) ≃ₜ* Multiplicative (Fin (Module.finrank ℚ K) → ℝ)) ∧
      DiscreteTopology (Eexp (GK D)).ker ∧
      Nonempty (Multiplicative K ≃* (Eexp (GK D)).ker) ∧
      (∀ k : K, arlaEquiv (iotaGK_d D) (iotaGK_injective D)
        (diagK D (Multiplicative.ofAdd k)).1.2 =
          Multiplicative.ofAdd fun j => 2 * π * ((basisK K).equivFun k j : ℝ)) :=
  ⟨⟨zassenhausLieEquiv D⟩, ⟨lieResolutionEquiv D⟩, ⟨arlaEquiv (iotaGK_d D) (iotaGK_injective D)⟩,
    discrete_kerE (iotaGK_injective D) (iotaGK_d D), ⟨diagK D⟩, diagK_arch D⟩

end AdelicToriLean
