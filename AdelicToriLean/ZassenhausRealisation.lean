import AdelicToriLean.ZassenhausTopology
import AdelicToriLean.ArcComponent
import AdelicToriLean.Paper

/-!
# Theorem `zassenhaus-realisation`: the topological half

For the group of integers `B_K = Σ_k 𝔭_k⁻¹` (`D.BK`), taken discrete (`BKd D`), and a `ℤ`-basis
of `𝒪_K` (`NumberField.integralBasis`, a `ℚ`-basis of `K`), write
`T_K^∨ = 𝒪_K^⊥ ⊆ B_K^∨` (`TK D`), the characters of `B_K` trivial on `𝒪_K` (the dual of
`T_K = B_K/𝒪_K`). With `n = [K : ℚ]` (`zassenhaus_topological`):

* `B_K^∨` is compact, connected and Hausdorff;
* `T_K^∨` is a delta-subgroup of `B_K^∨`, with `B_K^∨ / T_K^∨ ≅ (ℝ/ℤ)ⁿ`;
* `(δ, x) ↦ δ · exp_a(x)` induces `(T_K^∨ × ℝⁿ)/𝒪_K ≅ B_K^∨`, `𝒪_K = ℤⁿ` embedded diagonally;
* the projection of the diagonal `𝒪_K` into `T_K^∨` is dense.
-/

open Topology Real NumberField

noncomputable section

namespace AdelicToriLean

/-- A compact group whose dual embeds in `ℚⁿ` with `ι(d_j) = e_j` is connected:
`exp_a(Hom(ℝ, G))` lies in the path component of `1` and is dense. -/
theorem connectedSpace_of_rank {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [DiscreteTopology (PontryaginDual G)]
    {n : ℕ} {ι : Additive (PontryaginDual G) →+ (Fin n → ℚ)} (hι : Function.Injective ι) :
    ConnectedSpace G := by
  have hd : Dense (pathComponent (1 : G)) := (dense_range_expa_of hι).mono range_expa_subset
  have hc : IsConnected (closure (pathComponent (1 : G))) :=
    isPathConnected_pathComponent.isConnected.closure
  rw [hd.closure_eq] at hc
  exact connectedSpace_iff_univ.mpr hc

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

/-- `B_K` with the discrete topology. -/
def BKd : Type _ := D.BK

instance : AddCommGroup (BKd D) := inferInstanceAs (AddCommGroup D.BK)
instance : TopologicalSpace (BKd D) := ⊥
instance : DiscreteTopology (BKd D) := ⟨rfl⟩

variable {D} in
/-- The underlying element of `K`. -/
def BKd.toK (x : BKd D) : K := ((show D.BK from x) : K)

variable {D} in
@[simp] theorem BKd.toK_add (x y : BKd D) : (x + y).toK = x.toK + y.toK := rfl
variable {D} in
@[simp] theorem BKd.toK_zero : (0 : BKd D).toK = 0 := rfl

variable (K) in
/-- The `ℚ`-basis of `K` given by a `ℤ`-basis of `𝒪_K`, indexed by `Fin [K : ℚ]`. -/
def basisK : Module.Basis (Fin (Module.finrank ℚ K)) ℚ K :=
  (integralBasis K).reindex
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis (integralBasis K)).symm)

/-- `B_K → K → ℚⁿ`, coordinates in the integral basis. -/
def iotaK : BKd D →+ (Fin (Module.finrank ℚ K) → ℚ) where
  toFun x := (basisK K).equivFun x.toK
  map_zero' := by rw [BKd.toK_zero, map_zero]
  map_add' x y := by rw [BKd.toK_add, map_add]

theorem iotaK_injective : Function.Injective (iotaK D) := by
  intro x y h
  have : x.toK = y.toK := (basisK K).equivFun.injective h
  exact Subtype.ext this

theorem basisK_mem_OK (j : Fin (Module.finrank ℚ K)) : basisK K j ∈ D.OK := by
  rw [basisK, Module.Basis.reindex_apply, integralBasis_apply]
  exact D.coe_mem_OK _

/-- The integral basis, in `B_K`. -/
def dK (j : Fin (Module.finrank ℚ K)) : BKd D :=
  (⟨basisK K j, D.OK_le_BK (basisK_mem_OK D j)⟩ : D.BK)

theorem iotaK_dK (j : Fin (Module.finrank ℚ K)) : iotaK D (dK D j) = Pi.single j 1 := by
  show (basisK K).equivFun (basisK K j) = _
  funext i
  rw [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  simp [eq_comm]

/-- `T_K^∨ = 𝒪_K^⊥ ⊆ B_K^∨`. -/
abbrev TK : Subgroup (PontryaginDual (Multiplicative (BKd D))) := Tperp (dK D)

theorem coords_int_iff (x : BKd D) :
    (∀ j, ∃ m : ℤ, iotaK D x j = m) ↔ x.toK ∈ D.OK := by
  constructor
  · intro h
    choose m hm using h
    have hx : x.toK = ∑ j, (m j : ℚ) • basisK K j := by
      rw [← (basisK K).sum_equivFun x.toK]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hm j]; rfl
    rw [hx]
    refine Submodule.sum_mem _ fun j _ => ?_
    have : (m j : ℚ) • basisK K j = (m j : 𝓞 K) • basisK K j := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rw [this]
    exact Submodule.smul_mem _ _ (basisK_mem_OK D j)
  · intro h j
    obtain ⟨o, ho⟩ := (D.mem_OK_iff).mp h
    refine ⟨(RingOfIntegers.basis K).repr o
      ((Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis (integralBasis K)).symm).symm j),
      ?_⟩
    show (basisK K).equivFun x.toK j = _
    rw [← ho, Module.Basis.equivFun_apply, basisK, Module.Basis.repr_reindex_apply]
    simp

/-- **`T_K^∨` is the annihilator of `𝒪_K`.** -/
theorem mem_TK_iff (χ : PontryaginDual (Multiplicative (BKd D))) :
    χ ∈ TK D ↔ ∀ x : BKd D, x.toK ∈ D.OK → χ (Multiplicative.ofAdd x) = 1 := by
  rw [mem_Tperp_iff (iotaK_dK D) (iotaK_injective D)]
  exact forall_congr' fun x => by rw [coords_int_iff]

/-- **Theorem `zassenhaus-realisation`, topological half.** `B_K^∨` is a compact connected
Hausdorff group; `T_K^∨ = 𝒪_K^⊥` is a delta-subgroup with `B_K^∨/T_K^∨ ≅ (ℝ/ℤ)^[K:ℚ]`; the
diagonal `𝒪_K = ℤ^[K:ℚ]` has dense projection into `T_K^∨`; and
`(T_K^∨ × ℝ^[K:ℚ])/𝒪_K ≅ B_K^∨`, the kernel of `(δ, x) ↦ δ · exp_a(x)` being the diagonal. -/
theorem zassenhaus_topological :
    CompactSpace (PontryaginDual (Multiplicative (BKd D))) ∧
    ConnectedSpace (PontryaginDual (Multiplicative (BKd D))) ∧
    T2Space (PontryaginDual (Multiplicative (BKd D))) ∧
    (∀ χ, χ ∈ TK D ↔ ∀ x : BKd D, x.toK ∈ D.OK → χ (Multiplicative.ofAdd x) = 1) ∧
    IsDelta (TK D) (Module.finrank ℚ K) ∧
    Dense (Set.range fun m : Fin (Module.finrank ℚ K) → ℤ =>
      (⟨expA (iotaK D) (castZ m), expA_castZ_mem (iotaK_dK D) m⟩ : TK D)) ∧
    (∀ p : TK D × Multiplicative (Fin (Module.finrank ℚ K) → ℝ),
      resol (iotaK D) (dK D) p = 1 ↔ ∃ m : Fin (Module.finrank ℚ K) → ℤ, p.2 = castZ m ∧
        (p.1 : PontryaginDual (Multiplicative (BKd D))) = (expA (iotaK D) (castZ m))⁻¹) ∧
    Nonempty ((TK D × Multiplicative (Fin (Module.finrank ℚ K) → ℝ)) ⧸
      (resol (iotaK D) (dK D)).ker ≃ₜ* PontryaginDual (Multiplicative (BKd D))) := by
  have : DiscreteTopology (PontryaginDual (PontryaginDual (Multiplicative (BKd D)))) :=
    discreteTopology_dual
  exact ⟨inferInstance, connectedSpace_of_rank (iotaG_injective (iotaK_injective D)),
    inferInstance, mem_TK_iff D, Tperp_isDelta (iotaK_dK D) (iotaK_injective D),
    dense_diag (iotaK_dK D) (iotaK_injective D), ker_resolution (iotaK_dK D),
    ⟨resolutionEquiv (iotaK_dK D) (iotaK_injective D)⟩⟩

end AdelicToriLean
