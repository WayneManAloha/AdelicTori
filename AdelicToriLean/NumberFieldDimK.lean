import AdelicToriLean.DimLattice
import AdelicToriLean.NumberFieldDim
import AdelicToriLean.ZassenhausRealisation

/-!
# Theorem `nonarchimedean-line-number-field`: `dim_n K = 1`

A group of integers of `K` (`IsGroupOfIntegers`): `𝒪_K ⊆ B ⊆ K` (as `ℤ`-modules), `B` not finitely
generated (no free summands; a finitely generated torsion-free group is free), and every
endomorphism of `B` is multiplication by a unique element of `𝒪_K`. For such `B`, with coordinates
in an integral basis, `ι⁻¹(ℤⁿ) = 𝒪_K` (`mem_FlatB`) and `dim_n(B^∨) = dim_n(B/𝒪_K)`.

* `one_le_dimN_B`: every group of integers has `dim_n(B^∨) ≥ 1`;
* `dimN_BK`: `dim_n(B_K^∨) = 1`, and `B_K` is a group of integers (`isGroupOfIntegers_BK`);
* `dimNK_eq_one`: `dim_n K := min { dim_n(B^∨) : B a group of integers of K } = 1`.
-/

open NumberField

noncomputable section

namespace AdelicToriLean

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

/-- Integral-basis coordinates are integral exactly on `𝒪_K`. -/
theorem intCoords_iff (x : K) :
    (∀ j, ∃ m : ℤ, (basisK K).equivFun x j = m) ↔ x ∈ D.OK := by
  constructor
  · intro h
    choose m hm using h
    have hx : x = ∑ j, (m j : ℚ) • basisK K j := by
      rw [← (basisK K).sum_equivFun x]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hm j]
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
    rw [← ho, Module.Basis.equivFun_apply, basisK, Module.Basis.repr_reindex_apply]
    simp

/-- Coordinates on a subgroup `B ⊆ K`. -/
def iotaB (B : Submodule ℤ K) : B →+ (Fin (Module.finrank ℚ K) → ℚ) where
  toFun x := (basisK K).equivFun (x : K)
  map_zero' := by simp
  map_add' x y := by simp

theorem mem_FlatB (B : Submodule ℤ K) (x : B) : x ∈ Flat (iotaB B) ↔ (x : K) ∈ D.OK :=
  intCoords_iff D x

/-- **Group of integers of `K`.** -/
def IsGroupOfIntegers (B : Submodule ℤ K) : Prop :=
  D.OZ ≤ B ∧ ¬ Module.Finite ℤ B ∧ ∀ f : B →+ B, ∃! o : 𝓞 K, ∀ x : B, (f x : K) = (o : K) * x

/-- For `𝒪_K ⊆ B` not finitely generated, `B/𝒪_K` is infinite. -/
theorem infinite_quot (B : Submodule ℤ K) (hOB : D.OZ ≤ B) (hB : ¬ Module.Finite ℤ B) :
    Infinite (B ⧸ Flat (iotaB B)) := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  set N := Nat.card (B ⧸ Flat (iotaB B))
  have hN : N ≠ 0 := Nat.card_pos.ne'
  apply hB
  refine (D.sandwich_free B hOB N hN fun x hx => ?_).2.1
  have h1 : N • ((⟨x, hx⟩ : B) : B ⧸ Flat (iotaB B)) = 0 := card_nsmul_eq_zero'
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, mem_FlatB D] at h1
  simpa [nsmul_eq_mul] using h1

/-- **Lower bound**: every group of integers has `dim_n(B^∨) ≥ 1`. -/
theorem one_le_dimN_B {B : Submodule ℤ K} (hB : IsGroupOfIntegers D B) :
    1 ≤ dimN (B ⧸ Flat (iotaB B)) :=
  one_le_dimN _ (infinite_quot D B hB.1 hB.2.1)

/-- `B_K` as a `ℤ`-submodule. -/
abbrev BKZ : Submodule ℤ K := D.BK.restrictScalars ℤ

/-- `B_K / 𝒪_K` in the two presentations. -/
def quotBKEquiv : (BKZ D ⧸ Flat (iotaB (BKZ D))) ≃+ TKq D :=
  QuotientAddGroup.congr _ _
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
    (by
      ext x
      simp only [AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (mem_FlatB D _ y).mp hy
      · intro hx
        exact ⟨⟨x.1, x.2⟩, (mem_FlatB D _ _).mpr hx, rfl⟩)

/-- **`dim_n(B_K^∨) = 1`.** -/
theorem dimN_BK : dimN (BKZ D ⧸ Flat (iotaB (BKZ D))) = 1 := by
  rw [dimN_congr (quotBKEquiv D)]
  exact dimN_TK D

/-- `B_K` is a group of integers. -/
theorem isGroupOfIntegers_BK : IsGroupOfIntegers D (BKZ D) := by
  refine ⟨fun x hx => D.OK_le_BK hx, fun hfin => ?_, fun f => ?_⟩
  · -- a finitely generated `B` has finite `B/𝒪_K`, so `dim_n = 0`
    have : Module.Finite ℤ (BKZ D ⧸ Flat (iotaB (BKZ D))) :=
      Module.Finite.of_surjective (QuotientAddGroup.mk' _).toIntLinearMap
        (QuotientAddGroup.mk'_surjective _)
    have htor : Module.IsTorsion ℤ (BKZ D ⧸ Flat (iotaB (BKZ D))) := by
      intro y
      induction y using QuotientAddGroup.induction_on with | H a => ?_
      obtain ⟨m, hm, hma⟩ := torsion_Flat (iotaB (BKZ D)) a
      refine ⟨⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm.ne')⟩, ?_⟩
      simp only [Submonoid.mk_smul, natCast_zsmul]; exact hma
    have := Module.finite_of_fg_torsion _ htor
    have h0 := (dimN_eq_zero_iff (iotaB (BKZ D))).mpr this
    rw [dimN_BK] at h0
    exact one_ne_zero h0
  · exact end_eq_mul D f

/-- **`dim_n K`**: the least `dim_n(B^∨)` over groups of integers `B` of `K`. -/
def dimNK : ℕ := sInf {d | ∃ B : Submodule ℤ K, IsGroupOfIntegers D B ∧
  dimN (B ⧸ Flat (iotaB B)) = d}

/-- **Theorem `nonarchimedean-line-number-field`: `dim_n K = 1`.** -/
theorem dimNK_eq_one : dimNK D = 1 := by
  have hmem : 1 ∈ {d | ∃ B : Submodule ℤ K, IsGroupOfIntegers D B ∧
      dimN (B ⧸ Flat (iotaB B)) = d} := ⟨BKZ D, isGroupOfIntegers_BK D, dimN_BK D⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨1, hmem⟩
  rintro d ⟨B, hB, rfl⟩
  exact one_le_dimN_B D hB

end AdelicToriLean
