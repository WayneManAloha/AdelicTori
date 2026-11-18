import AdelicToriLean.AdelicTorusProps
import AdelicToriLean.AdelicLieAlgebra
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# The canonical `ℤ̂`-action on a profinite abelian group

* `iZ : ℤ →+ ℤ̂`, `denseRange_iZ`: `ℤ` is dense in `ℤ̂`;
* `dvd_of_iZ_mem`: `dℤ̂ ∩ ℤ = dℤ`; `isOpen_nsmul`: `dℤ̂` is open;
* `exists_zhatHom`: for `P` compact, Hausdorff, totally disconnected abelian and `x ∈ P` there is a
  continuous homomorphism `f : ℤ̂ → P` with `f 1 = x` (`z ↦ z · x`), unique by density.
-/

open Topology Filter IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

noncomputable section

namespace AdelicToriLean

instance : TotallyDisconnectedSpace ZHat :=
  totallyDisconnected_of_injective continuous_subtype_val Subtype.val_injective

/-- `1 ∈ ℤ̂`. -/
def oneZ : ZHat := ⟨1, by simpa using algebraMap_int_mem_ZHat 1⟩

/-- `ℤ → ℤ̂`. -/
def iZ : ℤ →+ ZHat := zmultiplesHom ZHat oneZ

theorem coe_iZ (m : ℤ) : ((iZ m : ZHat) : QHat) = algebraMap ℚ QHat (m : ℚ) := by
  simp [iZ, oneZ, map_intCast]

theorem iZ_one : iZ 1 = oneZ := by simp [iZ]

theorem coe_nsmul (d : ℕ) (w : ZHat) : ((d • w : ZHat) : QHat) = algebraMap ℚ QHat (d : ℚ) * w := by
  rw [AddSubgroup.coe_nsmul, nsmul_eq_mul, map_natCast]

/-- `dℤ̂ ∩ ℤ = dℤ`. -/
theorem dvd_of_iZ_mem {d : ℕ} (hd : 0 < d) {m : ℤ} {w : ZHat} (h : iZ m = d • w) :
    (d : ℤ) ∣ m := by
  have hq : algebraMap ℚ QHat ((m : ℚ) / d) = w := by
    have h' := congrArg (fun y : ZHat => (y : QHat)) h
    simp only [coe_iZ, coe_nsmul] at h'
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [div_eq_mul_inv, map_mul, h', mul_comm, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hd', map_one, one_mul]
  have hden := rat_mem_ZHat (hq ▸ w.2)
  refine ⟨((m : ℚ) / d).num, ?_⟩
  have hnum : (((m : ℚ) / d).num : ℚ) = (m : ℚ) / d := (Rat.den_eq_one_iff _).mp hden
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have : (m : ℚ) = d * (((m : ℚ) / d).num : ℚ) := by rw [hnum]; field_simp
  exact_mod_cast this

/-- **`ℤ` is dense in `ℤ̂`.** -/
theorem denseRange_iZ : DenseRange iZ := by
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro z
  rw [mem_closure_iff]
  intro O hO hzO
  -- an open subgroup `U` with `z + U ⊆ O`
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalAddSubgroup_sub_open_nhds_of_zero
    (hO.preimage (continuous_const_add z)) (by simpa using hzO)
  have : Finite (ZHat ⧸ U.toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen U.toAddSubgroup U.isOpen
  have : U.toAddSubgroup.FiniteIndex := U.toAddSubgroup.finiteIndex_of_finite_quotient
  set k := U.toAddSubgroup.index
  have hk : 0 < k := Nat.pos_of_ne_zero (AddSubgroup.FiniteIndex.index_ne_zero)
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  obtain ⟨r, w, hw, hrw⟩ := exists_rat_add_ZHat (algebraMap ℚ QHat (k : ℚ)⁻¹ * (z : QHat))
  set w' : ZHat := ⟨w, hw⟩
  -- `z = k r + k w`
  have hz : (z : QHat) = algebraMap ℚ QHat (k * r) + ((k • w' : ZHat) : QHat) := by
    rw [coe_nsmul, map_mul, ← mul_add]
    show _ = _ * (_ + w)
    rw [← hrw, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hk', map_one, one_mul]
  have hkr : algebraMap ℚ QHat (k * r) ∈ ZHat := by
    have : algebraMap ℚ QHat (k * r) = (z : QHat) - ((k • w' : ZHat) : QHat) := by
      rw [hz]; ring
    rw [this]; exact ZHat.sub_mem z.2 (k • w').2
  have hden := rat_mem_ZHat hkr
  set m := ((k : ℚ) * r).num
  have hm : ((m : ℤ) : ℚ) = k * r := (Rat.den_eq_one_iff _).mp hden
  have hmem : k • w' ∈ U.toAddSubgroup := AddSubgroup.nsmul_index_mem _ _
  have this : iZ m = z - k • w' := by
    apply Subtype.ext
    rw [coe_iZ, hm, AddSubgroup.coe_sub, hz]; ring
  have h2 : iZ m - z ∈ (U : Set ZHat) := by
    rw [this, sub_sub_cancel_left]
    exact U.toAddSubgroup.neg_mem hmem
  refine ⟨iZ m, ?_, ⟨m, rfl⟩⟩
  simpa using hU h2

/-- `dℤ̂` as an additive subgroup. -/
def nsmulZ (d : ℕ) : AddSubgroup ZHat := (nsmulAddMonoidHom (α := ZHat) d).range

theorem mem_nsmulZ {d : ℕ} {y : ZHat} : y ∈ nsmulZ d ↔ ∃ w, d • w = y := by
  simp [nsmulZ]

theorem isClosed_nsmulZ (d : ℕ) : IsClosed (nsmulZ d : Set ZHat) := by
  have : (nsmulZ d : Set ZHat) = Set.range (fun w : ZHat => d • w) := by
    ext y; simp [nsmulZ]
  rw [this]
  exact (isCompact_range (continuous_id.nsmul d)).isClosed

theorem iZ_mem_coset (d : ℕ) (hd : 0 < d) (m : ℤ) :
    ∃ j : Fin d, iZ m - iZ (j : ℤ) ∈ nsmulZ d := by
  refine ⟨⟨(m % d).toNat, ?_⟩, ?_⟩
  · have h1 := Int.emod_lt_of_pos m (by exact_mod_cast hd : (0 : ℤ) < d)
    have h2 := Int.emod_nonneg m (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0)
    omega
  · have h2 := Int.emod_nonneg m (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0)
    rw [mem_nsmulZ]
    refine ⟨iZ (m / d), ?_⟩
    simp only [Int.toNat_of_nonneg h2, ← map_sub, ← map_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    have := Int.emod_add_mul_ediv m d
    linarith

/-- `dℤ̂` has finite index. -/
theorem nsmulZ_finiteIndex (d : ℕ) (hd : 0 < d) : (nsmulZ d).FiniteIndex := by
  -- the finitely many cosets `j + dℤ̂` cover `ℤ̂`
  have hcov : (⋃ j : Fin d, (fun y => iZ (j : ℤ) + y) '' (nsmulZ d : Set ZHat)) = Set.univ := by
    have hcl : IsClosed (⋃ j : Fin d, (fun y => iZ (j : ℤ) + y) '' (nsmulZ d : Set ZHat)) :=
      isClosed_iUnion_of_finite fun j =>
        (Homeomorph.addLeft (iZ (j : ℤ))).isClosedMap _ (isClosed_nsmulZ d)
    refine Set.eq_univ_of_univ_subset ?_
    rw [← denseRange_iZ.closure_range]
    refine closure_minimal ?_ hcl
    rintro _ ⟨m, rfl⟩
    obtain ⟨j, hj⟩ := iZ_mem_coset d hd m
    exact Set.mem_iUnion.mpr ⟨j, _, hj, add_sub_cancel _ _⟩
  have hfin : Finite (ZHat ⧸ nsmulZ d) := by
    refine Finite.of_surjective (fun j : Fin d => (QuotientAddGroup.mk (iZ (j : ℤ)) :
      ZHat ⧸ nsmulZ d)) ?_
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      have : y ∈ (⋃ j : Fin d, (fun y => iZ (j : ℤ) + y) '' (nsmulZ d : Set ZHat)) := by
        rw [hcov]; trivial
      obtain ⟨j, w, hw, rfl⟩ := Set.mem_iUnion.mp this
      refine ⟨j, ?_⟩
      rw [QuotientAddGroup.eq]
      simpa using hw
  exact (nsmulZ d).finiteIndex_of_finite_quotient

/-- `dℤ̂` is open. -/
theorem isOpen_nsmulZ (d : ℕ) (hd : 0 < d) : IsOpen (nsmulZ d : Set ZHat) := by
  have := nsmulZ_finiteIndex d hd
  exact AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_nsmulZ d)

section Action

variable {P : Type*} [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P]

omit [T2Space P] [TotallyDisconnectedSpace P] in
/-- Integers close in `ℤ̂` give powers in the same coset of an open subgroup. -/
theorem key (x : P) (V : Subgroup P) (hV : IsOpen (V : Set P)) :
    ∃ U : AddSubgroup ZHat, IsOpen (U : Set ZHat) ∧
      ∀ m m' : ℤ, iZ m - iZ m' ∈ U → x ^ (m - m') ∈ V := by
  have : Finite (P ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  have : V.FiniteIndex := V.finiteIndex_of_finite_quotient
  set d := V.index
  have hd : 0 < d := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  refine ⟨nsmulZ d, isOpen_nsmulZ d hd, fun m m' h => ?_⟩
  obtain ⟨w, hw⟩ := mem_nsmulZ.mp h
  rw [← map_sub] at hw
  obtain ⟨c, hc⟩ := dvd_of_iZ_mem hd hw.symm
  rw [hc, zpow_mul]
  exact V.zpow_mem (by simpa using V.pow_index_mem x) c

/-- `ℤ` inside `ℤ̂`. -/
abbrev Zs : AddSubgroup ZHat := iZ.range

instance : Nontrivial QHat :=
  ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun a : QHat => a ((primesEquiv (R := ℤ)).symm
    ⟨2, Nat.prime_two⟩)) h)⟩⟩

theorem iZ_injective : Function.Injective iZ := by
  intro m m' h
  have h' := congrArg (fun y : ZHat => (y : QHat)) h
  simp only [coe_iZ] at h'
  exact_mod_cast (algebraMap ℚ QHat).injective h'

/-- `ℤ ≃ ℤ`-inside-`ℤ̂`. -/
def zsEquiv : ℤ ≃+ Zs := AddMonoidHom.ofInjective iZ_injective

/-- `m ↦ x^m` on `ℤ ⊆ ℤ̂`. -/
def gpow (x : P) (y : Zs) : P := x ^ (zsEquiv.symm y)

omit [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P]
  [TotallyDisconnectedSpace P] in
theorem gpow_iZ (x : P) (m : ℤ) : gpow x ⟨iZ m, m, rfl⟩ = x ^ m := by
  have : (⟨iZ m, m, rfl⟩ : Zs) = zsEquiv m := rfl
  rw [gpow, this, zsEquiv.symm_apply_apply]

theorem isDenseInducing_Zs : IsDenseInducing (Subtype.val : Zs → ZHat) where
  toIsInducing := IsInducing.subtypeVal
  dense := by
    have : Set.range (Subtype.val : Zs → ZHat) = Set.range iZ := by
      ext y; simp
    rw [DenseRange, this]
    exact denseRange_iZ

omit [T2Space P] in
/-- Every open neighbourhood of a point of `P` contains a translate of an open subgroup. -/
theorem exists_coset_sub {c : P} {W : Set P} (hW : W ∈ 𝓝 c) :
    ∃ V : Subgroup P, IsOpen (V : Set P) ∧ ∀ p, c⁻¹ * p ∈ V → p ∈ W := by
  obtain ⟨O, hOW, hO, hcO⟩ := mem_nhds_iff.mp hW
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hO.preimage (continuous_const_mul c)) (by simpa using hcO)
  refine ⟨V.toSubgroup, V.isOpen, ?_⟩
  intro p hp
  exact hOW (by simpa using hV hp)

omit [T2Space P] [TotallyDisconnectedSpace P] in
/-- The values of `gpow x` near `b` lie in one coset of `V`. -/
theorem gpow_near (x : P) (V : Subgroup P) (hV : IsOpen (V : Set P)) (b : ZHat) :
    ∃ a : P, ∃ N ∈ 𝓝 b, ∀ y : Zs, (y : ZHat) ∈ N → a⁻¹ * gpow x y ∈ V := by
  obtain ⟨U, hUo, hU⟩ := key x V hV
  have hN : (fun z => z - b) ⁻¹' (U : Set ZHat) ∈ 𝓝 b :=
    (hUo.preimage (continuous_sub_right b)).mem_nhds (by simp)
  -- a base point
  obtain ⟨y0, hy0⟩ : ∃ y0 : Zs, (y0 : ZHat) ∈ (fun z => z - b) ⁻¹' (U : Set ZHat) :=
    (isDenseInducing_Zs.dense.exists_mem_open (hUo.preimage (continuous_sub_right b))
      ⟨b, by simp⟩).imp fun y hy => hy
  refine ⟨gpow x y0, _, hN, fun y hy => ?_⟩
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (⟨y, rfl⟩ : ∃ y' : Zs, y' = y)
  obtain ⟨⟨_, m0, rfl⟩, hm0⟩ := (⟨y0, rfl⟩ : ∃ y' : Zs, y' = y0)
  rw [← hm] at hy ⊢
  rw [← hm0] at hy0 ⊢
  rw [gpow_iZ, gpow_iZ]
  have hdiff : iZ m - iZ m0 ∈ U := by
    have := U.sub_mem hy hy0
    simpa using this
  have := hU m m0 hdiff
  simpa [zpow_sub, mul_comm] using this

omit [T2Space P] in
theorem tendsto_gpow (x : P) (b : ZHat) :
    ∃ c, Tendsto (gpow x) (comap Subtype.val (𝓝 b)) (𝓝 c) := by
  set F := map (gpow x) (comap (Subtype.val : Zs → ZHat) (𝓝 b))
  have : F.NeBot := (isDenseInducing_Zs.comap_nhds_neBot b).map _
  obtain ⟨c, -, hc⟩ := isCompact_univ.exists_clusterPt (f := F) (le_principal_iff.mpr univ_mem)
  refine ⟨c, fun W hW => ?_⟩
  obtain ⟨V, hVo, hVW⟩ := exists_coset_sub hW
  obtain ⟨a, N, hN, haN⟩ := gpow_near x V hVo b
  set A : Set P := {p | a⁻¹ * p ∈ V}
  have hF : A ∈ F :=
    mem_map.mpr (mem_of_superset (preimage_mem_comap hN) fun y hy => haN y hy)
  have hAo : IsOpen A := hVo.preimage (continuous_const_mul a⁻¹)
  have hAc : IsClosed A := (Subgroup.isClosed_of_isOpen V hVo).preimage (continuous_const_mul a⁻¹)
  have hca : c ∈ A := hAc.closure_eq ▸ hc.mem_closure_of_mem _ hF
  have hsub : A ⊆ W := by
    intro p hp
    apply hVW
    have := V.mul_mem (V.inv_mem hca) hp
    simpa [mul_assoc] using this
  exact mem_of_superset hF hsub

omit [T2Space P] in
theorem continuous_gpow (x : P) : Continuous (gpow x) := by
  rw [continuous_iff_continuousAt]
  intro y W hW
  obtain ⟨V, hVo, hVW⟩ := exists_coset_sub hW
  obtain ⟨U, hUo, hU⟩ := key x V hVo
  rw [Filter.mem_map]
  refine mem_of_superset ((hUo.preimage ((continuous_sub_right (y : ZHat)).comp
    continuous_subtype_val)).mem_nhds
    (show (y : ZHat) - y ∈ (U : Set ZHat) by simp)) ?_
  intro y' hy'
  have hy'' : (y' : ZHat) - y ∈ U := hy'
  obtain ⟨_, m, rfl⟩ := y'
  obtain ⟨_, m0, rfl⟩ := y
  apply hVW
  simp only [gpow_iZ]
  have := hU m m0 hy''
  simpa [zpow_sub, mul_comm] using this

/-- **The canonical `ℤ̂`-action.** For `x` in a profinite abelian group there is a continuous
homomorphism `ℤ̂ → P`, `z ↦ z · x`, sending `1` to `x`. -/
theorem exists_zhatHom (x : P) :
    ∃ f : ContinuousMonoidHom (Multiplicative ZHat) P, f (Multiplicative.ofAdd oneZ) = x := by
  set ext := isDenseInducing_Zs.extend (gpow x)
  have hcont : Continuous ext := isDenseInducing_Zs.continuous_extend (tendsto_gpow x)
  have heq : ∀ y : Zs, ext y = gpow x y :=
    isDenseInducing_Zs.extend_eq (continuous_gpow x)
  have hdr : DenseRange (Subtype.val : Zs → ZHat) := isDenseInducing_Zs.dense
  have hmul : ∀ a b : ZHat, ext (a + b) = ext a * ext b := by
    intro a b
    refine DenseRange.induction_on₂ hdr ?_ (fun y y' => ?_) a b
    · exact isClosed_eq (hcont.comp continuous_add)
        ((hcont.comp continuous_fst).mul (hcont.comp continuous_snd))
    · obtain ⟨_, m, rfl⟩ := y
      obtain ⟨_, m', rfl⟩ := y'
      have e : iZ m + iZ m' = ((⟨iZ (m + m'), m + m', rfl⟩ : Zs) : ZHat) := by simp
      rw [e, heq, heq ⟨iZ m, m, rfl⟩, heq ⟨iZ m', m', rfl⟩, gpow_iZ, gpow_iZ, gpow_iZ,
        zpow_add]
  refine ⟨⟨⟨⟨fun z => ext (Multiplicative.toAdd z), ?_⟩, fun a b => hmul _ _⟩,
    hcont.comp continuous_toAdd⟩, ?_⟩
  · show ext 0 = 1
    rw [show (0 : ZHat) = ((⟨iZ 0, 0, rfl⟩ : Zs) : ZHat) by simp, heq, gpow_iZ, zpow_zero]
  · show ext oneZ = x
    rw [show oneZ = ((⟨iZ 1, 1, rfl⟩ : Zs) : ZHat) by simp [iZ_one], heq, gpow_iZ, zpow_one]

end Action

/-- **`ℤ̂` is topologically generated by `1`.** Continuous homomorphisms `ℤ̂ → H` into a Hausdorff
group agreeing at `1` are equal. -/
theorem zhatHom_ext {H : Type*} [Group H] [TopologicalSpace H] [T2Space H]
    {f g : ContinuousMonoidHom (Multiplicative ZHat) H}
    (h : f (Multiplicative.ofAdd oneZ) = g (Multiplicative.ofAdd oneZ)) : f = g := by
  have hm : ∀ m : ℤ, f (Multiplicative.ofAdd (iZ m)) = g (Multiplicative.ofAdd (iZ m)) := by
    intro m
    rw [show Multiplicative.ofAdd (iZ m) = (Multiplicative.ofAdd oneZ) ^ m by
      simp [iZ, ← ofAdd_zsmul], map_zpow, map_zpow, h]
  ext z
  have hc : Continuous fun a : ZHat => f (Multiplicative.ofAdd a) :=
    f.continuous.comp continuous_ofAdd
  have hc' : Continuous fun a : ZHat => g (Multiplicative.ofAdd a) :=
    g.continuous.comp continuous_ofAdd
  have := congrFun (denseRange_iZ.equalizer hc hc' (funext hm)) (Multiplicative.toAdd z)
  simpa using this

end AdelicToriLean
