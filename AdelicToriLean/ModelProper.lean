import AdelicToriLean.ModelSequence
import AdelicToriLean.RealDual
import AdelicToriLean.AdelicTorus

/-!
# Properness of the sequence and periodicity of `L`

* `mem_compact_open_of_nsmul`: in a topological group with a compact open subgroup `H`, an element
  with a multiple in `H` lies in a compact open subgroup;
* `K0`: the compact open subgroup `ℤ̂ⁿ / C` of `L`; `periodic_modelL`: `L` is periodic;
* `isOpenMap_FMap`: `L × ℝⁿ → G` is open;
* `discrete_range_jMap`: the image of `G^∨` in `L × ℝⁿ` is discrete.
-/

open IsDedekindDomain Topology

noncomputable section

namespace AdelicToriLean

theorem mem_compact_open_of_nsmul {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (H : AddSubgroup X) (hHc : IsCompact (H : Set X))
    (hHo : IsOpen (H : Set X)) (l : X) {d : ℕ} (hd : 0 < d) (hdl : d • l ∈ H) :
    ∃ K : AddSubgroup X, IsCompact (K : Set X) ∧ IsOpen (K : Set X) ∧ l ∈ K := by
  let K : AddSubgroup X := H ⊔ AddSubgroup.zmultiples l
  have hKeq : (K : Set X) = ⋃ k ∈ Finset.range d, (fun x => (k : ℤ) • l + x) '' (H : Set X) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨h, hh, y, hy, rfl⟩ := AddSubgroup.mem_sup.mp hx
      obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      have hdi : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
      have hk0 : 0 ≤ m % (d : ℤ) := Int.emod_nonneg _ hdi
      have hkd : m % (d : ℤ) < d := Int.emod_lt_of_pos _ (by exact_mod_cast hd)
      have hm : m = m / (d : ℤ) * d + m % (d : ℤ) := (Int.emod_add_ediv_mul m d).symm.trans
        (add_comm _ _)
      refine Set.mem_iUnion₂.mpr ⟨(m % (d : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
      refine ⟨h + (m / (d : ℤ)) • (d • l), H.add_mem hh (H.zsmul_mem hdl _), ?_⟩
      show (((m % (d : ℤ)).toNat : ℕ) : ℤ) • l + (h + (m / (d : ℤ)) • (d • l)) = h + m • l
      conv_rhs => rw [hm]
      rw [Int.toNat_of_nonneg hk0, add_zsmul, mul_zsmul, natCast_zsmul]
      abel
    · intro x hx
      obtain ⟨k, -, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hx
      exact K.add_mem (AddSubgroup.mem_sup_right (AddSubgroup.zsmul_mem_zmultiples l k))
        (AddSubgroup.mem_sup_left hy)
  refine ⟨K, ?_, AddSubgroup.isOpen_mono le_sup_left hHo,
    AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples l)⟩
  rw [hKeq]
  exact (Finset.range d).isCompact_biUnion fun k _ =>
    hHc.image (continuous_const.add continuous_id)

variable {n : ℕ} {D : Type*} [CommGroup D] (ι : Additive D →+ (Fin n → ℚ))

theorem isCompact_ZHatn : IsCompact (↑(ZHatn (n := n)) : Set (Fin n → QHat)) := by
  have : (↑(ZHatn (n := n)) : Set (Fin n → QHat)) = Set.univ.pi fun _ => (ZHat : Set QHat) := by
    ext u; simp [mem_ZHatn]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_ZHat

/-- `ℤ̂ⁿ / C ⊆ L`. -/
def K0 : AddSubgroup (ModelL ι) :=
  ((ZHatn (n := n)).addSubgroupOf (Hp (Cm ι))).map (QuotientAddGroup.mk' (Cp (Cm ι)))

theorem isCompact_K0 : IsCompact (K0 ι : Set (ModelL ι)) := by
  have hc : IsCompact (((ZHatn (n := n)).addSubgroupOf (Hp (Cm ι)) : AddSubgroup (Hp (Cm ι))) :
      Set (Hp (Cm ι))) := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    have : Subtype.val '' (((ZHatn (n := n)).addSubgroupOf (Hp (Cm ι)) : AddSubgroup _) :
        Set (Hp (Cm ι))) = (↑(ZHatn (n := n)) : Set (Fin n → QHat)) := by
      ext u
      constructor
      · rintro ⟨h, hh, rfl⟩; exact AddSubgroup.mem_addSubgroupOf.mp hh
      · intro hu
        exact ⟨⟨u, ZHatn_le_perp ι hu⟩, AddSubgroup.mem_addSubgroupOf.mpr hu, rfl⟩
    rw [this]; exact isCompact_ZHatn
  exact hc.image continuous_quot_mk

theorem isOpen_K0 : IsOpen (K0 ι : Set (ModelL ι)) := by
  apply QuotientAddGroup.isOpenMap_coe
  exact isOpen_ZHatn.preimage continuous_subtype_val

/-- **`L` is periodic**: it has the compact open subgroup `ℤ̂ⁿ / C`, and every element lies in a
compact open subgroup. -/
theorem periodic_modelL (l : ModelL ι) :
    ∃ K : AddSubgroup (ModelL ι), IsCompact (K : Set (ModelL ι)) ∧
      IsOpen (K : Set (ModelL ι)) ∧ l ∈ K := by
  obtain ⟨h, rfl⟩ := QuotientAddGroup.mk_surjective l
  have hsa : ∀ i, ∃ r : ℚ, ∃ z ∈ ZHat, (h : Fin n → QHat) i = algebraMap ℚ QHat r + z :=
    fun i => exists_rat_add_ZHat _
  choose r z hz hrz using hsa
  set d : ℕ := ∏ i, (r i).den
  have hd : 0 < d := Finset.prod_pos fun i _ => (r i).pos
  refine mem_compact_open_of_nsmul (K0 ι) (isCompact_K0 ι) (isOpen_K0 ι) _ hd ?_
  refine ⟨d • h, ?_, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf, mem_ZHatn]
  intro i
  have hdi : (r i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨e, he⟩ := hdi
  have hint : ((d : ℚ) * r i) = ((e * (r i).num : ℤ) : ℚ) := by
    rw [he]; push_cast
    rw [show ((r i).den : ℚ) * e * r i = e * ((r i).den * r i) by ring, Rat.den_mul_eq_num]
  show (d • (h : Fin n → QHat)) i ∈ ZHat
  rw [Pi.smul_apply, hrz i, smul_add]
  refine ZHat.add_mem ?_ (AddSubgroup.nsmul_mem _ (hz i) _)
  rw [nsmul_eq_mul, ← map_natCast (algebraMap ℚ QHat), ← map_mul, hint]
  exact algebraMap_int_mem_ZHat _

theorem sigmaCompact_modelL : SigmaCompactSpace (ModelL ι) := by
  have hHc : IsClosed (Hp (Cm ι) : Set (Fin n → QHat)) :=
    AddSubgroup.isClosed_of_isOpen _ (isOpen_perp ι)
  have : SigmaCompactSpace (Hp (Cm ι)) := hHc.sigmaCompactSpace
  rw [← isSigmaCompact_univ_iff, ← (QuotientAddGroup.mk_surjective (s := Cp (Cm ι))).range_eq]
  exact isSigmaCompact_range continuous_quot_mk

/-- **The image of `G^∨` in `L × ℝⁿ` is discrete.** -/
theorem discrete_range_jMap (hZ : ∀ j : Fin n, Pi.single j 1 ∈ Set.range ι) :
    DiscreteTopology (jMap ι hZ).range := by
  set U : Set (ModelL ι × (Fin n → ℝ)) :=
    (K0 ι : Set (ModelL ι)) ×ˢ {x | ∀ i, |x i| < 1 / 2}
  have hU : IsOpen U := (isOpen_K0 ι).prod (by
    have : {x : Fin n → ℝ | ∀ i, |x i| < 1 / 2} = Set.univ.pi fun _ => Set.Ioo (-(1/2) : ℝ) (1/2) := by
      ext x; simp [abs_lt]
    rw [this]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo)
  apply discreteTopology_of_isOpen_singleton_zero
  have hpre : IsOpen ((Subtype.val : (jMap ι hZ).range → ModelL ι × (Fin n → ℝ)) ⁻¹' U) :=
    hU.preimage continuous_subtype_val
  convert hpre using 1
  ext ⟨p, d, rfl⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro h
    have h0 : jMap ι hZ d = 0 := congrArg Subtype.val h
    rw [h0]
    exact ⟨(K0 ι).zero_mem, fun i => by simp⟩
  · rintro ⟨hK, hx⟩
    obtain ⟨y, hy, hye⟩ := AddSubgroup.mem_map.mp hK
    have hdiff : (y : Fin n → QHat) - emb (ι d) ∈ Cm ι := by
      have := (QuotientAddGroup.eq).mp hye
      rw [AddSubgroup.mem_addSubgroupOf] at this
      have h2 := neg_mem this
      convert h2 using 1
      simp [embH]; abel
    have hint : ∀ i, (ι d i).den = 1 := by
      intro i
      apply rat_mem_ZHat
      have hyZ : (y : Fin n → QHat) ∈ ZHatn := AddSubgroup.mem_addSubgroupOf.mp hy
      have := (ZHatn (n := n)).sub_mem hyZ (Cm_le_ZHatn ι hdiff)
      rw [sub_sub_cancel] at this
      exact mem_ZHatn.mp this i
    have hzero : ι d = 0 := by
      funext i
      have hi := hx i
      have : |((ι d i : ℚ) : ℝ)| < 1 / 2 := hi
      have hnum : (ι d i : ℚ) = ((ι d i).num : ℚ) := (Rat.coe_int_num_of_den_eq_one (hint i)).symm
      rw [hnum] at this
      have h' : |((ι d i).num : ℝ)| < 1 / 2 := by exact_mod_cast this
      have : (ι d i).num = 0 := by
        rw [← Int.cast_abs] at h'
        have : |(ι d i).num| < 1 := by
          have : ((|(ι d i).num| : ℤ) : ℝ) < 1 := lt_trans h' (by norm_num)
          exact_mod_cast this
        exact Int.abs_lt_one_iff.mp this
      rw [Pi.zero_apply, hnum, this, Int.cast_zero]
    apply Subtype.ext
    have he : embH ι hZ d = 0 := Subtype.ext (show emb (ι d) = 0 by rw [hzero, map_zero])
    show (QuotientAddGroup.mk (embH ι hZ d), ratReal (ι d)) = (0 : ModelL ι × (Fin n → ℝ))
    rw [he, hzero, map_zero]
    rfl

variable [TopologicalSpace D] [DiscreteTopology D]

/-- **`L × ℝⁿ → (𝔸ⁿ/C)/Λ` is open.** -/
theorem isOpenMap_FMap (hι : Function.Injective ι)
    (hZ : ∀ j : Fin n, Pi.single j 1 ∈ Set.range ι) : IsOpenMap (FMap ι) := by
  have := sigmaCompact_modelL ι
  have : CompactSpace (AdelicTorus ι) := compactSpace_adelicTorus ι
  have : T2Space (Multiplicative (AdelicTorus ι)) :=
    (adelicModelEquiv ι hι hZ).toHomeomorph.symm.t2Space
  have : T2Space (AdelicTorus ι) := inferInstanceAs (T2Space (Multiplicative (AdelicTorus ι)))
  have : BaireSpace (AdelicTorus ι) := BaireSpace.of_t2Space_locallyCompactSpace
  exact AddMonoidHom.isOpenMap_of_sigmaCompact _ (FMap_surjective ι) (continuous_FMap ι)

end AdelicToriLean
