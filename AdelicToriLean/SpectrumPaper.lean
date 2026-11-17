import AdelicToriLean.SpectrumResolution
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The periodic factor `L_B` and the paper-facing Theorem `spectrum-resolutions`

General facts about `L = (C ⊕ B) / {(α z, -j z)}` (with `j` injective):

* `isClosed_S`, `t2Space_L`: `L` is Hausdorff;
* `ιC : C → L`, `c ↦ [c, 0]`: injective (`ιC_injective`), open image (`isOpen_range_ιC`), compact
  image when `C` is compact (`isCompact_range_ιC`);
* `exact_L`: `0 → C → L → B/ℤⁿ → 0` is exact;
* `periodic_L`: if `B/ℤⁿ` is torsion and `C` compact, every element of `L` lies in a compact open
  subgroup (`L` is periodic).

Paper-facing (with `C'`, `B ⊆ ℚⁿ`):

* `spectrum_of_resolutions`: if `G ≅ (C' × ℝⁿ)/ℤⁿ` then `G ≅ (L_B × ℝⁿ)/B`.
-/

open Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace AdelicToriLean

namespace Spectrum

variable {C Z B V : Type*} [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
  [AddCommGroup Z] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  (α : Z →+ C) (j : Z →+ B)

/-- `{(α z, -j z)}` is closed in `C × B` (`C` Hausdorff, `B` discrete, `j` injective). -/
theorem isClosed_S [T2Space C] (hj : Function.Injective j) : IsClosed (S α j : Set (C × B)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  rintro ⟨c, b⟩ hcb
  -- inside the open slice `C × {b}`, `S` has at most the one point `(α z₀, b)`
  by_cases hb : ∃ z, -j z = b
  · obtain ⟨z₀, hz₀⟩ := hb
    have hne : c ≠ α z₀ := by
      rintro rfl; exact hcb ⟨z₀, by simp [hz₀]⟩
    refine ⟨{α z₀}ᶜ ×ˢ {b}, ?_, isClosed_singleton.isOpen_compl.prod (isOpen_discrete _),
      ⟨hne, rfl⟩⟩
    rintro ⟨c', b'⟩ ⟨hc', hb'⟩ ⟨z, hz⟩
    simp only [Set.mem_singleton_iff] at hb'
    simp only [AddMonoidHom.prod_apply, AddMonoidHom.neg_apply, Prod.mk.injEq] at hz
    have : z = z₀ := hj (neg_injective (hz.2.trans (hb'.trans hz₀.symm)))
    subst this
    exact hc' hz.1.symm
  · refine ⟨Set.univ ×ˢ {b}, ?_, isOpen_univ.prod (isOpen_discrete _), ⟨trivial, rfl⟩⟩
    rintro ⟨c', b'⟩ ⟨-, hb'⟩ ⟨z, hz⟩
    simp only [Set.mem_singleton_iff] at hb'
    simp only [AddMonoidHom.prod_apply, AddMonoidHom.neg_apply, Prod.mk.injEq] at hz
    exact hb ⟨z, hz.2.trans hb'⟩

/-- **`L_B` is Hausdorff.** -/
theorem t2Space_L [T2Space C] (hj : Function.Injective j) : T2Space (L α j) := by
  have : IsClosed (S α j : Set (C × B)) := isClosed_S α j hj
  infer_instance

/-- `ι_C : C → L`, `c ↦ [c, 0]`. -/
def ιC : C →+ L α j := (QuotientAddGroup.mk' (S α j)).comp (AddMonoidHom.inl C B)

theorem ιC_injective (hj : Function.Injective j) : Function.Injective (ιC α j) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).mp hc
  simp only [AddMonoidHom.prod_apply, AddMonoidHom.neg_apply, AddMonoidHom.inl_apply,
    Prod.mk.injEq, neg_eq_zero] at hz
  have : z = 0 := hj (by rw [hz.2, map_zero])
  rw [← hz.1, this, map_zero]

theorem continuous_ιC : Continuous (ιC α j) :=
  continuous_quot_mk.comp (continuous_id.prodMk continuous_const)

/-- `C` is an open subgroup of `L`. -/
theorem isOpen_range_ιC : IsOpen (Set.range (ιC α j)) := by
  have : Set.range (ιC α j) = (QuotientAddGroup.mk : C × B → L α j) '' (Set.univ ×ˢ {0}) := by
    ext x; constructor
    · rintro ⟨c, rfl⟩; exact ⟨(c, 0), ⟨trivial, rfl⟩, rfl⟩
    · rintro ⟨⟨c, b⟩, ⟨-, hb⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at hb; subst hb
      exact ⟨c, rfl⟩
  rw [this]
  exact QuotientAddGroup.isOpenMap_coe (N := S α j) _ (isOpen_univ.prod (isOpen_discrete _))

/-- `C` is a compact subgroup of `L` when `C` is compact. -/
theorem isCompact_range_ιC [CompactSpace C] : IsCompact (Set.range (ιC α j)) :=
  isCompact_range (continuous_ιC α j)

/-- `L → B / ℤⁿ`, `[c, b] ↦ b + ℤⁿ`. -/
def toQuotB : L α j →+ B ⧸ j.range :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' j.range).comp (AddMonoidHom.snd C B)) (by
    rintro _ ⟨z, rfl⟩
    rw [AddMonoidHom.mem_ker]
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.prod_apply,
      AddMonoidHom.coe_snd, AddMonoidHom.neg_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
    exact ⟨-z, by simp⟩)

/-- **The exact sequence** `0 → C → L → B/ℤⁿ → 0`. -/
theorem exact_L (hj : Function.Injective j) :
    Function.Injective (ιC α j) ∧ Function.Surjective (toQuotB α j) ∧
      (toQuotB α j).ker = (ιC α j).range := by
  refine ⟨ιC_injective α j hj, ?_, ?_⟩
  · intro y
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact ⟨QuotientAddGroup.mk (0, b), rfl⟩
  · ext l
    obtain ⟨⟨c, b⟩, rfl⟩ := QuotientAddGroup.mk_surjective l
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro h
      obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).mp h
      simp only [AddMonoidHom.coe_snd] at hz
      refine ⟨c + α z, ?_⟩
      show (QuotientAddGroup.mk (c + α z, 0) : L α j) = QuotientAddGroup.mk (c, b)
      rw [QuotientAddGroup.eq]
      exact ⟨-z, by ext <;> simp [hz]⟩
    · rintro ⟨c', hc'⟩
      rw [← hc']
      show (QuotientAddGroup.mk (0 : B) : B ⧸ j.range) = 0
      rfl

omit [IsTopologicalAddGroup C] in
theorem coe_range_ιC : (((ιC α j).range : AddSubgroup (L α j)) : Set (L α j)) =
    Set.range (ιC α j) :=
  AddMonoidHom.coe_range _

/-- An element of a finite-order class modulo the compact open subgroup `C` lies in a compact
open subgroup. -/
theorem mem_compact_open [CompactSpace C] (l : L α j) {d : ℕ} (hd : 0 < d)
    (hdl : d • l ∈ (ιC α j).range) :
    ∃ K : AddSubgroup (L α j), IsCompact (K : Set (L α j)) ∧ IsOpen (K : Set (L α j)) ∧ l ∈ K := by
  let H : AddSubgroup (L α j) := (ιC α j).range
  have hHopen : IsOpen (H : Set (L α j)) := by
    rw [coe_range_ιC]; exact isOpen_range_ιC α j
  have hHcpt : IsCompact (H : Set (L α j)) := by
    rw [coe_range_ιC]; exact isCompact_range_ιC α j
  let K : AddSubgroup (L α j) := H ⊔ AddSubgroup.zmultiples l
  have hKeq : (K : Set (L α j)) =
      ⋃ k ∈ Finset.range d, (fun x => (k : ℤ) • l + x) '' (H : Set (L α j)) := by
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
  refine ⟨K, ?_, AddSubgroup.isOpen_mono le_sup_left hHopen,
    AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples l)⟩
  rw [hKeq]
  exact (Finset.range d).isCompact_biUnion fun k _ =>
    hHcpt.image (continuous_const.add continuous_id)

/-- **`L_B` is periodic**: every element lies in a compact open subgroup, provided `C` is compact
and `B / ℤⁿ` is torsion. -/
theorem periodic_L [CompactSpace C] (hj : Function.Injective j)
    (htor : ∀ b : B, ∃ d : ℕ, 0 < d ∧ d • b ∈ j.range) (l : L α j) :
    ∃ K : AddSubgroup (L α j), IsCompact (K : Set (L α j)) ∧ IsOpen (K : Set (L α j)) ∧ l ∈ K := by
  obtain ⟨⟨c, b⟩, rfl⟩ := QuotientAddGroup.mk_surjective l
  obtain ⟨d, hd, hdb⟩ := htor b
  refine mem_compact_open α j _ hd ?_
  have hmem : toQuotB α j (d • (QuotientAddGroup.mk (c, b) : L α j)) = 0 := by
    rw [map_nsmul]
    show d • (QuotientAddGroup.mk b : B ⧸ j.range) = 0
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hdb
  have := (exact_L α j hj).2.2
  rw [← AddMonoidHom.mem_ker, this] at hmem
  exact hmem

end Spectrum

/-! ### Paper-facing statement, `C'` and `ℤⁿ ⊆ B ⊆ ℚⁿ` -/

/-- `B` with the discrete topology. -/
def DiscreteB {n : ℕ} (B : AddSubgroup (Fin n → ℚ)) : Type := B

instance {n : ℕ} (B : AddSubgroup (Fin n → ℚ)) : AddCommGroup (DiscreteB B) :=
  inferInstanceAs (AddCommGroup B)

instance {n : ℕ} (B : AddSubgroup (Fin n → ℚ)) : TopologicalSpace (DiscreteB B) := ⊥

instance {n : ℕ} (B : AddSubgroup (Fin n → ℚ)) : DiscreteTopology (DiscreteB B) := ⟨rfl⟩

variable {n : ℕ} (B : AddSubgroup (Fin n → ℚ)) (hZB : ∀ z : Fin n → ℤ, (fun i => (z i : ℚ)) ∈ B)

/-- `ℤⁿ ⊆ B`. -/
def jB : (Fin n → ℤ) →+ DiscreteB B where
  toFun z := ⟨fun i => (z i : ℚ), hZB z⟩
  map_zero' := Subtype.ext (funext fun i => by simp only [Pi.zero_apply, Int.cast_zero]; rfl)
  map_add' z w := Subtype.ext (funext fun i => by simp only [Pi.add_apply, Int.cast_add]; rfl)

/-- `B ⊆ ℝⁿ`. -/
def rB : DiscreteB B →+ (Fin n → ℝ) where
  toFun b i := ((Subtype.val (b : B)) i : ℝ)
  map_zero' := by
    funext i
    show ((((0 : B) : Fin n → ℚ) i : ℚ) : ℝ) = 0
    simp
  map_add' b c := by
    funext i
    show (((Subtype.val ((b + c : DiscreteB B) : B)) i : ℚ) : ℝ) =
      (((Subtype.val (b : B)) i : ℚ) : ℝ) + (((Subtype.val (c : B)) i : ℚ) : ℝ)
    have hb : (Subtype.val ((b + c : DiscreteB B) : B)) i =
        (Subtype.val (b : B)) i + (Subtype.val (c : B)) i := rfl
    exact (congrArg (fun q : ℚ => (q : ℝ)) hb).trans (Rat.cast_add _ _)

/-- `ℤⁿ ⊆ ℝⁿ`. -/
def epsZ : (Fin n → ℤ) →+ (Fin n → ℝ) where
  toFun z i := (z i : ℝ)
  map_zero' := by funext i; simp
  map_add' z w := by funext i; simp

theorem rB_comp_jB : (rB B).comp (jB B hZB) = epsZ := by
  ext z i
  show ((((Pi.single z (1 : ℤ) : Fin n → ℤ) i : ℚ)) : ℝ) = (((Pi.single z (1 : ℤ) : Fin n → ℤ) i : ℝ))
  push_cast; rfl

theorem jB_injective : Function.Injective (jB B hZB) := by
  intro z w h
  funext i
  have := congrFun (congrArg Subtype.val h) i
  exact_mod_cast (show ((z i : ℤ) : ℚ) = (w i : ℚ) from this)

/-- A topological additive isomorphism, written multiplicatively. -/
def toMultiplicativeEquiv {X Y : Type*} [AddGroup X] [AddGroup Y] [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ+ Y) : Multiplicative X ≃ₜ* Multiplicative Y where
  toMulEquiv := AddEquiv.toMultiplicative f.toAddEquiv
  continuous_toFun := f.continuous
  continuous_invFun := f.symm.continuous

/-- **Theorem `spectrum-resolutions`.** Let `C'` be a topological group and `α : ℤⁿ → C'`, and
suppose `G ≅ (C' × ℝⁿ)/ℤⁿ`, `ℤⁿ` embedded by `z ↦ (α z, z)`. If `ℤⁿ ⊆ B ⊆ ℚⁿ`, then
`G ≅ (L_B × ℝⁿ)/B`, where `L_B = C' ⊕_{ℤⁿ} B` is the pushout. -/
theorem spectrum_of_resolutions {C' : Type*} [AddCommGroup C'] [TopologicalSpace C']
    [IsTopologicalAddGroup C'] (α : (Fin n → ℤ) →+ C') {G : Type*} [CommGroup G]
    [TopologicalSpace G]
    (e : G ≃ₜ* Multiplicative (Spectrum.G0 α (epsZ (n := n)))) :
    Nonempty (G ≃ₜ* Multiplicative (Spectrum.Dq α (jB B hZB) (rB B))) := by
  let f := Spectrum.spectrumEquiv α epsZ (jB B hZB) (rB B) (rB_comp_jB B hZB)
  exact ⟨e.trans (toMultiplicativeEquiv f.symm)⟩

/-- `B / ℤⁿ` is torsion for `ℤⁿ ⊆ B ⊆ ℚⁿ`. -/
theorem torsion_B (b : DiscreteB B) : ∃ d : ℕ, 0 < d ∧ d • b ∈ (jB B hZB).range := by
  set v : Fin n → ℚ := Subtype.val (b : B)
  refine ⟨∏ i, (v i).den, Finset.prod_pos fun i _ => (v i).den_pos, ?_⟩
  refine ⟨fun i => ((∏ k, (v k).den : ℕ) : ℤ) * (v i).num / (v i).den, ?_⟩
  apply Subtype.ext
  funext i
  show (((((∏ k, (v k).den : ℕ) : ℤ) * (v i).num / (v i).den : ℤ)) : ℚ) =
    (Subtype.val (((∏ k, (v k).den) • b : DiscreteB B) : B)) i
  have hsmul : (Subtype.val (((∏ k, (v k).den) • b : DiscreteB B) : B)) i =
      ((∏ k, (v k).den : ℕ) : ℚ) * v i := by
    show ((∏ k, (v k).den) • v) i = _
    rw [Pi.smul_apply, nsmul_eq_mul]
  rw [hsmul]
  have hdvd : ((v i).den : ℤ) ∣ ((∏ k, (v k).den : ℕ) : ℤ) * (v i).num :=
    dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))) _
  rw [Int.cast_div hdvd (by exact_mod_cast (v i).den_nz), Int.cast_mul, Int.cast_natCast]
  conv_rhs => rw [← Rat.num_div_den (v i)]
  field_simp
  norm_cast

/-- **`L_B` is a Hausdorff group** (`C'` Hausdorff). -/
theorem t2Space_LB {C' : Type*} [AddCommGroup C'] [TopologicalSpace C'] [IsTopologicalAddGroup C']
    [T2Space C'] (α : (Fin n → ℤ) →+ C') : T2Space (Spectrum.L α (jB B hZB)) :=
  Spectrum.t2Space_L α _ (jB_injective B hZB)

/-- **The exact sequence** `0 → C' → L_B → B/ℤⁿ → 0`. -/
theorem exact_LB {C' : Type*} [AddCommGroup C'] [TopologicalSpace C'] [IsTopologicalAddGroup C']
    (α : (Fin n → ℤ) →+ C') :
    Function.Injective (Spectrum.ιC α (jB B hZB)) ∧
      Function.Surjective (Spectrum.toQuotB α (jB B hZB)) ∧
      (Spectrum.toQuotB α (jB B hZB)).ker = (Spectrum.ιC α (jB B hZB)).range :=
  Spectrum.exact_L α _ (jB_injective B hZB)

/-- **`L_B` is periodic** (`C'` compact): `C'` is a compact open subgroup of `L_B` and every element
of `L_B` lies in a compact open subgroup. -/
theorem periodic_LB {C' : Type*} [AddCommGroup C'] [TopologicalSpace C'] [IsTopologicalAddGroup C']
    [CompactSpace C'] (α : (Fin n → ℤ) →+ C') :
    IsCompact (Set.range (Spectrum.ιC α (jB B hZB))) ∧
      IsOpen (Set.range (Spectrum.ιC α (jB B hZB))) ∧
      ∀ l : Spectrum.L α (jB B hZB), ∃ K : AddSubgroup (Spectrum.L α (jB B hZB)),
        IsCompact (K : Set (Spectrum.L α (jB B hZB))) ∧
          IsOpen (K : Set (Spectrum.L α (jB B hZB))) ∧ l ∈ K :=
  ⟨Spectrum.isCompact_range_ιC α _, Spectrum.isOpen_range_ιC α _,
    Spectrum.periodic_L α _ (jB_injective B hZB) (torsion_B B hZB)⟩

end AdelicToriLean
