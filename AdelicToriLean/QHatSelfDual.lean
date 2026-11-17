import AdelicToriLean.QHatDual
import AdelicToriLean.AdelicModel
import AdelicToriLean.Protorus

/-!
# `ℚ̂ ≅ ℚ̂^∨`

`chi u (x) = e(ψ(u x))`. Main result: `chi_surjective`, every continuous character of `ℚ̂` is
`chi u` for a unique `u` (`chi_injective`).

Proof of surjectivity: the image `H` of `chi` is a subgroup with `H ∩ W = chi(ℤ̂)` compact, where
`W` is the open set of characters with values near `1` on `ℤ̂`; so `H` is locally compact,
hence closed. If `H` were proper, the vendored duality theorem would give `x ≠ 0` with
`ψ(u x) = 0` for all `u`, contradicting `exists_psi_ne_zero`.
-/

open IsDedekindDomain Topology Circle Real

noncomputable section

namespace AdelicToriLean

instance : T2Space (Multiplicative QHat) := inferInstanceAs (T2Space QHat)
instance : LocallyCompactSpace (Multiplicative QHat) := inferInstanceAs (LocallyCompactSpace QHat)

theorem ZHat_mul_mem {u x : QHat} (hu : u ∈ ZHat) (hx : x ∈ ZHat) : u * x ∈ ZHat := by
  rw [mem_ZHat] at hu hx ⊢
  intro v
  exact (v.adicCompletionIntegers ℚ).mul_mem _ _ (hu v) (hx v)

/-- The character `x ↦ e(ψ(u x))` of `ℚ̂`. -/
def chi (u : QHat) : PontryaginDual (Multiplicative QHat) :=
  ⟨{ toFun := fun x => AddCircle.toCircle (psi (u * Multiplicative.toAdd x))
     map_one' := by simp
     map_mul' := fun x y => by simp [mul_add, AddCircle.toCircle_add] },
    AddCircle.continuous_toCircle.comp
      (continuous_psi.comp (continuous_const.mul continuous_id))⟩

theorem chi_apply (u : QHat) (x : Multiplicative QHat) :
    chi u x = AddCircle.toCircle (psi (u * Multiplicative.toAdd x)) := rfl

theorem chi_add (u v : QHat) : chi (u + v) = chi u * chi v := by
  ext x
  simp only [chi_apply, add_mul, map_add, AddCircle.toCircle_add]
  rfl

theorem chi_zero : chi 0 = 1 := by
  ext x; simp [chi_apply]

theorem chi_eq_one_iff (u : QHat) (x : Multiplicative QHat) :
    chi u x = 1 ↔ psi (u * Multiplicative.toAdd x) = 0 := by
  rw [chi_apply, ← AddCircle.toCircle_zero]
  exact (AddCircle.injective_toCircle one_ne_zero).eq_iff

theorem chi_injective : Function.Injective chi := by
  intro u v h
  by_contra hne
  obtain ⟨w, hw⟩ := exists_psi_ne_zero (sub_ne_zero.mpr hne)
  have h1 : chi (u - v) = 1 := by
    rw [show u = (u - v) + v by abel, chi_add] at h
    exact mul_eq_right.mp h
  have := (chi_eq_one_iff (u - v) (Multiplicative.ofAdd w)).mp (by rw [h1]; rfl)
  exact hw this

theorem continuous_chi : Continuous chi := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : QHat × Multiplicative QHat =>
    AddCircle.toCircle (psi (p.1 * Multiplicative.toAdd p.2)))
  exact AddCircle.continuous_toCircle.comp (continuous_psi.comp
    (continuous_fst.mul (continuous_toAdd.comp continuous_snd)))

/-- `ℤ̂` as a subset of `Multiplicative ℚ̂`. -/
def ZHatM : Set (Multiplicative QHat) := Multiplicative.ofAdd '' (ZHat : Set QHat)

theorem mem_ZHatM {x : Multiplicative QHat} : x ∈ ZHatM ↔ Multiplicative.toAdd x ∈ ZHat := by
  constructor
  · rintro ⟨z, hz, rfl⟩; exact hz
  · intro h; exact ⟨_, h, rfl⟩

theorem isCompact_ZHatM : IsCompact ZHatM :=
  isCompact_ZHat.image continuous_ofAdd

/-- Characters with values near `1` on `ℤ̂`. -/
def Wnbhd : Set (PontryaginDual (Multiplicative QHat)) :=
  {χ | Set.MapsTo (ContinuousMonoidHom.toContinuousMap χ) ZHatM (centeredArc (π / 2))}

theorem isOpen_Wnbhd : IsOpen Wnbhd :=
  (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_ZHatM (isOpen_centeredArc (r := π / 2))).preimage
    (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous

theorem one_mem_Wnbhd : (1 : PontryaginDual (Multiplicative QHat)) ∈ Wnbhd := by
  intro x _
  exact ⟨0, by simp [Real.pi_pos], by rw [Circle.exp_zero]; exact (PontryaginDual.one_apply x).symm⟩

theorem chi_mem_Wnbhd_iff (u : QHat) : chi u ∈ Wnbhd ↔ u ∈ ZHat := by
  constructor
  · intro h
    -- the image of `ℤ̂` under `chi u` is a subgroup inside the arc, hence trivial
    let K : Subgroup Circle :=
      { carrier := (fun z : QHat => chi u (Multiplicative.ofAdd z)) '' (ZHat : Set QHat)
        mul_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          refine ⟨a + b, ZHat.add_mem ha hb, ?_⟩
          show chi u (Multiplicative.ofAdd (a + b)) =
            chi u (Multiplicative.ofAdd a) * chi u (Multiplicative.ofAdd b)
          rw [ofAdd_add, map_mul]
        one_mem' := ⟨0, ZHat.zero_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨a, ha, rfl⟩
          refine ⟨-a, ZHat.neg_mem ha, ?_⟩
          show chi u (Multiplicative.ofAdd (-a)) = (chi u (Multiplicative.ofAdd a))⁻¹
          rw [ofAdd_neg, map_inv] }
    have hK := subgroup_le_centeredArc K (by
      rintro _ ⟨z, hz, rfl⟩
      exact h (show Multiplicative.ofAdd z ∈ ZHatM from ⟨z, hz, rfl⟩))
    apply mem_ZHat_of_psi
    intro z hz
    have : chi u (Multiplicative.ofAdd z) ∈ K := ⟨z, hz, rfl⟩
    rw [hK, Subgroup.mem_bot] at this
    exact (chi_eq_one_iff u _).mp this
  · intro hu x hx
    have h0 : chi u x = 1 := by
      rw [chi_eq_one_iff]
      exact psi_ZHat (ZHat_mul_mem hu (mem_ZHatM.mp hx))
    show chi u x ∈ centeredArc (π / 2)
    rw [h0]; exact ⟨0, by simp [Real.pi_pos], by simp⟩

/-- The image of `chi` as a subgroup. -/
def rangeChi : Subgroup (PontryaginDual (Multiplicative QHat)) where
  carrier := Set.range chi
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, chi_add a b⟩
  one_mem' := ⟨0, chi_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    rw [eq_inv_iff_mul_eq_one, ← chi_add, neg_add_cancel, chi_zero]

theorem isClosed_rangeChi : IsClosed (rangeChi : Set (PontryaginDual (Multiplicative QHat))) := by
  -- `rangeChi` is locally compact: `rangeChi ∩ W = chi(ℤ̂)` is a compact neighbourhood of `1`
  let H := rangeChi
  have hcpt : IsCompact (Subtype.val ⁻¹' Wnbhd : Set H) := by
    have himg : (Subtype.val '' (Subtype.val ⁻¹' Wnbhd : Set H)) = chi '' (ZHat : Set QHat) := by
      ext χ
      constructor
      · rintro ⟨⟨_, ⟨u, rfl⟩⟩, hW, rfl⟩
        exact ⟨u, (chi_mem_Wnbhd_iff u).mp hW, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨chi u, ⟨u, rfl⟩⟩, (chi_mem_Wnbhd_iff u).mpr hu, rfl⟩
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]
    exact isCompact_ZHat.image continuous_chi
  have hnhds : (Subtype.val ⁻¹' Wnbhd : Set H) ∈ 𝓝 (1 : H) :=
    (isOpen_Wnbhd.preimage continuous_subtype_val).mem_nhds one_mem_Wnbhd
  have : LocallyCompactSpace H := hcpt.locallyCompactSpace_of_mem_nhds_of_group hnhds
  exact Subgroup.isClosed_of_locallyCompactSpace H

/-- **Self-duality of `ℚ̂`**: every continuous character of `ℚ̂` is `x ↦ e(ψ(u x))`. -/
theorem chi_surjective : Function.Surjective chi := by
  classical
  intro x
  by_contra hx
  have hxH : x ∉ rangeChi := by rintro ⟨a, rfl⟩; exact hx ⟨a, rfl⟩
  set H := rangeChi
  have : IsClosed (H : Set (PontryaginDual (Multiplicative QHat))) := isClosed_rangeChi
  have hne : (QuotientGroup.mk x : PontryaginDual (Multiplicative QHat) ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have hinj := PontryaginDual.eval_injective (PontryaginDual (Multiplicative QHat) ⧸ H)
  have hev : PontryaginDual.eval
      (QuotientGroup.mk x : PontryaginDual (Multiplicative QHat) ⧸ H) ≠ 1 := by
    intro h; apply hne; apply hinj; rw [h, map_one]
  obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual (PontryaginDual (Multiplicative QHat) ⧸ H),
      χ (QuotientGroup.mk x) ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hev (PontryaginDual.ext fun χ => by
      rw [PontryaginDual.eval_apply, hall χ, PontryaginDual.one_apply])
  let ψ' : PontryaginDual (PontryaginDual (Multiplicative QHat)) :=
    ⟨χ.toMonoidHom.comp (QuotientGroup.mk' H), χ.continuous.comp continuous_quot_mk⟩
  have hψH : ∀ u, ψ' (chi u) = 1 := by
    intro u
    show χ (QuotientGroup.mk (chi u)) = 1
    have hmem : chi u ∈ H := Set.mem_range_self u
    rw [(QuotientGroup.eq_one_iff _).mpr hmem, map_one]
  have hψx : ψ' x ≠ 1 := hχ
  obtain ⟨y, hy⟩ := PontryaginDual.eval_surjective (Multiplicative QHat) ψ'
  have hy1 : Multiplicative.toAdd y ≠ 0 := by
    intro h0
    apply hψx
    rw [← hy, show y = 1 from h0, map_one, PontryaginDual.one_apply]
  obtain ⟨w, hw⟩ := exists_psi_ne_zero hy1
  apply hw
  have := hψH w
  rw [← hy, PontryaginDual.eval_apply, chi_eq_one_iff] at this
  rwa [mul_comm] at this

end AdelicToriLean
