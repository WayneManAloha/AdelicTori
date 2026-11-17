import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# The `p`-adic fractional part

The paper's pairing on `𝔸ⁿ` uses the `p`-adic fractional part `{·}_p : ℚ_p → ℚ_p/ℤ_p ↪ ℚ/ℤ`.
Here it is a continuous additive map `fractP p : ℚ_[p] →+ AddCircle (1 : ℝ)` with

* `fractP_rat`: `fractP p r = r (mod 1)` for `r ∈ ℤ[1/p]`;
* `fractP_eq_zero_iff`: `fractP p x = 0 ↔ x ∈ ℤ_p`;
* `continuous_fractP`.

Construction: `ℤ[1/p] → ℚ_p/ℤ_p` is surjective with kernel `ℤ`, so `ℚ_p/ℤ_p ≅ ℤ[1/p]/ℤ ↪ ℝ/ℤ`.
-/

open Padic

noncomputable section

namespace AdelicToriLean

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ℤ[1/p]` as an additive subgroup of `ℚ`: rationals whose denominator divides a power of `p`. -/
def zInvP : AddSubgroup ℚ where
  carrier := {r | ∃ k : ℕ, r.den ∣ p ^ k}
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, (Rat.add_den_dvd a b).trans (pow_add p k l ▸ mul_dvd_mul hk hl)⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by rintro a ⟨k, hk⟩; exact ⟨k, by simpa using hk⟩

/-- `ℤ_p` as an additive subgroup of `ℚ_p`. -/
abbrev zP : AddSubgroup ℚ_[p] := (PadicInt.subring p).toAddSubgroup

theorem mem_zP {x : ℚ_[p]} : x ∈ zP p ↔ ‖x‖ ≤ 1 := Iff.rfl

/-- A rational of `p`-adic norm `≤ 1` has denominator prime to `p`. -/
theorem not_dvd_den_of_norm_le {r : ℚ} (h : ‖(r : ℚ_[p])‖ ≤ 1) : ¬ p ∣ r.den := by
  intro hd
  have hu := PadicInt.isUnit_den r h
  obtain ⟨k, hk⟩ := hd
  have : IsUnit ((p : ℤ_[p]) * k) := by
    have : ((r.den : ℕ) : ℤ_[p]) = (p : ℤ_[p]) * k := by rw [hk]; push_cast; ring
    rw [← this]; exact hu
  exact PadicInt.p_nonunit (isUnit_of_mul_isUnit_left this)

/-- `ℤ[1/p] ∩ ℤ_p = ℤ`. -/
theorem den_eq_one_of_mem {r : ℚ} (hr : r ∈ zInvP p) (h : ‖(r : ℚ_[p])‖ ≤ 1) : r.den = 1 := by
  obtain ⟨k, hk⟩ := hr
  have hcop : Nat.Coprime r.den (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
      (not_dvd_den_of_norm_le p h))))
  exact Nat.Coprime.eq_one_of_dvd hcop hk

/-- The map `ℤ[1/p] → ℚ_p/ℤ_p`. -/
def toQuot : zInvP p →+ ℚ_[p] ⧸ zP p :=
  (QuotientAddGroup.mk' (zP p)).comp ((Rat.castHom ℚ_[p]).toAddMonoidHom.comp (zInvP p).subtype)

theorem toQuot_surjective : Function.Surjective (toQuot p) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  -- choose `k` with `p^k x ∈ ℤ_p`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖(p : ℚ_[p]) ^ k * x‖ ≤ 1 := by
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    refine ⟨(-x.valuation).toNat, ?_⟩
    rw [norm_mul, norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx, ← zpow_add₀
      (by exact_mod_cast hp.out.ne_zero)]
    apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hp.out.one_lt.le)
    omega
  set y : ℤ_[p] := ⟨(p : ℚ_[p]) ^ k * x, hk⟩
  set m := y.appr k
  refine ⟨⟨(m : ℚ) / p ^ k, k, ?_⟩, ?_⟩
  · have : ((m : ℚ) / p ^ k).den ∣ (p ^ k : ℕ) := by
      have := Rat.den_dvd (m : ℤ) ((p ^ k : ℕ) : ℤ)
      have h2 : (((m : ℚ) / p ^ k).den : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by
        simpa [Rat.divInt_eq_div] using this
      exact Int.natCast_dvd_natCast.mp h2
    exact this
  · simp only [toQuot, AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_div₀, map_natCast, map_pow,
      QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq, mem_zP]
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k y)
    have hp0 : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    have key : -((m : ℚ_[p]) / (p : ℚ_[p]) ^ k) + x = (z : ℚ_[p]) := by
      have h1 : (z : ℚ_[p]) * (p : ℚ_[p]) ^ k = (p : ℚ_[p]) ^ k * x - m := by
        have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hz
        simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] at this
        rw [this, PadicInt.coe_sub]
        rfl
      field_simp
      linear_combination -h1
    rw [key]; exact z.2

theorem toQuot_ker : (toQuot p).ker = (AddMonoidHom.range (Int.castAddHom ℚ)).addSubgroupOf (zInvP p) := by
  ext ⟨r, hr⟩
  simp only [AddMonoidHom.mem_ker, toQuot, AddMonoidHom.coe_comp, Function.comp_apply,
    AddSubgroup.coe_subtype, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    AddMonoidHom.mem_range, Int.coe_castAddHom]
  constructor
  · intro h
    have h' : ‖((r : ℚ) : ℚ_[p])‖ ≤ 1 := h
    exact ⟨r.num, by simpa using Rat.coe_int_num_of_den_eq_one (den_eq_one_of_mem p hr h')⟩
  · rintro ⟨n, rfl⟩
    show ‖((n : ℚ) : ℚ_[p])‖ ≤ 1
    push_cast; exact Padic.norm_int_le_one n

/-- `ℚ_p/ℤ_p ≅ ℤ[1/p]/ℤ`. -/
def quotEquiv : (zInvP p ⧸ (toQuot p).ker) ≃+ ℚ_[p] ⧸ zP p :=
  QuotientAddGroup.quotientKerEquivOfSurjective _ (toQuot_surjective p)

/-- The map `ℤ[1/p]/ℤ → ℝ/ℤ`. -/
def toCircle : zInvP p ⧸ (toQuot p).ker →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' _).comp ((Rat.castHom ℝ).toAddMonoidHom.comp (zInvP p).subtype))
    (by
      intro r hr
      rw [toQuot_ker, AddSubgroup.mem_addSubgroupOf] at hr
      obtain ⟨n, hn⟩ := hr
      rw [AddMonoidHom.mem_ker]
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
        RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, QuotientAddGroup.mk'_apply]
      rw [← hn]
      simp only [Int.coe_castAddHom, map_intCast]
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩)

/-- **The `p`-adic fractional part** `ℚ_p → ℝ/ℤ`. -/
def fractP : ℚ_[p] →+ AddCircle (1 : ℝ) :=
  (toCircle p).comp ((quotEquiv p).symm.toAddMonoidHom.comp (QuotientAddGroup.mk' (zP p)))

/-- On `ℤ[1/p]`, the fractional part is the class mod `1`. -/
theorem fractP_rat {r : ℚ} (hr : r ∈ zInvP p) : fractP p (r : ℚ_[p]) = ((r : ℝ) : AddCircle (1 : ℝ)) := by
  have : (QuotientAddGroup.mk' (zP p)) (r : ℚ_[p]) = quotEquiv p (QuotientAddGroup.mk ⟨r, hr⟩) := rfl
  simp only [fractP, AddMonoidHom.coe_comp, Function.comp_apply, this,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, AddEquiv.symm_apply_apply]
  rfl

theorem fractP_eq_zero_iff (x : ℚ_[p]) : fractP p x = 0 ↔ ‖x‖ ≤ 1 := by
  obtain ⟨⟨r, hr⟩, hx⟩ := toQuot_surjective p (QuotientAddGroup.mk' (zP p) x)
  have hxr : QuotientAddGroup.mk' (zP p) x = quotEquiv p (QuotientAddGroup.mk ⟨r, hr⟩) := hx.symm
  have hval : fractP p x = ((r : ℝ) : AddCircle (1 : ℝ)) := by
    simp only [fractP, AddMonoidHom.coe_comp, Function.comp_apply, hxr,
      AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, AddEquiv.symm_apply_apply]
    rfl
  have hsub : -(r : ℚ_[p]) + x ∈ zP p := by
    have : QuotientAddGroup.mk' (zP p) (r : ℚ_[p]) = QuotientAddGroup.mk' (zP p) x := hx
    exact QuotientAddGroup.eq.mp this
  rw [hval, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hrn : r = n := by
      have : (r : ℝ) = n := by rw [← hn, zsmul_one]
      exact_mod_cast this
    rw [mem_zP] at hsub
    have : x = -(r : ℚ_[p]) + x + (r : ℚ_[p]) := by ring
    rw [this]
    refine (Padic.nonarchimedean _ _).trans (max_le hsub ?_)
    rw [hrn]; push_cast; exact Padic.norm_int_le_one n
  · intro hx1
    have hr1 : ‖(r : ℚ_[p])‖ ≤ 1 := by
      have : (r : ℚ_[p]) = x + -(-(r : ℚ_[p]) + x) := by ring
      rw [this]
      exact (Padic.nonarchimedean _ _).trans (max_le hx1 (by rw [norm_neg]; exact hsub))
    have hden := den_eq_one_of_mem p hr hr1
    refine ⟨r.num, ?_⟩
    rw [zsmul_one]
    exact_mod_cast Rat.coe_int_num_of_den_eq_one hden

theorem fractP_eq_zero_of_norm_le {x : ℚ_[p]} (h : ‖x‖ ≤ 1) : fractP p x = 0 :=
  (fractP_eq_zero_iff p x).mpr h

/-- The fractional part is continuous: it is constant on the cosets of the open subgroup `ℤ_p`. -/
theorem continuous_fractP : Continuous (fractP p) := by
  have hopen : IsOpen (zP p : Set ℚ_[p]) := by
    have := IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) (one_ne_zero (α := ℝ))
    convert this using 1
    ext x; simp
  refine continuous_of_continuousAt_zero (fractP p) ?_
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [hopen.mem_nhds (zP p).zero_mem] with y hy
  rw [fractP_eq_zero_of_norm_le p hy, map_zero]

end AdelicToriLean
