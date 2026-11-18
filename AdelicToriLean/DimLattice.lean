import AdelicToriLean.NonarchDim
import AdelicToriLean.DeltaExistence

/-!
# `dim_n` for `A ⊆ ℚⁿ`: bounds and the zero case

`A` an abelian group with `ι : A → ℚⁿ` injective, `F = ι⁻¹(ℤⁿ)` (`Flat ι`), `T = A/F`.

* `card_ptors_le`: `|T[m]| ≤ mⁿ`, so `T[m]` is finite and `rk_p T ≤ n`;
* `dimN_le`: `dim_n ≤ n`, i.e. `dim_n G ≤ dim_a G`;
* `dimN_eq_zero_iff`: `dim_n = 0` iff `T` is finite; `one_le_dimN`: `T` infinite gives
  `dim_n ≥ 1`.
-/

noncomputable section

namespace AdelicToriLean

variable {A : Type*} [AddCommGroup A] {n : ℕ} (ι : A →+ (Fin n → ℚ))

/-- `F = ι⁻¹(ℤⁿ)`. -/
def Flat : AddSubgroup A where
  carrier := {a | ∀ j, ∃ m : ℤ, ι a j = m}
  zero_mem' j := ⟨0, by simp⟩
  add_mem' {a b} ha hb j := by
    obtain ⟨m, hm⟩ := ha j
    obtain ⟨m', hm'⟩ := hb j
    exact ⟨m + m', by rw [map_add, Pi.add_apply, hm, hm']; push_cast; ring⟩
  neg_mem' {a} ha j := by
    obtain ⟨m, hm⟩ := ha j
    exact ⟨-m, by rw [map_neg, Pi.neg_apply, hm]; push_cast; ring⟩

theorem mem_Flat {a : A} : a ∈ Flat ι ↔ ∀ j, ∃ m : ℤ, ι a j = m := Iff.rfl

/-- `A/F` is torsion. -/
theorem torsion_Flat (a : A) : ∃ m : ℕ, 0 < m ∧ m • (a : A ⧸ Flat ι) = 0 := by
  obtain ⟨m, hm, k, hk⟩ := exists_int_multiple (ι a)
  refine ⟨m, hm, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  intro j
  exact ⟨k j, by rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, hk j]⟩

/-- **`|(A/F)[m]| ≤ mⁿ`**, by `x ↦ (ι(m x) mod m)`. -/
theorem card_ptors_le (m : ℕ) [NeZero m] :
    Finite (ptors (A ⧸ Flat ι) m) ∧ Nat.card (ptors (A ⧸ Flat ι) m) ≤ m ^ n := by
  let f : ptors (A ⧸ Flat ι) m → (Fin n → ZMod m) := fun y j =>
    ((⌊ι (m • (y : A ⧸ Flat ι).out) j⌋ : ℤ) : ZMod m)
  have hint : ∀ y : ptors (A ⧸ Flat ι) m, m • (y : A ⧸ Flat ι).out ∈ Flat ι := fun y => by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul, QuotientAddGroup.out_eq']
    exact y.2
  have hfl : ∀ y : ptors (A ⧸ Flat ι) m, ∀ j,
      ((⌊ι (m • (y : A ⧸ Flat ι).out) j⌋ : ℤ) : ℚ) = ι (m • (y : A ⧸ Flat ι).out) j :=
    fun y j => by
      obtain ⟨k, hk⟩ := hint y j
      rw [hk, Int.floor_intCast]
  have hinj : Function.Injective f := by
    intro y₁ y₂ h
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne m
    have hdiff : (y₁ : A ⧸ Flat ι).out - (y₂ : A ⧸ Flat ι).out ∈ Flat ι := by
      intro j
      have hj := congrFun h j
      simp only [f] at hj
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hj
      obtain ⟨t, ht⟩ := hj
      refine ⟨-t, ?_⟩
      have e1 := hfl y₁ j
      have e2 := hfl y₂ j
      have := congrArg (fun z : ℤ => (z : ℚ)) ht
      push_cast at this
      rw [e1, e2, map_nsmul, map_nsmul, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul,
        nsmul_eq_mul] at this
      rw [map_sub, Pi.sub_apply]
      apply mul_left_cancel₀ hm0
      push_cast
      linear_combination -this
    apply Subtype.ext
    rw [← QuotientAddGroup.out_eq' (y₁ : A ⧸ Flat ι), ← QuotientAddGroup.out_eq' (y₂ : A ⧸ Flat ι)]
    exact QuotientAddGroup.eq.mpr (by
      have := (Flat ι).neg_mem hdiff
      rwa [neg_sub, sub_eq_neg_add] at this)
  refine ⟨Finite.of_injective f hinj, ?_⟩
  calc Nat.card (ptors (A ⧸ Flat ι) m) ≤ Nat.card (Fin n → ZMod m) :=
        Nat.card_le_card_of_injective f hinj
    _ = m ^ n := by simp [Nat.card_eq_fintype_card, ZMod.card]

theorem prank_le {p : ℕ} (hp : p.Prime) :
    prank (A ⧸ Flat ι) p ≤ n := by
  have : NeZero p := ⟨hp.ne_zero⟩
  unfold prank
  calc Nat.log p (Nat.card (ptors (A ⧸ Flat ι) p)) ≤ Nat.log p (p ^ n) :=
        Nat.log_mono_right (card_ptors_le ι p).2
    _ = n := Nat.log_pow hp.one_lt n

theorem n_mem_dimSet : n ∈ dimSet (A ⧸ Flat ι) := by
  refine ⟨⊥, inferInstance, fun p hp => ?_⟩
  rw [← prank_congr (QuotientAddGroup.quotientBot (G := A ⧸ Flat ι)).symm]
  exact prank_le ι hp

/-- **`dim_n ≤ n`** (`dim_n G ≤ dim_a G`). -/
theorem dimN_le : dimN (A ⧸ Flat ι) ≤ n :=
  Nat.sInf_le (n_mem_dimSet ι)

/-- **`dim_n = 0` iff `A/F` is finite.** -/
theorem dimN_eq_zero_iff :
    dimN (A ⧸ Flat ι) = 0 ↔ Finite (A ⧸ Flat ι) := by
  set T := A ⧸ Flat ι
  constructor
  · intro h0
    have hmem := Nat.sInf_mem ⟨n, n_mem_dimSet ι⟩
    rw [show sInf (dimSet T) = 0 from h0] at hmem
    obtain ⟨E, hE, hk⟩ := hmem
    -- `T/E = 0`
    have htriv : ∀ y : T ⧸ E, y = 0 := by
      intro y
      by_contra hy
      induction y using QuotientAddGroup.induction_on with | H x => ?_
      induction x using QuotientAddGroup.induction_on with | H a => ?_
      obtain ⟨m, hm, hma⟩ := torsion_Flat ι a
      set y : T ⧸ E := ((a : T) : T ⧸ E)
      have hmy : m • y = 0 := by
        show m • (((a : T)) : T ⧸ E) = 0
        rw [← QuotientAddGroup.mk_nsmul, hma, QuotientAddGroup.mk_zero]
      have hord : 0 < addOrderOf y :=
        (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, hm, hmy⟩).addOrderOf_pos
      have hord1 : addOrderOf y ≠ 1 := fun h => hy (AddMonoid.addOrderOf_eq_one_iff.mp h)
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hord1
      obtain ⟨c, hc⟩ := hpd
      set z := c • y
      have hz : p • z = 0 := by
        show p • c • y = 0
        rw [smul_smul, ← hc, addOrderOf_nsmul_eq_zero]
      have hz0 : z ≠ 0 := by
        intro h
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h
        rw [hc] at hdvd
        have hcpos : 0 < c := by
          rcases Nat.eq_zero_or_pos c with h' | h'
          · rw [h', mul_zero] at hc; omega
          · exact h'
        have := Nat.le_of_dvd hcpos hdvd
        have hp2 := hp.two_le
        nlinarith
      have : NeZero p := ⟨hp.ne_zero⟩
      have : Finite (ptors T p) := (card_ptors_le ι p).1
      have : Finite E := hE
      have : Finite (ptors (T ⧸ E) p) := finite_ptors_quot E p
      have h1 := one_le_prank hp hz hz0
      exact absurd (le_trans h1 (hk p hp)) (by norm_num)
    have : Finite E := hE
    have hET : ∀ x : T, x ∈ E := fun x =>
      (QuotientAddGroup.eq_zero_iff x).mp (htriv (x : T ⧸ E))
    exact Finite.of_injective (fun x : T => (⟨x, hET x⟩ : E)) fun x y h =>
      congrArg Subtype.val h
  · intro hfin
    refine Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨⊤, inferInstance, fun p hp => ?_⟩)
    unfold prank
    have : Subsingleton (T ⧸ (⊤ : AddSubgroup T)) := QuotientAddGroup.subsingleton_quotient_top
    have hc : Nat.card (ptors (T ⧸ (⊤ : AddSubgroup T)) p) = 1 := Nat.card_unique
    rw [hc, Nat.log_one_right]

/-- **Lower bound.** If `A/F` is infinite then `dim_n ≥ 1`. -/
theorem one_le_dimN (hinf : Infinite (A ⧸ Flat ι)) :
    1 ≤ dimN (A ⧸ Flat ι) := by
  by_contra h
  have h0 : dimN (A ⧸ Flat ι) = 0 := by omega
  exact (not_finite_iff_infinite.mpr hinf) ((dimN_eq_zero_iff ι).mp h0)

end AdelicToriLean
