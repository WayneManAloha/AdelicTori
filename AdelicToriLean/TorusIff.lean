import AdelicToriLean.DeltaLattice

/-!
# `dim_n G = 0` iff `G` is an `n`-dimensional real torus

`A` discrete, `ι : A → ℚⁿ` injective, `d_j ∈ A` with `ι(d_j) = e_j`, `G = A^∨`, `n = dim_a G`.

* `dimN_eq_zero_iff_torus`: `dim_n G = 0` iff `{1}` is a delta-subgroup of `G` with
  `G ≅ (ℝ/ℤ)ⁿ`; together with `dimN_le` (`0 ≤ dim_n G ≤ dim_a G`) this is Lewis 2019,
  Corollary 4, as quoted in the paper.
-/

noncomputable section

namespace AdelicToriLean

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] {n : ℕ}
  {ι : A →+ (Fin n → ℚ)} {d : Fin n → A} (hd : ∀ j, ι (d j) = Pi.single j 1)

include hd in
/-- **`dim_n G = 0` iff `G` is an `n`-dimensional real torus** (`{1}` is a delta-subgroup). -/
theorem dimN_eq_zero_iff_torus (hι : Function.Injective ι) :
    dimN (A ⧸ Flat ι) = 0 ↔ IsDelta (⊥ : Subgroup (PontryaginDual (Multiplicative A))) n := by
  constructor
  · intro h0
    have hfin := (dimN_eq_zero_iff ι).mp h0
    set N := Nat.card (A ⧸ Flat ι)
    have hN : N ≠ 0 := Nat.card_pos.ne'
    -- `a ↦ N ι(a)` embeds `A` in `ℤⁿ`
    have hint : ∀ a : A, ∀ j, ∃ k : ℤ, (N : ℚ) * ι a j = k := fun a j => by
      have h1 : N • (a : A ⧸ Flat ι) = 0 := card_nsmul_eq_zero'
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h1
      obtain ⟨k, hk⟩ := h1 j
      exact ⟨k, by rw [← hk, map_nsmul, Pi.smul_apply, nsmul_eq_mul]⟩
    choose k hk using hint
    let e : A →ₗ[ℤ] (Fin n → ℤ) :=
      { toFun := fun a j => k a j
        map_add' := fun a b => by
          funext j
          have := hk (a + b) j
          rw [map_add, Pi.add_apply, mul_add, hk a j, hk b j] at this
          exact_mod_cast this.symm
        map_smul' := fun c a => by
          funext j
          have := hk (c • a) j
          rw [map_zsmul, Pi.smul_apply, zsmul_eq_mul, ← mul_assoc, mul_comm (N : ℚ),
            mul_assoc, hk a j] at this
          simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
          exact_mod_cast this.symm }
    have he : Function.Injective e := by
      intro a b hab
      apply hι
      funext j
      have h1 := hk a j
      have h2 := hk b j
      have : k a j = k b j := congrFun hab j
      have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
      apply mul_left_cancel₀ hN'
      rw [h1, h2, this]
    -- `A` is free of finite rank
    have : Module.Finite ℤ A := Module.Finite.of_injective e he
    have : Module.Free ℤ A := Module.Free.of_equiv (LinearEquiv.ofInjective e he).symm
    -- the rank is `n`
    have hrank : Module.finrank ℤ A = n := by
      apply le_antisymm
      · have := LinearMap.finrank_le_finrank_of_injective he
        simpa using this
      · have hli : LinearIndependent ℤ d := by
          rw [Fintype.linearIndependent_iff]
          intro c hc j
          have := congrArg (fun a => ι a j) hc
          simp [map_sum, hd, Pi.single_apply, Finset.sum_apply] at this
          exact_mod_cast this
        simpa using hli.fintype_card_le_finrank
    let b : Module.Basis (Fin n) ℤ A := (Module.finBasis ℤ A).reindex (finCongr hrank)
    let ι' : A →+ (Fin n → ℚ) :=
      { toFun := fun a j => (b.repr a j : ℚ)
        map_zero' := by funext j; simp
        map_add' := fun x y => by funext j; simp }
    have hι' : Function.Injective ι' := by
      intro x y h
      apply b.repr.injective
      ext j
      have := congrFun h j
      simp only [ι', AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      exact_mod_cast this
    have hd' : ∀ j, ι' (b j) = Pi.single j 1 := fun j => by
      funext i
      simp only [ι', AddMonoidHom.coe_mk, ZeroHom.coe_mk, Module.Basis.repr_self,
        Finsupp.single_apply, Pi.single_apply, eq_comm]
      split_ifs <;> simp
    have hbot : Tperp (fun j => b j) = ⊥ := by
      rw [eq_bot_iff]
      intro χ hχ
      rw [Subgroup.mem_bot]
      refine PontryaginDual.ext fun x => ?_
      rw [PontryaginDual.one_apply]
      have key : ∀ y ∈ Submodule.span ℤ (Set.range b), χ (Multiplicative.ofAdd y) = 1 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨j, rfl⟩ := hy
          exact hχ j
        | zero => exact map_one χ
        | add y z _ _ hy hz =>
          show χ (Multiplicative.ofAdd y * Multiplicative.ofAdd z) = 1
          rw [map_mul, hy, hz, one_mul]
        | smul c y _ hy =>
          show χ (Multiplicative.ofAdd y ^ c) = 1
          rw [map_zpow, hy, one_zpow]
      exact key (Multiplicative.toAdd x) (by rw [b.span_eq]; trivial)
    rw [← hbot]
    exact Tperp_isDelta hd' hι'
  · intro hbot
    obtain ⟨-, h⟩ := dimN_delta hd hι hbot
    rw [← h]
    have htop : perpA (⊥ : Subgroup (PontryaginDual (Multiplicative A))) = ⊤ := by
      rw [eq_top_iff]
      intro a _ χ hχ
      rw [Subgroup.mem_bot] at hχ
      rw [hχ]; rfl
    rw [htop]
    refine Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨⊥, inferInstance, fun p hp => ?_⟩)
    unfold prank
    have : Subsingleton ((A ⧸ (⊤ : AddSubgroup A)) ⧸ (⊥ : AddSubgroup (A ⧸ (⊤ : AddSubgroup A)))) := by
      have : Subsingleton (A ⧸ (⊤ : AddSubgroup A)) := QuotientAddGroup.subsingleton_quotient_top
      exact (QuotientAddGroup.quotientBot).toEquiv.subsingleton
    rw [Nat.card_unique, Nat.log_one_right]

end AdelicToriLean
