import AdelicToriLean.ZassenhausTopology
import AdelicToriLean.DimLattice

/-!
# Delta-subgroups are annihilators of lattices; `dim_n` is independent of the delta-subgroup

`A` discrete, `ι : A → ℚⁿ` injective, `d_j ∈ A` with `ι(d_j) = e_j`, `F = ι⁻¹(ℤⁿ)`,
`G = A^∨`. For a delta-subgroup `C` of `G`, `C^⊥ = {a : χ(a) = 1 ∀ χ ∈ C}` (`perpA C`):

* `mem_iff_perp`: `C = (C^⊥)^⊥` (characters separate points from closed subgroups);
* `exists_pow_mem`: a compact totally disconnected subgroup `H` of `G` has `χ^N ∈ C` for all
  `χ ∈ H`, some `N > 0` (`G/C` is a torus, which has no small subgroups);
* `dimN_delta`: `dim_n(A/C^⊥) = dim_n(A/F)`. So `dim_n G := dim_n C` does not depend on the
  delta-subgroup `C` (Lewis 2019, Lemma 6, Corollary 4).
-/

open Topology

noncomputable section

namespace AdelicToriLean

/-- **Compact totally disconnected subgroups die in a torus up to a fixed power.** For
`q : G → (ℝ/ℤ)ᵐ` continuous and `H` compact, totally disconnected, there is `N > 0` with
`q(x)^N = 1` for all `x ∈ H`. -/
theorem exists_pow_ker {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    {m : ℕ} (q : G →* Torus m) (hq : Continuous q) (H : Subgroup G) [CompactSpace H]
    [T2Space H] [TotallyDisconnectedSpace H] :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ H, q x ^ N = 1 := by
  obtain ⟨U, hU, h1U, hsub⟩ := torus_nss m
  set qH : H →* Torus m := q.comp H.subtype
  have hqH : Continuous qH := hq.comp continuous_subtype_val
  obtain ⟨V, hV, h1V, hVU⟩ := compact_exists_isClopen_in_isOpen (hU.preimage hqH)
    (show qH 1 ∈ U by rw [map_one]; exact h1U)
  obtain ⟨O, hO⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hV h1V
  -- `q` kills `O`
  have hO1 : ∀ x ∈ (O : Subgroup H), qH x = 1 := by
    have := hsub ((O : Subgroup H).map qH) (by
      rintro _ ⟨x, hx, rfl⟩; exact hVU (hO hx))
    intro x hx
    have hmem : qH x ∈ (O : Subgroup H).map qH := ⟨x, hx, rfl⟩
    rw [this] at hmem
    exact hmem
  -- `O` has finite index
  have hfin : Finite (H ⧸ (O : Subgroup H)) := by
    have : DiscreteTopology (H ⧸ (O : Subgroup H)) := by
      rw [discreteTopology_iff_isOpen_singleton_one]
      have : ({1} : Set (H ⧸ (O : Subgroup H))) = QuotientGroup.mk '' (O : Set H) := by
        ext y
        constructor
        · rintro rfl; exact ⟨1, (O : Subgroup H).one_mem, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact (QuotientGroup.eq_one_iff x).mpr hx
      rw [this]
      exact QuotientGroup.isOpenMap_coe _ O.isOpen
    exact finite_of_compact_of_discrete
  have hidx : (O : Subgroup H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨(O : Subgroup H).index, Nat.pos_of_ne_zero hidx, fun x hx => ?_⟩
  have := hO1 _ ((O : Subgroup H).pow_index_mem ⟨x, hx⟩)
  rw [map_pow] at this
  exact this

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] {n : ℕ}
  {ι : A →+ (Fin n → ℚ)} {d : Fin n → A} (hd : ∀ j, ι (d j) = Pi.single j 1)

/-- `C^⊥ ⊆ A`. -/
def perpA (C : Subgroup (PontryaginDual (Multiplicative A))) : AddSubgroup A where
  carrier := {a | ∀ χ ∈ C, χ (Multiplicative.ofAdd a) = 1}
  zero_mem' χ _ := map_one χ
  add_mem' {a b} ha hb χ hχ := by
    show χ (Multiplicative.ofAdd a * Multiplicative.ofAdd b) = 1
    rw [map_mul, ha χ hχ, hb χ hχ, one_mul]
  neg_mem' {a} ha χ hχ := by
    show χ (Multiplicative.ofAdd a)⁻¹ = 1
    rw [map_inv, ha χ hχ, inv_one]

/-- **`C = (C^⊥)^⊥`** for closed `C`. -/
theorem mem_iff_perp {C : Subgroup (PontryaginDual (Multiplicative A))}
    (hC : IsClosed (C : Set (PontryaginDual (Multiplicative A)))) (χ : PontryaginDual (Multiplicative A)) :
    χ ∈ C ↔ ∀ a ∈ perpA C, χ (Multiplicative.ofAdd a) = 1 := by
  constructor
  · intro hχ a ha; exact ha χ hχ
  · intro h
    by_contra hχ
    obtain ⟨ψ, hψC, hψχ⟩ := exists_char_sep hC hχ
    obtain ⟨a, rfl⟩ := PontryaginDual.eval_surjective (Multiplicative A) ψ
    apply hψχ
    exact h (Multiplicative.toAdd a) fun c hc => hψC c hc

include hd in
/-- `F = (F^⊥)^⊥`: an `a` killed by every character in `T^∨` has integral coordinates. -/
theorem mem_Flat_of_Tperp {a : A} (h : ∀ χ ∈ Tperp d, χ (Multiplicative.ofAdd a) = 1) :
    a ∈ Flat ι := by
  intro j
  have h1 := h _ (expA_castZ_mem hd (Pi.single j 1))
  rw [expA_apply, castZ, toAdd_ofAdd, toAdd_ofAdd, ip, Finset.sum_eq_single j,
    Circle.exp_eq_one] at h1
  · obtain ⟨m, hm⟩ := h1
    refine ⟨m, ?_⟩
    have := Real.pi_pos
    simp only [Pi.single_eq_same, Int.cast_one, one_mul] at hm
    have : 2 * Real.pi * ((ι a j : ℚ) : ℝ) = 2 * Real.pi * m := by rw [hm]; ring
    exact_mod_cast mul_left_cancel₀ (by positivity) this
  · intro i _ hij; simp [Pi.single_eq_of_ne hij]
  · intro h'; exact absurd (Finset.mem_univ j) h'

/-- A delta-subgroup is compact and totally disconnected. -/
theorem delta_compact_td {C : Subgroup (PontryaginDual (Multiplicative A))} {m : ℕ}
    (hC : IsDelta C m) : CompactSpace C ∧ TotallyDisconnectedSpace C :=
  ⟨isCompact_iff_compactSpace.mp hC.closed.isCompact,
    totallyDisconnectedSpace_subtype_iff.mpr hC.td⟩

include hd in
/-- **`dim_n` does not depend on the delta-subgroup.** For every delta-subgroup `C` of `A^∨`,
`C = (C^⊥)^⊥` and `dim_n(A/C^⊥) = dim_n(A/F)`. -/
theorem dimN_delta (hι : Function.Injective ι) {C : Subgroup (PontryaginDual (Multiplicative A))}
    {m : ℕ} (hC : IsDelta C m) :
    (∀ χ, χ ∈ C ↔ ∀ a ∈ perpA C, χ (Multiplicative.ofAdd a) = 1) ∧
      dimN (A ⧸ perpA C) = dimN (A ⧸ Flat ι) := by
  refine ⟨mem_iff_perp hC.closed, ?_⟩
  set G := PontryaginDual (Multiplicative A)
  set F := perpA C
  have hT := Tperp_isDelta hd hι
  obtain ⟨hCc, hCt⟩ := delta_compact_td hC
  obtain ⟨hTc, hTt⟩ := delta_compact_td hT
  obtain ⟨qC, hqC, -, -, hkC⟩ := hC.exists_map
  obtain ⟨qT, hqT, -, -, hkT⟩ := hT.exists_map
  obtain ⟨N, hN, hNT⟩ := exists_pow_ker qC hqC (Tperp d)
  obtain ⟨N', hN', hNC⟩ := exists_pow_ker qT hqT C
  -- `N F ⊆ Flat`
  have h1 : ∀ a ∈ F, N • a ∈ Flat ι := fun a ha =>
    mem_Flat_of_Tperp hd fun χ hχ => by
      have hC' : χ ^ N ∈ C := (hkC _).mp (by rw [map_pow]; exact hNT χ hχ)
      have := ha _ hC'
      erw [ContinuousMonoidHom.pow_apply] at this
      show χ (Multiplicative.ofAdd a ^ N) = 1
      rw [map_pow]; exact this
  -- `N' Flat ⊆ F`
  have h2 : ∀ a ∈ Flat ι, N' • a ∈ F := fun a ha χ hχ => by
    have hT' : χ ^ N' ∈ Tperp d := (hkT _).mp (by rw [map_pow]; exact hNC χ hχ)
    have := (mem_Tperp_iff hd hι _).mp hT' a ha
    erw [ContinuousMonoidHom.pow_apply] at this
    show χ (Multiplicative.ofAdd a ^ N') = 1
    rw [map_pow]; exact this
  -- finiteness of the two images
  have hfin1 : Finite ((F ⊔ Flat ι).map (QuotientAddGroup.mk' F)) := by
    -- the image of `Flat ι` in `A/F`, finitely generated and killed by `N'`
    set M := (F ⊔ Flat ι).map (QuotientAddGroup.mk' F)
    have hgen : ∀ y ∈ M, ∃ k : Fin n → ℤ, y = ((∑ j, k j • d j : A) : A ⧸ F) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨u, hu, v, hv, rfl⟩ := AddSubgroup.mem_sup.mp hx
      choose k hk using hv
      refine ⟨k, ?_⟩
      rw [eq_sum_of_int hd hι hk]
      simp [(QuotientAddGroup.eq_zero_iff u).mpr hu]
    let L : (Fin n → ℤ) →ₗ[ℤ] M :=
      { toFun := fun k => ⟨((∑ j, k j • d j : A) : A ⧸ F), ⟨∑ j, k j • d j,
            AddSubgroup.mem_sup_right (AddSubgroup.sum_mem _ fun j _ =>
              AddSubgroup.zsmul_mem _ (fun i => ⟨if i = j then 1 else 0, by
                rw [hd, Pi.single_apply]; split_ifs <;> simp⟩) _), rfl⟩⟩
        map_add' := fun k k' => by
          ext; simp [add_smul, Finset.sum_add_distrib]
        map_smul' := fun c k => by
          ext; simp [Finset.smul_sum, mul_smul] }
    have hL : Function.Surjective L := fun y => by
      obtain ⟨k, hk⟩ := hgen y y.2
      exact ⟨k, Subtype.ext hk.symm⟩
    have : Module.Finite ℤ M := Module.Finite.of_surjective L hL
    have htor : Module.IsTorsion ℤ M := by
      intro y
      obtain ⟨k, hk⟩ := hgen y y.2
      refine ⟨⟨(N' : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN'.ne')⟩, ?_⟩
      apply Subtype.ext
      simp only [Submonoid.mk_smul, natCast_zsmul, AddSubgroup.coe_nsmul, hk,
        AddSubgroup.coe_zero]
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact h2 _ (AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ (fun i =>
        ⟨if i = j then 1 else 0, by rw [hd, Pi.single_apply]; split_ifs <;> simp⟩) _)
    exact Module.finite_of_fg_torsion _ htor
  have hfin2 : Finite ((F ⊔ Flat ι).map (QuotientAddGroup.mk' (Flat ι))) := by
    -- the image of `F` in `A/Flat`, inside `(A/Flat)[N]`
    have : NeZero N := ⟨hN.ne'⟩
    have hfinN := (card_ptors_le ι N).1
    refine Finite.of_injective (fun y : (F ⊔ Flat ι).map (QuotientAddGroup.mk' (Flat ι)) =>
      (⟨y, ?_⟩ : ptors (A ⧸ Flat ι) N)) fun y y' h => by
        have := congrArg Subtype.val h; exact Subtype.ext this
    obtain ⟨x, hx, hxy⟩ := y.2
    obtain ⟨u, hu, v, hv, rfl⟩ := AddSubgroup.mem_sup.mp hx
    show N • (y : A ⧸ Flat ι) = 0
    rw [← hxy, QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk_nsmul,
      QuotientAddGroup.eq_zero_iff, smul_add]
    exact (Flat ι).add_mem (h1 u hu) ((Flat ι).nsmul_mem hv N)
  exact dimN_eq_of_finiteIndex F (Flat ι)

end AdelicToriLean
