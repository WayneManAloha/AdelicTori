import AdelicToriLean.ArlaReal

/-!
# Theorem `adelic-exponential-lie-category`

For a finite-dimensional protorus `G`, `n = dim_a G`, the exponential
`E : nala(G) × arla(G) → G`, `E(f, g) = f(1) · g(1)` (the adelic exponential under
`adla(G) ≅ nala(G) × arla(G)`, `expAd_eq`) is continuous, surjective and open, with discrete kernel
isomorphic to `ℚⁿ`.

Fix `ι : G^∨ → ℚⁿ` injective, `d_j` with `ι(d_j) = e_j`, `q = qmap d`, `Δ = ker q`.
* `E_surjective`: `x = (x · v_θ(1)⁻¹) · v_θ(1)` with `d_j(v_θ(1)) = d_j(x)`, the first factor in `Δ`;
* `vθ_one_mem_td_iff`: `v_θ(1) ∈ td(G)` iff `θ ∈ (2πℚ)ⁿ`;
* `kerE_equiv`: `ker E ≅ ℚⁿ`; `discrete_kerE`: `ker E` is discrete;
* `sigmaCompact_nala`: `nala(G)` is σ-compact (fibres of `f ↦ q(f 1)` over the countable torsion
  of the torus are compact); `E_isOpenMap` by the open mapping theorem.
-/

open Topology TensorProduct Real

noncomputable section

namespace AdelicToriLean

/-- The torsion of the torus is countable. -/
theorem countable_torsion_torus (n : ℕ) :
    {y : Torus n | ∃ k : ℕ, 0 < k ∧ y ^ k = 1}.Countable := by
  have : {y : Torus n | ∃ k : ℕ, 0 < k ∧ y ^ k = 1} =
      ⋃ k : ℕ, {y : Torus n | 0 < k ∧ y ^ k = 1} := by
    ext y; simp
  rw [this]
  refine Set.countable_iUnion fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · refine ((Set.Finite.pi (t := fun _ => {z : Circle | z ^ k = 1})
      fun _ => finite_roots_circle hk).subset ?_).countable
    rintro y ⟨-, hy⟩ i -
    show y i ^ k = 1
    rw [← Pi.pow_apply, hy, Pi.one_apply]

/-- Torsion of the circle: `exp θ` is torsion iff `θ ∈ 2πℚ`. -/
theorem circle_torsion_iff (θ : ℝ) :
    (∃ k : ℕ, 0 < k ∧ Circle.exp θ ^ k = 1) ↔ ∃ r : ℚ, θ = 2 * π * r := by
  constructor
  · rintro ⟨k, hk, h⟩
    rw [← zpow_natCast, ← Circle.exp_zsmul, Circle.exp_eq_one] at h
    obtain ⟨m, hm⟩ := h
    refine ⟨(m : ℚ) / k, ?_⟩
    simp only [zsmul_eq_mul, Int.cast_natCast] at hm
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast
    field_simp
    linarith
  · rintro ⟨r, rfl⟩
    refine ⟨r.den, r.den_pos, ?_⟩
    rw [← zpow_natCast, ← Circle.exp_zsmul, Circle.exp_eq_one]
    refine ⟨r.num, ?_⟩
    simp only [zsmul_eq_mul, Int.cast_natCast]
    rw [show (r.den : ℝ) * (2 * π * r) = ((r.den : ℝ) * r) * (2 * π) by ring,
      show (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) by exact_mod_cast Rat.den_mul_eq_num r]

/-- `r ↦ 2πr : ℚⁿ → ℝⁿ`. -/
def twoPiRat {n : ℕ} : Multiplicative (Fin n → ℚ) →* Multiplicative (Fin n → ℝ) where
  toFun r := Multiplicative.ofAdd fun j => 2 * π * (Multiplicative.toAdd r j : ℝ)
  map_one' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1; funext j; simp
  map_mul' r s := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 1; funext j; simp [mul_add]

theorem twoPiRat_injective {n : ℕ} : Function.Injective (twoPiRat (n := n)) := by
  intro r s h
  have := congrArg Multiplicative.toAdd h
  apply Multiplicative.toAdd.injective
  funext j
  have hj := congrFun this j
  simp only [twoPiRat, MonoidHom.coe_mk, OneHom.coe_mk] at hj
  exact_mod_cast mul_left_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0) hj

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]

/-- `E(f, g) = f(1) · g(1)`. -/
def Eexp : nala G × arla G →* G := (expn G).coprod (expa G)

omit [CompactSpace G] [T2Space G] in
theorem Eexp_apply (p : nala G × arla G) : Eexp G p = expn G p.1 * expa G p.2 := rfl

omit [CompactSpace G] [T2Space G] in
theorem continuous_Eexp : Continuous (Eexp G) :=
  ((continuous_expn G).comp continuous_fst).mul ((continuous_expa G).comp continuous_snd)

omit [CompactSpace G] [T2Space G] in
/-- The adelic exponential is `E` composed with `adla(G) ≅ nala(G) × arla(G)`. -/
theorem expAd_eq_Eexp (f : adla G) : expAd G f = Eexp G (adlaEquiv G f) := expAd_eq G f

section Data

variable {G}
variable [DiscreteTopology (PontryaginDual G)] {n : ℕ}
  {ι : Additive (PontryaginDual G) →+ (Fin n → ℚ)} (hι : Function.Injective ι)
  {d : Fin n → Additive (PontryaginDual G)} (hd : ∀ j, ι (d j) = Pi.single j 1)
include hι hd

omit hι in
theorem q_vθ_one (θ : Fin n → ℝ) (j : Fin n) :
    qmap G d (vθ ι θ (Multiplicative.ofAdd 1)) j = Circle.exp (θ j) := by
  rw [qmap_apply, d_vθ hd, toAdd_ofAdd, one_mul]

theorem mem_tdSet_of_ker {y : G} (hy : y ∈ (qmap G d).ker) : y ∈ tdSet G :=
  ⟨_, (ker_qmap_isDelta G hι hd).closed.isCompact,
    totallyDisconnectedSpace_subtype_iff.mpr (ker_qmap_isDelta G hι hd).td, hy⟩

/-- **`E` is surjective.** -/
theorem E_surjective : Function.Surjective (Eexp G) := by
  intro x
  choose θ hθ using fun j => Circle.exp_surjective (qmap G d x j)
  set v := vθ ι θ
  set y := x * (v (Multiplicative.ofAdd 1))⁻¹
  have hy : y ∈ (qmap G d).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    funext j
    rw [q_vθ_one hd, hθ]
  set f := (expnEquiv G).symm ⟨y, (mem_td_iff G).mpr (mem_tdSet_of_ker hι hd hy)⟩
  refine ⟨(f, v), ?_⟩
  rw [Eexp_apply]
  have hf : expn G f = y := by
    show (expnEquiv G f : G) = y
    rw [MulEquiv.apply_symm_apply]
  rw [hf]
  show x * (v (Multiplicative.ofAdd 1))⁻¹ * v (Multiplicative.ofAdd 1) = x
  group

/-- `v_θ(1) ∈ td(G)` iff `θ ∈ (2πℚ)ⁿ`. -/
theorem vθ_one_mem_td_iff (θ : Fin n → ℝ) :
    vθ ι θ (Multiplicative.ofAdd 1) ∈ tdSet G ↔ ∀ j, ∃ r : ℚ, θ j = 2 * π * r := by
  have hΔ := ker_qmap_isDelta G hι hd
  have hq : ∀ x, qmap G d x = 1 ↔ x ∈ (qmap G d).ker := fun x => MonoidHom.mem_ker.symm
  constructor
  · intro h j
    obtain ⟨k, hk, hk1⟩ := torsion_of_mem_tdSet (qmap G d) (continuous_qmap G d) h
    have := congrFun hk1 j
    rw [Pi.pow_apply, q_vθ_one hd, Pi.one_apply] at this
    exact (circle_torsion_iff (θ j)).mp ⟨k, hk, this⟩
  · intro h
    choose r hr using h
    obtain ⟨m, hm, k, hk⟩ := exists_int_multiple r
    refine mem_tdSet_of_torsion hΔ (qmap G d) (continuous_qmap G d) hq hm ?_
    funext j
    rw [Pi.pow_apply, q_vθ_one hd, Pi.one_apply, hr j, ← zpow_natCast, ← Circle.exp_zsmul,
      Circle.exp_eq_one]
    refine ⟨k j, ?_⟩
    simp only [zsmul_eq_mul, Int.cast_natCast]
    rw [show (m : ℝ) * (2 * π * r j) = ((m : ℝ) * r j) * (2 * π) by ring,
      show (m : ℝ) * (r j : ℝ) = (k j : ℝ) by exact_mod_cast hk j]

/-- The coordinate `ker E → ℝⁿ`, `(f, g) ↦ θ` with `g = v_θ`. -/
def kerCoord : (Eexp G).ker →* Multiplicative (Fin n → ℝ) :=
  (arlaEquiv hd hι).toMulEquiv.toMonoidHom.comp
    ((MonoidHom.snd (nala G) (arla G)).comp (Eexp G).ker.subtype)

theorem kerCoord_injective : Function.Injective (kerCoord hι hd) := by
  rintro ⟨⟨f, g⟩, hfg⟩ ⟨⟨f', g'⟩, hfg'⟩ h
  have hg : g = g' := (arlaEquiv hd hι).injective h
  subst hg
  have h1 : expn G f * expa G g = 1 := hfg
  have h2 : expn G f' * expa G g = 1 := hfg'
  have hf : f = f' := expn_injective G (by
    rw [eq_inv_of_mul_eq_one_left h1, eq_inv_of_mul_eq_one_left h2])
  subst hf
  rfl

/-- The range of `kerCoord` is `(2πℚ)ⁿ`. -/
theorem mem_range_kerCoord (θ : Multiplicative (Fin n → ℝ)) :
    θ ∈ (kerCoord hι hd).range ↔ ∀ j, ∃ r : ℚ, Multiplicative.toAdd θ j = 2 * π * r := by
  rw [← vθ_one_mem_td_iff hι hd]
  constructor
  · rintro ⟨⟨⟨f, g⟩, hfg⟩, rfl⟩
    have hg : vθ ι (Multiplicative.toAdd ((arlaEquiv hd hι) g)) = g :=
      (arlaEquiv hd hι).symm_apply_apply g
    show vθ ι (Multiplicative.toAdd ((arlaEquiv hd hι) g)) (Multiplicative.ofAdd 1) ∈ tdSet G
    rw [hg]
    have h1 : f genZ * g (Multiplicative.ofAdd 1) = 1 := hfg
    have : g (Multiplicative.ofAdd 1) = (f genZ)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, ← range_expn]
    exact ⟨f⁻¹, rfl⟩
  · intro h
    set g := vθ ι (Multiplicative.toAdd θ)
    rw [← range_expn] at h
    obtain ⟨f, hf⟩ := h
    refine ⟨⟨(f⁻¹, g), ?_⟩, ?_⟩
    · show (f⁻¹ : nala G) genZ * g (Multiplicative.ofAdd 1) = 1
      have : (f⁻¹ : nala G) genZ = (f genZ)⁻¹ := rfl
      rw [this, show f genZ = g (Multiplicative.ofAdd 1) from hf, inv_mul_cancel]
    · show (arlaEquiv hd hι) g = θ
      exact (arlaEquiv hd hι).apply_symm_apply θ

/-- **`ker E ≅ ℚⁿ`.** -/
def kerE_equiv : (Eexp G).ker ≃* Multiplicative (Fin n → ℚ) :=
  (MonoidHom.ofInjective (kerCoord_injective hι hd)).trans
    ((MulEquiv.subgroupCongr (by
      ext θ
      rw [mem_range_kerCoord hι hd]
      constructor
      · intro h
        choose r hr using h
        exact ⟨Multiplicative.ofAdd r, by
          apply Multiplicative.toAdd.injective; funext j; exact (hr j).symm⟩
      · rintro ⟨r, rfl⟩ j
        exact ⟨Multiplicative.toAdd r j, rfl⟩)).trans
      (MonoidHom.ofInjective (twoPiRat_injective (n := n))).symm)

/-- **`ker E` is discrete.** -/
theorem discrete_kerE : DiscreteTopology (Eexp G).ker := by
  set Δ := (qmap G d).ker
  set B : Set (Multiplicative (Fin n → ℝ)) := {θ | ∀ j, |Multiplicative.toAdd θ j| < 2 * π}
  have hB : IsOpen B := by
    have : B = Multiplicative.toAdd ⁻¹' Set.pi Set.univ (fun _ => Set.Ioo (-(2 * π)) (2 * π)) := by
      ext θ; simp [B, abs_lt]
    rw [this]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage continuous_toAdd
  set U : Set (nala G × arla G) :=
    (Kdelta Δ : Set (nala G)) ×ˢ ((arlaEquiv hd hι) ⁻¹' B)
  have hU : IsOpen U :=
    (isOpen_Kdelta (ker_qmap_isDelta G hι hd)).prod (hB.preimage (arlaEquiv hd hι).continuous)
  apply discreteTopology_of_isOpen_singleton_one
  have : ({1} : Set (Eexp G).ker) = Subtype.val ⁻¹' U := by
    ext ⟨⟨f, g⟩, hfg⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro h
      have h' : (f, g) = 1 := congrArg Subtype.val h
      simp only [Prod.mk_eq_one] at h'
      obtain ⟨rfl, rfl⟩ := h'
      refine ⟨(Kdelta Δ).one_mem, ?_⟩
      show (arlaEquiv hd hι 1) ∈ B
      rw [map_one]
      intro j
      simp [pi_pos]
    · rintro ⟨hf, hg⟩
      have h1 : f genZ * g (Multiplicative.ofAdd 1) = 1 := hfg
      set θ := arlaEquiv hd hι g
      have hgθ : vθ ι (Multiplicative.toAdd θ) = g := (arlaEquiv hd hι).symm_apply_apply g
      have hgΔ : g (Multiplicative.ofAdd 1) ∈ Δ := by
        rw [eq_inv_of_mul_eq_one_right h1]; exact Δ.inv_mem (hf genZ)
      have hθ0 : θ = 1 := by
        apply Multiplicative.toAdd.injective
        funext j
        have hq := congrFun (MonoidHom.mem_ker.mp hgΔ) j
        rw [← hgθ, q_vθ_one hd, Pi.one_apply, Circle.exp_eq_one] at hq
        obtain ⟨m, hm⟩ := hq
        have hb := hg j
        rw [hm, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hb
        have : |(m : ℝ)| < 1 := by
          by_contra hc; push Not at hc
          nlinarith [pi_pos]
        have hm0 : m = 0 := by
          have : |m| < 1 := by exact_mod_cast this
          have := abs_lt.mp this
          omega
        rw [hm, hm0]
        simp
      have hg1 : g = 1 := by
        rw [← hgθ, hθ0]
        exact (arlaEquiv hd hι).symm.map_one
      subst hg1
      have hf1 : f = 1 := expn_injective G (by
        rw [map_one]
        have : f genZ * 1 = 1 := h1
        show f genZ = 1
        simpa using this)
      subst hf1
      rfl
  rw [this]
  exact hU.preimage continuous_subtype_val

/-- `nala(G)` is σ-compact. -/
theorem sigmaCompact_nala : SigmaCompactSpace (nala G) := by
  have hΔ := ker_qmap_isDelta G hι hd
  set Δ := (qmap G d).ker
  set T := {y : Torus n | ∃ k : ℕ, 0 < k ∧ y ^ k = 1}
  set F : Torus n → Set (nala G) := fun t => {f | qmap G d (f genZ) = t}
  refine SigmaCompactSpace.of_countable (F '' T) ((countable_torsion_torus n).image F) ?_ ?_
  · rintro _ ⟨t, -, rfl⟩
    by_cases hne : (F t).Nonempty
    · obtain ⟨g, hg⟩ := hne
      have hcl : IsClosed (F t) := isClosed_singleton.preimage
        ((continuous_qmap G d).comp (continuous_expn G))
      refine (((isCompact_Kdelta hΔ.closed hΔ.td).image
        (continuous_const_mul g))).of_isClosed_subset hcl ?_
      intro f hf
      refine ⟨g⁻¹ * f, mem_Kdelta_of_genZ hΔ.closed ?_, by group⟩
      show qmap G d ((g⁻¹ * f) genZ) = 1
      have : (g⁻¹ * f) genZ = (g genZ)⁻¹ * f genZ := rfl
      rw [this, map_mul, map_inv, show qmap G d (g genZ) = t from hg,
        show qmap G d (f genZ) = t from hf, inv_mul_cancel]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]; exact isCompact_empty
  · rw [Set.sUnion_image, Set.eq_univ_iff_forall]
    intro f
    have hx : f genZ ∈ tdSet G := by rw [← range_expn]; exact ⟨f, rfl⟩
    obtain ⟨k, hk, hxk⟩ := torsion_of_mem_tdSet (qmap G d) (continuous_qmap G d) hx
    exact Set.mem_biUnion (x := qmap G d (f genZ)) ⟨k, hk, hxk⟩ rfl

/-- **`E` is open.** -/
theorem E_isOpenMap : IsOpenMap (Eexp G) := by
  have : SigmaCompactSpace (nala G) := sigmaCompact_nala hι hd
  have : SigmaCompactSpace (arla G) := by
    rw [← isSigmaCompact_univ_iff]
    have : (Set.univ : Set (arla G)) = Set.range (arlaEquiv hd hι).symm := by
      rw [(arlaEquiv hd hι).symm.surjective.range_eq]
    rw [this]
    exact isSigmaCompact_range (arlaEquiv hd hι).symm.continuous
  exact MonoidHom.isOpenMap_of_sigmaCompact _ (E_surjective hι hd) (continuous_Eexp G)

end Data

/-- **Theorem `adelic-exponential-lie-category`.** For a finite-dimensional protorus `G`,
`n = dim_a G`, the adelic exponential `exp(f) = f(1, 1)`, read on `nala(G) × arla(G)` as
`E(f, g) = f(1) · g(1)`, is continuous, surjective and open, with discrete kernel isomorphic
to `ℚⁿ`. -/
theorem adelic_exponential_lie_category [ConnectedSpace G]
    [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    (∀ f, expAd G f = Eexp G (adlaEquiv G f)) ∧ Continuous (Eexp G) ∧
      Function.Surjective (Eexp G) ∧ IsOpenMap (Eexp G) ∧
      DiscreteTopology (Eexp G).ker ∧ Nonempty ((Eexp G).ker ≃* Multiplicative (Fin (dimA G) → ℚ)) := by
  have : DiscreteTopology (PontryaginDual G) := discreteTopology_dual
  obtain ⟨ι, hι, hZ⟩ := exists_rank_embedding (dual_additive_torsionFree G)
  choose d hd using hZ
  exact ⟨expAd_eq_Eexp G, continuous_Eexp G, E_surjective hι hd, E_isOpenMap hι hd,
    discrete_kerE hι hd, ⟨kerE_equiv hι hd⟩⟩

end AdelicToriLean
