import AdelicToriLean.NonarchExp
import AdelicToriLean.Protorus
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# Delta-subgroups and `K_Δ ≅ Δ`

* `IsDelta Δ n`: `Δ` closed, totally disconnected, `G/Δ ≅ (ℝ/ℤ)ⁿ` (written `Fin n → Circle`);
* `torus_nss`: the torus has no small subgroups;
* `act`, `continuous_act`: the canonical `ℤ̂`-action `x ↦ (z ↦ z · x)` on a profinite abelian group
  is jointly continuous, so `x ↦ (z ↦ z · x)` is continuous into `Hom(ℤ̂, P)`;
* `Kdelta Δ = {f ∈ nala(G) : f(ℤ̂) ⊆ Δ}`: `isOpen_Kdelta`, and `kdeltaEquiv : K_Δ ≃ₜ* Δ` given by
  evaluation at `1`.
-/

open Topology Circle Real Filter

noncomputable section

namespace AdelicToriLean

/-- The real torus `(ℝ/ℤ)ⁿ`, written multiplicatively. -/
abbrev Torus (n : ℕ) := Fin n → Circle

/-- **No small subgroups.** -/
theorem torus_nss (n : ℕ) : ∃ U : Set (Torus n), IsOpen U ∧ (1 : Torus n) ∈ U ∧
    ∀ H : Subgroup (Torus n), (H : Set (Torus n)) ⊆ U → H = ⊥ := by
  refine ⟨Set.pi Set.univ fun _ => centeredArc (π / 2),
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_centeredArc _), ?_, ?_⟩
  · intro i _
    rw [Pi.one_apply, mem_centeredArc (by linarith [pi_pos])]
    simp [pi_pos]
  · intro H hH
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    funext i
    have hb := subgroup_le_centeredArc (H.map (Pi.evalMonoidHom (fun _ => Circle) i)) (by
      rintro _ ⟨w, hw, rfl⟩; exact hH hw i (Set.mem_univ i))
    have hm : y i ∈ H.map (Pi.evalMonoidHom (fun _ => Circle) i) := ⟨y, hy, rfl⟩
    rw [hb, Subgroup.mem_bot] at hm
    exact hm

/-- Torsion points of the circle are dense. -/
theorem dense_torsion_circle : Dense {z : Circle | ∃ k : ℕ, 0 < k ∧ z ^ k = 1} := by
  set g : ℝ → Circle := fun x => Circle.exp (x * (2 * π))
  have hgc : Continuous g := Circle.exp.continuous.comp (continuous_id.mul continuous_const)
  have hgs : Function.Surjective g := by
    intro z
    refine ⟨Complex.arg z / (2 * π), ?_⟩
    simp only [g]
    rw [div_mul_cancel₀ _ (by positivity), exp_arg]
  have hd : DenseRange (g ∘ (Rat.cast : ℚ → ℝ)) :=
    hgs.denseRange.comp Rat.denseRange_cast hgc
  refine hd.mono ?_
  rintro _ ⟨r, rfl⟩
  refine ⟨r.den, r.den_pos, ?_⟩
  simp only [Function.comp_apply, g]
  rw [← zpow_natCast, ← Circle.exp_zsmul, zsmul_eq_mul, ← mul_assoc]
  push_cast
  rw [show (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) by exact_mod_cast Rat.den_mul_eq_num r,
    Circle.exp_int_mul_two_pi]

/-- Torsion points of the torus are dense. -/
theorem dense_torsion_torus (n : ℕ) : Dense {y : Torus n | ∃ k : ℕ, 0 < k ∧ y ^ k = 1} := by
  refine (dense_pi Set.univ fun _ _ => dense_torsion_circle).mono ?_
  intro y hy
  choose k hk using fun i => hy i (Set.mem_univ i)
  refine ⟨∏ i, k i, Finset.prod_pos fun i _ => (hk i).1, ?_⟩
  funext i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ i)
  rw [Pi.pow_apply, hc, pow_mul, (hk i).2, one_pow, Pi.one_apply]

theorem circle_exp_one_not_torsion : ∀ k : ℕ, 0 < k → Circle.exp 1 ^ k ≠ 1 := by
  intro k hk h
  rw [← zpow_natCast, ← Circle.exp_zsmul, Circle.exp_eq_one] at h
  obtain ⟨m, hm⟩ := h
  simp only [zsmul_eq_mul, Int.cast_natCast, mul_one] at hm
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hm; exact (Nat.cast_pos.mpr hk).ne' hm
  apply irrational_pi
  refine ⟨(k : ℚ) / (2 * m), ?_⟩
  push_cast
  field_simp
  linarith

section Act

variable {P : Type*} [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P]

/-- The canonical `ℤ̂`-action: `act x z = z · x`. -/
def act (x : P) : ContinuousMonoidHom (Multiplicative ZHat) P :=
  Classical.choose (exists_zhatHom x)

theorem act_genZ (x : P) : act x genZ = x := Classical.choose_spec (exists_zhatHom x)

theorem act_mul (x y : P) : act (x * y) = act x * act y :=
  zhatHom_ext (by rw [ContinuousMonoidHom.mul_apply, act_genZ, act_genZ, act_genZ])

theorem act_iZ (x : P) (m : ℤ) : act x (Multiplicative.ofAdd (iZ m)) = x ^ m := by
  rw [show Multiplicative.ofAdd (iZ m) = genZ ^ m by simp [genZ, iZ, ← ofAdd_zsmul], map_zpow,
    act_genZ]

/-- Values of the action of `y ∈ V` lie in the closed subgroup `V`. -/
theorem act_mem (V : Subgroup P) (hV : IsClosed (V : Set P)) {y : P} (hy : y ∈ V)
    (z : Multiplicative ZHat) : act y z ∈ V := by
  have hc : IsClosed {a : ZHat | act y (Multiplicative.ofAdd a) ∈ V} :=
    hV.preimage ((act y).continuous.comp continuous_ofAdd)
  have hsub : Set.range iZ ⊆ {a : ZHat | act y (Multiplicative.ofAdd a) ∈ V} := by
    rintro _ ⟨m, rfl⟩
    show act y (Multiplicative.ofAdd (iZ m)) ∈ V
    rw [act_iZ]; exact V.zpow_mem hy m
  have : Multiplicative.toAdd z ∈ closure (Set.range iZ) := by
    rw [denseRange_iZ.closure_range]; trivial
  exact hc.closure_subset_iff.mpr hsub this

/-- **Joint continuity of the canonical `ℤ̂`-action.** -/
theorem continuous_act_uncurry :
    Continuous (fun p : P × Multiplicative ZHat => act p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, z0⟩ W hW
  obtain ⟨V, hVo, hVW⟩ := exists_coset_sub hW
  have : Finite (P ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo
  have : V.FiniteIndex := V.finiteIndex_of_finite_quotient
  set d := V.index
  have hd : 0 < d := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hVc : IsClosed (V : Set P) := Subgroup.isClosed_of_isOpen V hVo
  set A : Set P := {x | x0⁻¹ * x ∈ V}
  set Z : Set (Multiplicative ZHat) := {z | Multiplicative.toAdd (z0⁻¹ * z) ∈ nsmulZ d}
  have hA : A ∈ 𝓝 x0 := (hVo.preimage (continuous_const_mul x0⁻¹)).mem_nhds
    (by simp [V.one_mem])
  have hZ : Z ∈ 𝓝 z0 := ((isOpen_nsmulZ d hd).preimage
    (continuous_toAdd.comp (continuous_const_mul z0⁻¹))).mem_nhds
    (by simp [(nsmulZ d).zero_mem])
  rw [Filter.mem_map]
  refine mem_of_superset (prod_mem_nhds hA hZ) ?_
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  show act x z ∈ W
  apply hVW
  obtain ⟨w, hw⟩ := mem_nsmulZ.mp hz
  have h1 : act x0 (z0⁻¹ * z) ∈ V := by
    rw [show z0⁻¹ * z = (Multiplicative.ofAdd w) ^ d by
      rw [← ofAdd_nsmul, hw]; rfl, map_pow]
    exact V.pow_index_mem _
  have h2 : act (x0⁻¹ * x) z ∈ V := act_mem V hVc hx z
  have e : (act x0 z0)⁻¹ * act x z = act x0 (z0⁻¹ * z) * act (x0⁻¹ * x) z := by
    rw [show x = x0 * (x0⁻¹ * x) by group, act_mul, ContinuousMonoidHom.mul_apply, map_mul,
      map_inv]
    group
  rw [e]
  exact V.mul_mem h1 h2

theorem continuous_act : Continuous (act : P → ContinuousMonoidHom (Multiplicative ZHat) P) :=
  ContinuousMonoidHom.continuous_of_continuous_uncurry _ continuous_act_uncurry

end Act

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A **delta-subgroup** of `G`: closed, totally disconnected, with `G/Δ ≅ (ℝ/ℤ)ⁿ`. -/
structure IsDelta (Δ : Subgroup G) (n : ℕ) : Prop where
  closed : IsClosed (Δ : Set G)
  td : IsTotallyDisconnected (Δ : Set G)
  quot : Nonempty (G ⧸ Δ ≃ₜ* Torus n)

/-- The quotient map `G → G/Δ ≅ (ℝ/ℤ)ⁿ`. -/
theorem IsDelta.exists_map {Δ : Subgroup G} {n : ℕ} (h : IsDelta Δ n) :
    ∃ q : G →* Torus n, Continuous q ∧ IsOpenMap q ∧ Function.Surjective q ∧
      ∀ x, q x = 1 ↔ x ∈ Δ := by
  obtain ⟨e⟩ := h.quot
  refine ⟨e.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' Δ),
    e.continuous.comp continuous_quot_mk, e.isOpenMap.comp QuotientGroup.isOpenMap_coe,
    e.surjective.comp (QuotientGroup.mk'_surjective Δ), fun x => ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
  show e (x : G ⧸ Δ) = 1 ↔ x ∈ Δ
  rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]

/-- `K_Δ = {f ∈ nala(G) : f(ℤ̂) ⊆ Δ}`. -/
def Kdelta (Δ : Subgroup G) : Subgroup (nala G) where
  carrier := {f | ∀ z, f z ∈ Δ}
  mul_mem' hf hg z := Δ.mul_mem (hf z) (hg z)
  one_mem' _ := Δ.one_mem
  inv_mem' {f} hf z := by
    show (f z)⁻¹ ∈ Δ
    exact Δ.inv_mem (hf z)

theorem mem_Kdelta {Δ : Subgroup G} {f : nala G} : f ∈ Kdelta Δ ↔ ∀ z, f z ∈ Δ := Iff.rfl

/-- **`K_Δ` is open in `nala(G)`.** -/
theorem isOpen_Kdelta {Δ : Subgroup G} {n : ℕ} (h : IsDelta Δ n) :
    IsOpen (Kdelta Δ : Set (nala G)) := by
  obtain ⟨q, hqc, -, -, hq⟩ := h.exists_map
  obtain ⟨U, hUo, hU1, hU⟩ := torus_nss n
  set S : Set (nala G) := {f | Set.MapsTo f Set.univ (q ⁻¹' U)}
  have hS : IsOpen S :=
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ (hUo.preimage hqc)).preimage
      (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous
  have h1 : (1 : nala G) ∈ S := fun z _ => by
    show q 1 ∈ U
    rw [map_one]; exact hU1
  have hSK : S ⊆ Kdelta Δ := by
    intro f hf z
    have hb := hU ((q.comp (f : Multiplicative ZHat →* G)).range) (by
      rintro _ ⟨w, rfl⟩; exact hf (Set.mem_univ w))
    have : q (f z) ∈ (q.comp (f : Multiplicative ZHat →* G)).range := ⟨z, rfl⟩
    rw [hb, Subgroup.mem_bot] at this
    exact (hq _).mp this
  exact Subgroup.isOpen_of_mem_nhds _ (mem_of_superset (hS.mem_nhds h1) hSK)

section Compact

variable [CompactSpace G] [T2Space G]

/-- **`K_Δ ≅ Δ`**: evaluation at `1` is a topological isomorphism. -/
def kdeltaEquiv (Δ : Subgroup G) (hc : IsClosed (Δ : Set G))
    (htd : IsTotallyDisconnected (Δ : Set G)) : Kdelta Δ ≃ₜ* Δ :=
  haveI : CompactSpace Δ := isCompact_iff_compactSpace.mp hc.isCompact
  haveI : TotallyDisconnectedSpace Δ := totallyDisconnectedSpace_subtype_iff.mpr htd
  let ι : ContinuousMonoidHom Δ G := ⟨Δ.subtype, continuous_subtype_val⟩
  { toFun := fun f => ⟨(f : nala G) genZ, f.2 genZ⟩
    invFun := fun x => ⟨ι.comp (act x), fun z => (act x z).2⟩
    left_inv := fun f => by
      apply Subtype.ext
      apply zhatHom_ext
      show ((act (⟨(f : nala G) genZ, f.2 genZ⟩ : Δ) genZ : Δ) : G) = (f : nala G) genZ
      rw [act_genZ]
    right_inv := fun x => by
      apply Subtype.ext
      show ((act x genZ : Δ) : G) = x
      rw [act_genZ]
    map_mul' := fun _ _ => rfl
    continuous_toFun :=
      ((continuous_expn G).comp continuous_subtype_val).subtype_mk _
    continuous_invFun :=
      ((ContinuousMonoidHom.continuous_comp_right ι).comp continuous_act).subtype_mk _ }

theorem kdeltaEquiv_apply (Δ : Subgroup G) (hc : IsClosed (Δ : Set G))
    (htd : IsTotallyDisconnected (Δ : Set G)) (f : Kdelta Δ) :
    (kdeltaEquiv Δ hc htd f : G) = (f : nala G) genZ := rfl

/-- `exp_n(K_Δ) = Δ`. -/
theorem expn_image_Kdelta (Δ : Subgroup G) (hc : IsClosed (Δ : Set G))
    (htd : IsTotallyDisconnected (Δ : Set G)) :
    expn G '' (Kdelta Δ : Set (nala G)) = Δ := by
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩; exact hf genZ
  · intro hx
    obtain ⟨f, hf⟩ := (kdeltaEquiv Δ hc htd).surjective ⟨x, hx⟩
    exact ⟨f, f.2, congrArg Subtype.val hf⟩

end Compact

end AdelicToriLean
