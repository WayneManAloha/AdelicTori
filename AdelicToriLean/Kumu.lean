import AdelicToriLean.ArcDense

/-!
# Theorem `kumu`

For a finite-dimensional protorus `G`, let `a(G) = exp_a(Hom(ℝ, G))` (`arcSub`), the image of the
archimedean exponential (the paper's arc component of `0`), and let the **kumu** be
`κ(G) = td(G) ∩ a(G)` (`kumu`). `G` is **torus-free** (`TorusFree`) if it has no subgroup
topologically isomorphic to a torus `(ℝ/ℤ)^k`, `k ≥ 1`.

`kumu_theorem`: for a torus-free finite-dimensional protorus `G`, `n = dim_a G`, the kumu is a
dense, fully invariant subgroup, algebraically isomorphic to `ℚⁿ`.

* `expa_vθ_injective`: torus-free forces `θ ↦ exp_a(v_θ)` to be injective (a nonzero period
  gives an injective continuous `ℝ/ℤ → G`, i.e. a circle subgroup);
* `kumuEquiv : ℚⁿ ≃* κ(G)`, `r ↦ exp_a(v_{2πr})`;
* `dense_kumu`, `map_kumu_le`.
-/

open Topology TensorProduct Real

noncomputable section

namespace AdelicToriLean

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `a(G) = exp_a(Hom(ℝ, G))`. -/
def arcSub : Subgroup G := (expa G).range

/-- **The kumu** `κ(G) = td(G) ∩ a(G)`. -/
def kumu : Subgroup G := td G ⊓ arcSub G

/-- `G` is torus-free: no subgroup is topologically isomorphic to `(ℝ/ℤ)^k`, `k ≥ 1`. -/
def TorusFree : Prop :=
  ∀ (H : Subgroup G) (k : ℕ), 0 < k → IsEmpty (H ≃ₜ* (Fin k → Multiplicative (AddCircle (1 : ℝ))))

/-- **`κ(G)` is fully invariant** (functorial for continuous homomorphisms). -/
theorem map_kumu_le {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : ContinuousMonoidHom G H) : (kumu G).map (φ : G →* H) ≤ kumu H := by
  rintro _ ⟨x, ⟨hxt, ⟨g, rfl⟩⟩, rfl⟩
  exact ⟨map_td_le G φ ⟨_, hxt, rfl⟩, ⟨φ.comp g, rfl⟩⟩

/-- `(ℝ/ℤ)¹ ≅ ℝ/ℤ`. -/
def finOneEquiv (X : Type*) [Mul X] [TopologicalSpace X] : (Fin 1 → X) ≃ₜ* X where
  toFun f := f 0
  invFun x _ := x
  left_inv f := by funext i; rw [Subsingleton.elim i 0]
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_apply 0
  continuous_invFun := continuous_pi fun _ => continuous_id

theorem exp_pi_ne_one : Circle.exp π ≠ 1 := by
  intro h
  rw [Circle.exp_eq_one] at h
  obtain ⟨m, hm⟩ := h
  have : (1 : ℝ) = 2 * m := by
    have := pi_pos
    field_simp at hm
    nlinarith
  have : (2 * m : ℤ) = 1 := by exact_mod_cast this.symm
  omega

variable {G} [CompactSpace G] [T2Space G]

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- An injective continuous homomorphism `ℝ/ℤ → G` gives a circle subgroup. -/
theorem not_torusFree_of_injective (hT : TorusFree G)
    (Φ : ContinuousMonoidHom (Multiplicative (AddCircle (1 : ℝ))) G) (hΦ : Function.Injective Φ) :
    False := by
  set H := (Φ : Multiplicative (AddCircle (1 : ℝ)) →* G).range
  set e0 : Multiplicative (AddCircle (1 : ℝ)) ≃* H := MonoidHom.ofInjective hΦ
  have hcont : Continuous e0 := Φ.continuous.subtype_mk _
  set hom := hcont.homeoOfEquivCompactToT2 (f := e0.toEquiv)
  set e : Multiplicative (AddCircle (1 : ℝ)) ≃ₜ* H :=
    { e0 with continuous_toFun := hcont, continuous_invFun := hom.symm.continuous }
  exact (hT H 1 one_pos).false ((finOneEquiv _).trans e).symm

variable [DiscreteTopology (PontryaginDual G)] {n : ℕ}
  {ι : Additive (PontryaginDual G) →+ (Fin n → ℚ)} (hι : Function.Injective ι)
  {d : Fin n → Additive (PontryaginDual G)} (hd : ∀ j, ι (d j) = Pi.single j 1)

include hd in
/-- **Torus-free forces `θ ↦ exp_a(v_θ)` injective.** -/
theorem expa_vθ_injective (hT : TorusFree G) :
    Function.Injective fun θ : Fin n → ℝ => expa G (vθ ι θ) := by
  -- it is a homomorphism `ℝⁿ → G`; show the kernel is trivial
  suffices h0 : ∀ θ : Fin n → ℝ, expa G (vθ ι θ) = 1 → θ = 0 by
    intro θ θ' h
    have hmul : ∀ a b : Fin n → ℝ, vθ ι (a + b) = vθ ι a * vθ ι b := fun a b => by
      refine ContinuousMonoidHom.ext fun t => ?_
      apply (PontryaginDual.toDoubleDual G).injective
      refine ContinuousMonoidHom.ext fun χ => ?_
      rw [ContinuousMonoidHom.mul_apply, map_mul]
      show (PontryaginDual.toDoubleDual G (vθ ι (a + b) t)) χ =
        (PontryaginDual.toDoubleDual G (vθ ι a t)) χ * (PontryaginDual.toDoubleDual G (vθ ι b t)) χ
      rw [toDoubleDual_vθ, toDoubleDual_vθ, toDoubleDual_vθ]
      show Circle.exp (_ * coef ι (a + b) χ) =
        Circle.exp (_ * coef ι a χ) * Circle.exp (_ * coef ι b χ)
      rw [← Circle.exp_add, ← mul_add]
      congr 2
      simp only [coef, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have := h0 (θ - θ') (by
      have e1 : vθ ι θ = vθ ι (θ - θ') * vθ ι θ' := by rw [← hmul, sub_add_cancel]
      have h' : expa G (vθ ι θ) = expa G (vθ ι θ') := h
      rw [e1, map_mul] at h'
      exact mul_eq_right.mp h')
    exact sub_eq_zero.mp this
  intro θ hθ
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, θ j ≠ 0 := by
    by_contra h; simp only [not_exists, not_not] at h; exact hne (funext h)
  set v := vθ ι θ
  -- the additive one-parameter subgroup `ψ : ℝ → G`
  set ψ : ℝ →+ Additive G :=
    { toFun := fun t => Additive.ofMul (v (Multiplicative.ofAdd t))
      map_zero' := by simp
      map_add' := fun s t => by simp [ofAdd_add] }
  have hψc : Continuous ψ :=
    continuous_ofMul.comp (v.continuous.comp continuous_ofAdd)
  set K := ψ.ker
  have hKc : IsClosed (K : Set ℝ) := by
    have : (K : Set ℝ) = (fun t => v (Multiplicative.ofAdd t)) ⁻¹' {1} := by
      ext t; simp [K, ψ]
    rw [this]; exact isClosed_singleton.preimage (v.continuous.comp continuous_ofAdd)
  have h1K : (1 : ℝ) ∈ K := by
    show Additive.ofMul (v (Multiplicative.ofAdd 1)) = 0
    rw [show v (Multiplicative.ofAdd 1) = 1 from hθ]; rfl
  have hKtop : K ≠ ⊤ := by
    intro htop
    have hmem : π / θ j ∈ K := htop ▸ AddSubgroup.mem_top _
    have : (Additive.toMul (d j)) (v (Multiplicative.ofAdd (π / θ j))) = 1 := by
      have h' : v (Multiplicative.ofAdd (π / θ j)) = 1 := hmem
      rw [h', map_one]
    rw [d_vθ hd, toAdd_ofAdd, div_mul_cancel₀ _ hj] at this
    exact exp_pi_ne_one this
  -- `K = ℤ a`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, K = AddSubgroup.zmultiples a := by
    rcases AddSubgroup.dense_or_cyclic K with hd' | ⟨a, ha⟩
    · exact absurd (by
        rw [← SetLike.coe_set_eq, AddSubgroup.coe_top, ← hKc.closure_eq, hd'.closure_eq]) hKtop
    · exact ⟨a, by rw [ha, AddSubgroup.zmultiples_eq_closure]⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [ha] at h1K
    simp at h1K
  -- `w(t) = ψ(a t)` has kernel `ℤ`
  set w : ℝ →+ Additive G := ψ.comp (AddMonoidHom.mulLeft a)
  have hker : AddSubgroup.zmultiples (1 : ℝ) = w.ker := by
    ext t
    rw [AddMonoidHom.mem_ker]
    show t ∈ AddSubgroup.zmultiples (1 : ℝ) ↔ a * t ∈ K
    rw [ha, AddSubgroup.mem_zmultiples_iff, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, by simp [mul_comm]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have : (k : ℝ) * a = a * t := by simpa using hk
      simp only [zsmul_eq_mul, mul_one]
      exact (mul_right_cancel₀ ha0 (by rw [this, mul_comm])).symm
  set L : AddCircle (1 : ℝ) →+ Additive G :=
    QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℝ)) w hker.le
  have hLinj : Function.Injective L := (QuotientAddGroup.injective_lift_iff _ w hker.le).mpr hker
  have hLc : Continuous L :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
      (hψc.comp (continuous_const.mul continuous_id))
  set Φ : ContinuousMonoidHom (Multiplicative (AddCircle (1 : ℝ))) G :=
    ⟨AddMonoidHom.toMultiplicative L, continuous_toMul.comp (hLc.comp continuous_toAdd)⟩
  exact not_torusFree_of_injective hT Φ (fun x y h =>
    Multiplicative.toAdd.injective (hLinj (Additive.toMul.injective h)))

include hι hd in
/-- `x ∈ κ(G)` iff `x = exp_a(v_θ)` with `θ ∈ (2πℚ)ⁿ`. -/
theorem mem_kumu_iff (x : G) :
    x ∈ kumu G ↔ ∃ θ : Fin n → ℝ, (∀ j, ∃ r : ℚ, θ j = 2 * π * r) ∧ expa G (vθ ι θ) = x := by
  constructor
  · rintro ⟨hxt, ⟨g, rfl⟩⟩
    set θ := Multiplicative.toAdd (arlaEquiv hd hι g)
    have hg : vθ ι θ = g := (arlaEquiv hd hι).symm_apply_apply g
    refine ⟨θ, (vθ_one_mem_td_iff hι hd θ).mp ?_, by rw [hg]⟩
    rw [hg]; exact (mem_td_iff G).mp hxt
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨(mem_td_iff G).mpr ((vθ_one_mem_td_iff hι hd θ).mpr hθ), ⟨_, rfl⟩⟩

/-- `r ↦ exp_a(v_{2πr}) : ℚⁿ → G`. -/
def kumuMap : Multiplicative (Fin n → ℚ) →* G :=
  (expa G).comp ((arlaEquiv hd hι).symm.toMulEquiv.toMonoidHom.comp twoPiRat)

theorem kumuMap_apply (r : Multiplicative (Fin n → ℚ)) :
    kumuMap hι hd r = expa G (vθ ι (Multiplicative.toAdd (twoPiRat r))) := rfl

theorem kumuMap_injective (hT : TorusFree G) : Function.Injective (kumuMap hι hd) :=
  fun r s h => twoPiRat_injective (Multiplicative.toAdd.injective
    (expa_vθ_injective hd hT (by simpa [kumuMap_apply] using h)))

theorem range_kumuMap : (kumuMap hι hd).range = kumu G := by
  ext x
  rw [mem_kumu_iff hι hd]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨_, fun j => ⟨Multiplicative.toAdd r j, rfl⟩, rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    choose r hr using hθ
    refine ⟨Multiplicative.ofAdd r, ?_⟩
    rw [kumuMap_apply]
    congr 2
    funext j; exact (hr j).symm

/-- **`κ(G) ≅ ℚⁿ`** algebraically, for torus-free `G`. -/
def kumuEquiv (hT : TorusFree G) : Multiplicative (Fin n → ℚ) ≃* kumu G :=
  (MonoidHom.ofInjective (kumuMap_injective hι hd hT)).trans
    (MulEquiv.subgroupCongr (range_kumuMap hι hd))

omit [CompactSpace G] [T2Space G] [DiscreteTopology (PontryaginDual G)] in
theorem dense_twoPiRat : DenseRange (twoPiRat (n := n)) := by
  have h1 : DenseRange fun q : ℚ => 2 * π * (q : ℝ) :=
    (mul_left_surjective₀ (by positivity : (2 * π : ℝ) ≠ 0)).denseRange.comp
      Rat.denseRange_cast (continuous_const.mul continuous_id)
  have h2 : Dense (Set.range fun r : Fin n → ℚ => fun j => 2 * π * (r j : ℝ)) := by
    refine (dense_pi Set.univ fun _ _ => h1).mono ?_
    intro θ hθ
    choose r hr using fun j => hθ j (Set.mem_univ j)
    exact ⟨r, funext hr⟩
  exact h2

include hι hd in
/-- **`κ(G)` is dense.** -/
theorem dense_kumu : Dense (kumu G : Set G) := by
  rw [← range_kumuMap hι hd]
  have hsurj : DenseRange fun θ : Multiplicative (Fin n → ℝ) => expa G ((arlaEquiv hd hι).symm θ) := by
    have : Set.range (fun θ : Multiplicative (Fin n → ℝ) => expa G ((arlaEquiv hd hι).symm θ)) =
        Set.range (expa G) := by
      ext x
      constructor
      · rintro ⟨θ, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨arlaEquiv hd hι g, by
          show expa G ((arlaEquiv hd hι).symm (arlaEquiv hd hι g)) = expa G g
          rw [ContinuousMulEquiv.symm_apply_apply]⟩
    rw [DenseRange, this]
    exact dense_range_expa_of hι
  exact hsurj.comp dense_twoPiRat ((continuous_expa G).comp (arlaEquiv hd hι).symm.continuous)

end AdelicToriLean

namespace AdelicToriLean

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [ConnectedSpace G]

/-- **Theorem `kumu`.** For a torus-free finite-dimensional protorus `G`, `n = dim_a G`, the kumu
`κ(G) = td(G) ∩ a(G)` is a dense, fully invariant subgroup of `G`, algebraically isomorphic to
`ℚⁿ`. -/
theorem kumu_theorem [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))]
    (hT : TorusFree G) :
    Dense (kumu G : Set G) ∧
      (∀ φ : ContinuousMonoidHom G G, (kumu G).map (φ : G →* G) ≤ kumu G) ∧
      Nonempty (Multiplicative (Fin (dimA G) → ℚ) ≃* kumu G) := by
  have : DiscreteTopology (PontryaginDual G) := discreteTopology_dual
  obtain ⟨ι, hι, hZ⟩ := exists_rank_embedding (dual_additive_torsionFree G)
  choose d hd using hZ
  exact ⟨dense_kumu hι hd, fun φ => map_kumu_le G φ, ⟨kumuEquiv hι hd hT⟩⟩

end AdelicToriLean
