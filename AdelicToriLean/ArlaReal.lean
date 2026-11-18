import AdelicToriLean.AdelicExp
import AdelicToriLean.RealDual

/-!
# `arla(G) ≅ ℝⁿ`

Let `G` be a protorus, `ι : G^∨ → ℚⁿ` injective and `d_j ∈ G^∨` with `ι(d_j) = e_j`.

* `psiA v`: the character `x ↦ ∏ⱼ d_j(v(x_j))` of `ℝⁿ`, for `v ∈ arla(G) = Hom(ℝ, G)`;
* `vθ θ ∈ arla(G)`: `t ↦` the point of `G` with `χ ↦ exp(t ∑ⱼ ι(χ)_j θ_j)` (double duality);
* `arlaEquiv : arla(G) ≃ₜ* ℝⁿ`, `v ↦ realSelfDual⁻¹(psiA v)`.

`arla_real`: for a finite-dimensional protorus, `arla(G) ≅ ℝ^{dim_a G}`.
-/

open Topology TensorProduct

noncomputable section

namespace AdelicToriLean

instance : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
instance : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]
variable {n : ℕ} (ι : Additive (PontryaginDual G) →+ (Fin n → ℚ))
  (d : Fin n → Additive (PontryaginDual G))

/-- `x ↦ ∏ⱼ d_j(v(x_j))`. -/
def psiA (d : Fin n → Additive (PontryaginDual G)) (v : arla G) : PontryaginDual (Multiplicative (Fin n → ℝ)) :=
  ⟨{ toFun := fun x => ∏ j, (Additive.toMul (d j))
        (v (Multiplicative.ofAdd (Multiplicative.toAdd x j)))
     map_one' := by simp
     map_mul' := fun x y => by
       rw [← Finset.prod_mul_distrib]
       refine Finset.prod_congr rfl fun j _ => ?_
       rw [← map_mul, ← map_mul]
       rfl },
    by
      show Continuous fun x : Multiplicative (Fin n → ℝ) =>
        ∏ j, (Additive.toMul (d j)) (v (Multiplicative.ofAdd (Multiplicative.toAdd x j)))
      exact continuous_finsetProd _ fun j _ => (Additive.toMul (d j)).continuous.comp
        (v.continuous.comp (continuous_ofAdd.comp ((continuous_apply j).comp continuous_toAdd)))⟩

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem psiA_apply (v : arla G) (x : Multiplicative (Fin n → ℝ)) :
    psiA d v x = ∏ j, (Additive.toMul (d j)) (v (Multiplicative.ofAdd (Multiplicative.toAdd x j))) :=
  rfl

omit [CompactSpace G] [T2Space G] in
theorem psiA_mul (v w : arla G) : psiA d (v * w) = psiA d v * psiA d w := by
  refine ContinuousMonoidHom.ext fun x => ?_
  show ∏ j, (Additive.toMul (d j)) ((v * w) (Multiplicative.ofAdd (Multiplicative.toAdd x j))) =
    (∏ j, (Additive.toMul (d j)) (v (Multiplicative.ofAdd (Multiplicative.toAdd x j)))) *
    ∏ j, (Additive.toMul (d j)) (w (Multiplicative.ofAdd (Multiplicative.toAdd x j)))
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  show (Additive.toMul (d j)) (v _ * w _) = _
  rw [map_mul]

omit [CompactSpace G] [T2Space G] in
theorem continuous_psiA : Continuous (psiA d : arla G → _) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : arla G × Multiplicative (Fin n → ℝ) =>
    ∏ j, (Additive.toMul (d j)) (p.1 (Multiplicative.ofAdd (Multiplicative.toAdd p.2 j))))
  exact continuous_finsetProd _ fun j _ => (Additive.toMul (d j)).continuous.comp
    (continuous_eval.comp (continuous_fst.prodMk
      (continuous_ofAdd.comp ((continuous_apply j).comp (continuous_toAdd.comp continuous_snd)))))

/-- The real coefficient `∑ⱼ ι(χ)_j θ_j`. -/
def coef (ι : Additive (PontryaginDual G) →+ (Fin n → ℚ)) (θ : Fin n → ℝ) (χ : PontryaginDual G) : ℝ :=
  ∑ j, ((ι (Additive.ofMul χ) j : ℚ) : ℝ) * θ j

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem coef_mul (θ : Fin n → ℝ) (χ χ' : PontryaginDual G) :
    coef ι θ (χ * χ') = coef ι θ χ + coef ι θ χ' := by
  simp only [coef, ofMul_mul, map_add, Pi.add_apply, Rat.cast_add, add_mul,
    Finset.sum_add_distrib]

variable [DiscreteTopology (PontryaginDual G)]

/-- `χ ↦ exp(t · coef θ χ)`, a point of the double dual. -/
def phi (ι : Additive (PontryaginDual G) →+ (Fin n → ℚ)) (θ : Fin n → ℝ) (t : ℝ) : PontryaginDual (PontryaginDual G) :=
  ⟨{ toFun := fun χ => Circle.exp (t * coef ι θ χ)
     map_one' := by
       show Circle.exp (t * coef ι θ 1) = 1
       simp [coef]
     map_mul' := fun χ χ' => by
       show Circle.exp (t * coef ι θ (χ * χ')) = _
       rw [coef_mul, mul_add, Circle.exp_add] },
    continuous_of_discreteTopology⟩

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem phi_apply (θ : Fin n → ℝ) (t : ℝ) (χ : PontryaginDual G) :
    phi ι θ t χ = Circle.exp (t * coef ι θ χ) := rfl

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem continuous_phi_uncurry :
    Continuous (fun p : (Fin n → ℝ) × ℝ => phi ι p.1 p.2) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun q : ((Fin n → ℝ) × ℝ) × PontryaginDual G =>
    Circle.exp (q.1.2 * coef ι q.1.1 q.2))
  rw [continuous_prod_of_discrete_right]
  intro χ
  show Continuous fun p : (Fin n → ℝ) × ℝ =>
    Circle.exp (p.2 * ∑ j, ((ι (Additive.ofMul χ) j : ℚ) : ℝ) * p.1 j)
  exact Circle.exp.continuous.comp (continuous_snd.mul (continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp continuous_fst)))

/-- The one-parameter subgroup `vθ θ`. -/
def vθ (ι : Additive (PontryaginDual G) →+ (Fin n → ℚ)) (θ : Fin n → ℝ) : arla G :=
  ⟨{ toFun := fun t => (PontryaginDual.toDoubleDual G).symm (phi ι θ (Multiplicative.toAdd t))
     map_one' := by
       rw [← map_one (PontryaginDual.toDoubleDual G).symm]
       congr 1
       refine ContinuousMonoidHom.ext fun χ => ?_
       show Circle.exp (Multiplicative.toAdd (1 : Multiplicative ℝ) * coef ι θ χ) = 1
       rw [toAdd_one, zero_mul, Circle.exp_zero]
     map_mul' := fun s t => by
       rw [← map_mul]
       congr 1
       refine ContinuousMonoidHom.ext fun χ => ?_
       show Circle.exp (Multiplicative.toAdd (s * t) * coef ι θ χ) =
         Circle.exp (Multiplicative.toAdd s * coef ι θ χ) *
         Circle.exp (Multiplicative.toAdd t * coef ι θ χ)
       rw [toAdd_mul, add_mul, Circle.exp_add] },
    (PontryaginDual.toDoubleDual G).symm.continuous.comp
      ((continuous_phi_uncurry ι).comp (continuous_const.prodMk continuous_toAdd))⟩

theorem toDoubleDual_vθ (θ : Fin n → ℝ) (t : Multiplicative ℝ) :
    PontryaginDual.toDoubleDual G (vθ ι θ t) = phi ι θ (Multiplicative.toAdd t) :=
  (PontryaginDual.toDoubleDual G).apply_symm_apply _

theorem continuous_vθ : Continuous (vθ ι : (Fin n → ℝ) → arla G) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : (Fin n → ℝ) × Multiplicative ℝ =>
    (PontryaginDual.toDoubleDual G).symm (phi ι p.1 (Multiplicative.toAdd p.2)))
  exact (PontryaginDual.toDoubleDual G).symm.continuous.comp
    ((continuous_phi_uncurry ι).comp (continuous_fst.prodMk (continuous_toAdd.comp continuous_snd)))

variable {ι d} (hd : ∀ j, ι (d j) = Pi.single j 1)
include hd

theorem d_vθ (θ : Fin n → ℝ) (j : Fin n) (t : Multiplicative ℝ) :
    (Additive.toMul (d j)) (vθ ι θ t) = Circle.exp (Multiplicative.toAdd t * θ j) := by
  have h : (Additive.toMul (d j)) (vθ ι θ t) =
      PontryaginDual.toDoubleDual G (vθ ι θ t) (Additive.toMul (d j)) := rfl
  rw [h, toDoubleDual_vθ, phi_apply, coef]
  congr 2
  rw [show Additive.ofMul (Additive.toMul (d j)) = d j from rfl, hd j, Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Pi.single_eq_of_ne hij]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem psiA_vθ (θ : Multiplicative (Fin n → ℝ)) :
    psiA d (vθ ι (Multiplicative.toAdd θ)) = realSelfDual θ := by
  refine ContinuousMonoidHom.ext fun x => ?_
  show ∏ j, (Additive.toMul (d j)) ((vθ ι (Multiplicative.toAdd θ))
    (Multiplicative.ofAdd (Multiplicative.toAdd x j))) = chiRn θ x
  rw [chiRn_apply, exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [d_vθ hd, toAdd_ofAdd, mul_comm]

omit [DiscreteTopology (PontryaginDual G)] in
theorem psiA_injective (hι : Function.Injective ι) {v w : arla G} (h : psiA d v = psiA d w) :
    v = w := by
  -- `d_j ∘ v = d_j ∘ w`
  have hj : ∀ j (s : Multiplicative ℝ),
      (Additive.toMul (d j)) (v s) = (Additive.toMul (d j)) (w s) := by
    intro j s
    have := DFunLike.congr_fun h (Multiplicative.ofAdd (Pi.single j (Multiplicative.toAdd s)))
    rw [psiA_apply, psiA_apply, Finset.prod_eq_single j, Finset.prod_eq_single j] at this
    · simpa using this
    all_goals first
      | (intro i _ hij; simp [Pi.single_eq_of_ne hij])
      | (intro hj'; exact absurd (Finset.mem_univ j) hj')
  -- every character
  have hall : ∀ (χ : PontryaginDual G) (s : Multiplicative ℝ), χ (v s) = χ (w s) := by
    intro χ
    obtain ⟨m, hm, k, hk⟩ := exists_int_multiple (ι (Additive.ofMul χ))
    have hrel : m • Additive.ofMul χ = ∑ j, k j • d j := hι (by
      rw [map_nsmul, map_sum]
      funext i
      simp [Finset.sum_apply, hd, Pi.single_apply, nsmul_eq_mul, hk])
    have hpow : ∀ y : G, χ y ^ m = ∏ j, (Additive.toMul (d j) y) ^ k j := by
      intro y
      let ev : Additive (PontryaginDual G) →+ Additive Circle :=
        { toFun := fun c => Additive.ofMul (Additive.toMul c y)
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have h1 := congrArg (fun c => Additive.toMul (ev c)) hrel
      simp only [map_nsmul, map_sum, map_zsmul, toMul_nsmul, toMul_sum, toMul_zsmul] at h1
      exact h1
    set ρ : PontryaginDual (Multiplicative ℝ) :=
      (χ.comp v) * (χ.comp w)⁻¹
    have hρ : ρ ^ m = 1 := by
      refine ContinuousMonoidHom.ext fun s => ?_
      erw [ContinuousMonoidHom.pow_apply, PontryaginDual.one_apply]
      show (χ (v s) * (χ (w s))⁻¹) ^ m = 1
      rw [mul_pow, inv_pow, hpow, hpow]
      simp only [hj, mul_inv_cancel]
    have h1 := dual_torsionFree ρ hm hρ
    intro s
    have := DFunLike.congr_fun h1 s
    rw [PontryaginDual.one_apply] at this
    exact mul_inv_eq_one.mp this
  refine ContinuousMonoidHom.ext fun s => ?_
  apply (PontryaginDual.toDoubleDual G).injective
  refine ContinuousMonoidHom.ext fun χ => ?_
  exact hall χ s

/-- **`arla(G) ≅ ℝⁿ`.** -/
def arlaEquiv (hι : Function.Injective ι) : arla G ≃ₜ* Multiplicative (Fin n → ℝ) where
  toFun v := realSelfDual.symm (psiA d v)
  invFun θ := vθ ι (Multiplicative.toAdd θ)
  left_inv v := by
    apply psiA_injective hd hι
    rw [psiA_vθ hd, ContinuousMulEquiv.apply_symm_apply]
  right_inv θ := by
    show realSelfDual.symm (psiA d (vθ ι (Multiplicative.toAdd θ))) = θ
    rw [psiA_vθ hd, ContinuousMulEquiv.symm_apply_apply]
  map_mul' v w := by rw [psiA_mul, map_mul]
  continuous_toFun := realSelfDual.symm.continuous.comp (continuous_psiA d)
  continuous_invFun := (continuous_vθ ι).comp continuous_toAdd

end AdelicToriLean

namespace AdelicToriLean

open TensorProduct

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [ConnectedSpace G]

/-- **`arla(G) ≅ ℝⁿ`** for a finite-dimensional protorus, `n = dim_a G`. -/
theorem arla_real [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    Nonempty (arla G ≃ₜ* Multiplicative (Fin (dimA G) → ℝ)) := by
  have : DiscreteTopology (PontryaginDual G) := discreteTopology_dual
  obtain ⟨ι, hι, hZ⟩ := exists_rank_embedding (dual_additive_torsionFree G)
  choose d hd using hZ
  exact ⟨arlaEquiv hd hι⟩

/-- **Theorem `symmetric-adelic-lie-algebra`** (all assertions except `dim_n nala(G) = dim_n G`
and the cited uniqueness statements). For a finite-dimensional protorus `G`, `n = dim_a G`:
`adla(G) ≅ nala(G) × arla(G)`; `nala(G)` is a divisible periodic LCA group with
`ev_1 : nala(G) ≅ td(G)`; `arla(G) ≅ ℝⁿ`; and the adelic exponential is
`exp(f) = exp_n(f|ℤ̂) · exp_a(f|ℝ)`. -/
theorem symmetric_adelic_lie_algebra_fd
    [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    Nonempty (adla G ≃ₜ* nala G × arla G) ∧
      (T2Space (nala G) ∧ LocallyCompactSpace (nala G) ∧
        ∀ f : nala G, ∃ K : Subgroup (nala G), IsOpen (K : Set (nala G)) ∧
          IsCompact (K : Set (nala G)) ∧ f ∈ K) ∧
      (∀ (f : nala G) (m : ℕ), 0 < m → ∃ g : nala G, g ^ m = f) ∧
      Nonempty (arla G ≃ₜ* Multiplicative (Fin (dimA G) → ℝ)) ∧
      (∀ f : adla G, expAd G f = expn G (adlaEquiv G f).1 * expa G (adlaEquiv G f).2) := by
  obtain ⟨Δ, hΔ⟩ := exists_delta G
  obtain ⟨h1, h2, h3, -⟩ := nala_periodic_lca G
  exact ⟨symmetric_adelic_lie_algebra G, ⟨h1, h2, h3⟩, fun f m hm => nala_divisible hΔ f hm,
    arla_real G, expAd_eq G⟩

end AdelicToriLean
