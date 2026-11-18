import AdelicToriLean.AdelicCover
import AdelicToriLean.NonarchExp
import AdelicToriLean.PerpQuot

/-!
# `dim_n Lie_n(G) = n`: the local covering modules

For a finite place `v = p` of `ℚ`, `ℚ_p = v.adicCompletion ℚ`. For a topological abelian group `L`,
`Hom(ℚ_p, L)` (continuous homomorphisms) is a `ℚ_p`-vector space under precomposition (`modHomV`),
and

  `d_p(L) := dim_{ℚ_p} Hom(ℚ_p, L)` (`dP`),  `dim_n L := sup_p d_p(L)` (`dimNL`).

`d_p` is invariant under topological isomorphism by construction.

For `G = A^∨` (`A ⊆ ℚⁿ` of rank `n`) and `L = Lie_n(G) = Hom(ℤ̂, G)`:

* `homNalaEquiv`: `Hom(ℚ_p, Hom(ℤ̂, G)) ≅ Hom(ℚ_p, G)`, `F ↦ (x ↦ F(x)(1))`, inverse
  `f ↦ (x ↦ (z ↦ f(z_p x)))`; `ℚ_p`-linear;
* `thetaV`: `Hom(ℚ_p, A^∨) ≅ ℚ_pⁿ` (local characters `x ↦ e(fr_p(c x))`, obtained from the
  self-duality of `ℚ̂`);
* **`dP_nala`: `d_p(Lie_n G) = n` for every `p`**, hence **`dimNL_nala`: `dim_n Lie_n(G) = n`**,
  with no torus-free hypothesis (for `G = 𝕋ⁿ`, `Lie_n(G) ≅ (ℚ/ℤ)ⁿ`).
-/

open Topology IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

attribute [local instance] Classical.decEq

noncomputable section

namespace AdelicToriLean

variable (v : HeightOneSpectrum ℤ)

/-! ### `Hom(ℚ_p, L)` as a `ℚ_p`-vector space -/

/-- `Hom(ℚ_p, L)`. -/
abbrev HomV (L : Type*) [CommGroup L] [TopologicalSpace L] :=
  ContinuousMonoidHom (Multiplicative (v.adicCompletion ℚ)) L

/-- Multiplication by `r` on `ℚ_p`. -/
def mulV (r : v.adicCompletion ℚ) :
    ContinuousMonoidHom (Multiplicative (v.adicCompletion ℚ)) (Multiplicative (v.adicCompletion ℚ)) :=
  ⟨{ toFun := fun x => Multiplicative.ofAdd (r * Multiplicative.toAdd x)
     map_one' := by simp
     map_mul' := fun x y => by simp [mul_add] },
    continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)⟩

variable {L : Type*} [CommGroup L] [TopologicalSpace L] [IsTopologicalGroup L]

instance smulHomV : SMul (v.adicCompletion ℚ) (Additive (HomV v L)) where
  smul r f := Additive.ofMul ((Additive.toMul f).comp (mulV v r))

omit [IsTopologicalGroup L] in
theorem smulHomV_apply (r : v.adicCompletion ℚ) (f : HomV v L)
    (x : Multiplicative (v.adicCompletion ℚ)) :
    Additive.toMul (r • Additive.ofMul f) x =
      f (Multiplicative.ofAdd (r * Multiplicative.toAdd x)) := rfl

/-- **`Hom(ℚ_p, L)` is a `ℚ_p`-vector space** (precomposition). -/
instance modHomV : Module (v.adicCompletion ℚ) (Additive (HomV v L)) where
  one_smul f := by
    apply Additive.toMul.injective
    refine ContinuousMonoidHom.ext fun x => ?_
    show (Additive.toMul f) (Multiplicative.ofAdd (1 * Multiplicative.toAdd x)) = _
    rw [one_mul]; rfl
  mul_smul r s f := by
    apply Additive.toMul.injective
    refine ContinuousMonoidHom.ext fun x => ?_
    show (Additive.toMul f) (Multiplicative.ofAdd (r * s * Multiplicative.toAdd x)) =
      (Additive.toMul f) (Multiplicative.ofAdd (s * (r * Multiplicative.toAdd x)))
    congr 2; ring
  smul_zero r := by
    apply Additive.toMul.injective
    refine ContinuousMonoidHom.ext fun x => ?_
    rfl
  smul_add r f g := by
    apply Additive.toMul.injective
    refine ContinuousMonoidHom.ext fun x => ?_
    rfl
  add_smul r s f := by
    apply Additive.toMul.injective
    refine ContinuousMonoidHom.ext fun x => ?_
    show (Additive.toMul f) (Multiplicative.ofAdd ((r + s) * Multiplicative.toAdd x)) =
      (Additive.toMul f) (Multiplicative.ofAdd (r * Multiplicative.toAdd x)) *
        (Additive.toMul f) (Multiplicative.ofAdd (s * Multiplicative.toAdd x))
    rw [← map_mul, add_mul]; rfl
  zero_smul f := by
    apply Additive.toMul.injective
    refine ContinuousMonoidHom.ext fun x => ?_
    show (Additive.toMul f) (Multiplicative.ofAdd (0 * Multiplicative.toAdd x)) = 1
    rw [zero_mul]; exact map_one _

variable (L) in
/-- **`d_p(L) = dim_{ℚ_p} Hom(ℚ_p, L)`.** -/
def dP : ℕ := Module.finrank (v.adicCompletion ℚ) (Additive (HomV v L))

variable (L) in
/-- **`dim_n L = sup_p d_p(L)`.** -/
def dimNL : ℕ := ⨆ v : HeightOneSpectrum ℤ, dP v L

/-! ### Local characters -/

/-- `x ↦ e(fr_p(c x))`. -/
def chiV (c : v.adicCompletion ℚ) : PontryaginDual (Multiplicative (v.adicCompletion ℚ)) :=
  ⟨{ toFun := fun x => AddCircle.toCircle (frV v (c * Multiplicative.toAdd x))
     map_one' := by simp
     map_mul' := fun x y => by simp [mul_add, AddCircle.toCircle_add] },
    AddCircle.continuous_toCircle.comp ((continuous_frV v).comp
      (continuous_const.mul continuous_toAdd))⟩

theorem chiV_apply (c : v.adicCompletion ℚ) (x : Multiplicative (v.adicCompletion ℚ)) :
    chiV v c x = AddCircle.toCircle (frV v (c * Multiplicative.toAdd x)) := rfl

theorem chiV_add (c c' : v.adicCompletion ℚ) : chiV v (c + c') = chiV v c * chiV v c' := by
  refine PontryaginDual.ext fun x => ?_
  simp only [chiV_apply, add_mul, map_add, AddCircle.toCircle_add]
  rfl

theorem chiV_injective : Function.Injective (chiV v) := by
  intro c c' h
  by_contra hne
  have h0 : chiV v (c - c') = 1 := by
    rw [show c = (c - c') + c' by abel, chiV_add] at h
    exact mul_eq_right.mp h
  have hc : c - c' ≠ 0 := sub_ne_zero.mpr hne
  have := DFunLike.congr_fun h0 (Multiplicative.ofAdd
    ((c - c')⁻¹ * algebraMap ℚ (v.adicCompletion ℚ) ((primesEquiv v : ℕ) : ℚ)⁻¹))
  rw [chiV_apply, PontryaginDual.one_apply, toAdd_ofAdd, ← mul_assoc, mul_inv_cancel₀ hc,
    one_mul, toCircle_eq_one_iff] at this
  exact frV_inv_p_ne_zero v this

/-- Projection `ℚ̂ → ℚ_p`. -/
def projV : ContinuousMonoidHom (Multiplicative QHat) (Multiplicative (v.adicCompletion ℚ)) :=
  ⟨{ toFun := fun a => Multiplicative.ofAdd ((Multiplicative.toAdd a) v)
     map_one' := rfl
     map_mul' := fun _ _ => rfl },
    continuous_ofAdd.comp ((RestrictedProduct.continuous_eval v).comp continuous_toAdd)⟩

/-- **Every character of `ℚ_p` is `x ↦ e(fr_p(c x))`** (restrict the self-duality of `ℚ̂`). -/
theorem chiV_surjective : Function.Surjective (chiV v) := by
  intro χ
  obtain ⟨u, hu⟩ := chi_surjective (χ.comp (projV v))
  refine ⟨u v, PontryaginDual.ext fun x => ?_⟩
  have h := DFunLike.congr_fun hu (Multiplicative.ofAdd (singleAt v (Multiplicative.toAdd x)))
  rw [chi_apply, toAdd_ofAdd, mul_singleAt, psi_singleAt] at h
  rw [chiV_apply, h]
  show χ (Multiplicative.ofAdd ((singleAt v (Multiplicative.toAdd x)) v)) = χ x
  rw [singleAt_apply, Pi.single_eq_same]; rfl

/-- `ℚ_p ≅ ℚ_p^∨`, additively. -/
def chiVEquiv : v.adicCompletion ℚ ≃+ Additive (PontryaginDual (Multiplicative (v.adicCompletion ℚ))) where
  toFun c := Additive.ofMul (chiV v c)
  invFun χ := (Equiv.ofBijective (chiV v) ⟨chiV_injective v, chiV_surjective v⟩).symm
    (Additive.toMul χ)
  left_inv c := (Equiv.ofBijective (chiV v) ⟨chiV_injective v, chiV_surjective v⟩).symm_apply_apply c
  right_inv χ := by
    show Additive.ofMul ((Equiv.ofBijective (chiV v) ⟨chiV_injective v, chiV_surjective v⟩)
      ((Equiv.ofBijective (chiV v) _).symm _)) = χ
    rw [Equiv.apply_symm_apply]; rfl
  map_add' c c' := by
    show Additive.ofMul (chiV v (c + c')) = Additive.ofMul (chiV v c * chiV v c')
    rw [chiV_add]

theorem chiV_symm (χ : PontryaginDual (Multiplicative (v.adicCompletion ℚ))) :
    chiV v ((chiVEquiv v).symm (Additive.ofMul χ)) = χ :=
  congrArg Additive.toMul ((chiVEquiv v).apply_symm_apply (Additive.ofMul χ))

theorem symm_chiV (c : v.adicCompletion ℚ) : (chiVEquiv v).symm (Additive.ofMul (chiV v c)) = c :=
  (chiVEquiv v).symm_apply_apply c

/-! ### `Hom(ℚ_p, A^∨) ≅ ℚ_pⁿ` -/

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] {n : ℕ}

/-- `x ↦ f(x)(a)`. -/
def charOfV (f : HomV v (PontryaginDual (Multiplicative A))) (a : A) :
    PontryaginDual (Multiplicative (v.adicCompletion ℚ)) :=
  ⟨{ toFun := fun x => f x (Multiplicative.ofAdd a)
     map_one' := by rw [map_one]; rfl
     map_mul' := fun x y => by rw [map_mul]; rfl },
    (continuous_eval_const (F := PontryaginDual (Multiplicative A))
      (Multiplicative.ofAdd a)).comp f.continuous⟩

/-- `a ↦ c_a ∈ ℚ_p`. -/
def charHomV (f : HomV v (PontryaginDual (Multiplicative A))) : A →+ v.adicCompletion ℚ :=
  (chiVEquiv v).symm.toAddMonoidHom.comp
    { toFun := fun a => Additive.ofMul (charOfV v f a)
      map_zero' := by
        show Additive.ofMul (charOfV v f 0) = Additive.ofMul 1
        congr 1; refine PontryaginDual.ext fun x => ?_; show f x 1 = 1; rw [map_one]
      map_add' := fun a b => by
        show Additive.ofMul (charOfV v f (a + b)) = Additive.ofMul (charOfV v f a * charOfV v f b)
        congr 1; refine PontryaginDual.ext fun x => ?_
        show f x (Multiplicative.ofAdd a * Multiplicative.ofAdd b) = _
        rw [map_mul]; rfl }

omit [DiscreteTopology A] in
theorem chiV_charHomV (f : HomV v (PontryaginDual (Multiplicative A))) (a : A) :
    chiV v (charHomV v f a) = charOfV v f a :=
  chiV_symm v _

variable (ι : A →+ (Fin n → ℚ))

/-- `w_u(a) = ∑_j ι(a)_j u_j ∈ ℚ_p`. -/
def wvecV (u : Fin n → v.adicCompletion ℚ) : A →+ v.adicCompletion ℚ where
  toFun a := ∑ j, algebraMap ℚ (v.adicCompletion ℚ) (ι a j) * u j
  map_zero' := by simp
  map_add' a b := by
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `fuV u (x)(a) = e(fr_p(x w_u(a)))`. -/
def fuV (u : Fin n → v.adicCompletion ℚ) : HomV v (PontryaginDual (Multiplicative A)) :=
  ⟨{ toFun := fun x =>
        ⟨{ toFun := fun a => chiV v (wvecV v ι u (Multiplicative.toAdd a)) x
           map_one' := by
             rw [toAdd_one, map_zero, show chiV v 0 = 1 from
               PontryaginDual.ext fun y => by simp [chiV_apply]]; rfl
           map_mul' := fun a b => by
             rw [toAdd_mul, map_add, chiV_add]; rfl },
          continuous_of_discreteTopology⟩
     map_one' := PontryaginDual.ext fun a => by
       show chiV v _ 1 = 1; rw [map_one]
     map_mul' := fun x y => PontryaginDual.ext fun a => by
       show chiV v _ (x * y) = chiV v _ x * chiV v _ y; rw [map_mul] },
    by
      apply ContinuousMonoidHom.continuous_of_continuous_uncurry
      change Continuous fun p : Multiplicative (v.adicCompletion ℚ) × Multiplicative A =>
        chiV v (wvecV v ι u (Multiplicative.toAdd p.2)) p.1
      rw [continuous_prod_of_discrete_right]
      intro a
      exact (chiV v (wvecV v ι u (Multiplicative.toAdd a))).continuous⟩

variable {ι} {d : Fin n → A} (hd : ∀ j, ι (d j) = Pi.single j 1)

include hd in
omit [TopologicalSpace A] [DiscreteTopology A] in
theorem wvecV_d (u : Fin n → v.adicCompletion ℚ) (j : Fin n) : wvecV v ι u (d j) = u j := by
  simp only [wvecV, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hd, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (Finset.mem_univ j) h

variable (d) in
/-- `θ_p(f)_j = c_{d_j}`. -/
def thetaV (f : HomV v (PontryaginDual (Multiplicative A))) : Fin n → v.adicCompletion ℚ :=
  fun j => charHomV v f (d j)

include hd in
omit [DiscreteTopology A] in
theorem charHomV_eq (hι : Function.Injective ι) (f : HomV v (PontryaginDual (Multiplicative A))) :
    charHomV v f = wvecV v ι (thetaV v d f) := by
  set g := charHomV v f - wvecV v ι (thetaV v d f)
  have hF : ∀ a ∈ Flat ι, g a = 0 := by
    intro a ha
    choose k hk using ha
    rw [eq_sum_of_int hd hι hk, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_zsmul]
    simp [g, thetaV, wvecV_d v hd]
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨m, hm, hma⟩ := torsion_Flat ι a
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hma
  have h0 : m • g a = 0 := by rw [← map_nsmul]; exact hF _ hma
  rw [nsmul_eq_mul] at h0
  have hm0 : (m : v.adicCompletion ℚ) ≠ 0 := by
    rw [show (m : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) (m : ℚ) by simp]
    exact (map_ne_zero _).mpr (by exact_mod_cast hm.ne')
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hm0)

include hd in
theorem fuV_thetaV (hι : Function.Injective ι) (f : HomV v (PontryaginDual (Multiplicative A))) :
    fuV v ι (thetaV v d f) = f := by
  refine ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun a => ?_
  show chiV v (wvecV v ι (thetaV v d f) (Multiplicative.toAdd a)) x = f x a
  rw [← charHomV_eq v hd hι, chiV_charHomV]; rfl

include hd in
theorem thetaV_fuV (u : Fin n → v.adicCompletion ℚ) : thetaV v d (fuV v ι u) = u := by
  funext j
  show (chiVEquiv v).symm (Additive.ofMul (charOfV v (fuV v ι u) (d j))) = u j
  have : charOfV v (fuV v ι u) (d j) = chiV v (u j) := by
    refine PontryaginDual.ext fun x => ?_
    show chiV v (wvecV v ι u (d j)) x = _
    rw [wvecV_d v hd]
  rw [this, symm_chiV]

omit [DiscreteTopology A] in
theorem thetaV_mul (f g : HomV v (PontryaginDual (Multiplicative A))) :
    thetaV v d (f * g) = thetaV v d f + thetaV v d g := by
  funext j
  show (chiVEquiv v).symm (Additive.ofMul (charOfV v (f * g) (d j))) =
    (chiVEquiv v).symm (Additive.ofMul (charOfV v f (d j))) +
      (chiVEquiv v).symm (Additive.ofMul (charOfV v g (d j)))
  rw [← map_add]
  congr 1

omit [DiscreteTopology A] in
theorem thetaV_smul (r : v.adicCompletion ℚ) (f : HomV v (PontryaginDual (Multiplicative A))) :
    thetaV v d (Additive.toMul (r • Additive.ofMul f)) = r • thetaV v d f := by
  funext j
  show charHomV v _ (d j) = r * charHomV v f (d j)
  apply chiV_injective v
  rw [chiV_charHomV]
  refine PontryaginDual.ext fun x => ?_
  show (Additive.toMul (r • Additive.ofMul f)) x (Multiplicative.ofAdd (d j)) = _
  rw [smulHomV_apply]
  have h := DFunLike.congr_fun (chiV_charHomV v f (d j))
    (Multiplicative.ofAdd (r * Multiplicative.toAdd x))
  rw [chiV_apply, toAdd_ofAdd] at h
  refine Eq.trans h.symm ?_
  rw [chiV_apply]
  congr 2; ring

include hd in
/-- **`Hom(ℚ_p, A^∨) ≅ ℚ_pⁿ`** as `ℚ_p`-vector spaces. -/
def thetaVEquiv (hι : Function.Injective ι) :
    Additive (HomV v (PontryaginDual (Multiplicative A))) ≃ₗ[v.adicCompletion ℚ]
      (Fin n → v.adicCompletion ℚ) where
  toFun f := thetaV v d (Additive.toMul f)
  invFun u := Additive.ofMul (fuV v ι u)
  map_add' f g := thetaV_mul v (Additive.toMul f) (Additive.toMul g)
  map_smul' r f := thetaV_smul v r (Additive.toMul f)
  left_inv f := congrArg Additive.ofMul (fuV_thetaV v hd hι (Additive.toMul f))
  right_inv u := thetaV_fuV v hd u

include hd in
/-- **`d_p(A^∨) = n`.** -/
theorem dP_dual (hι : Function.Injective ι) : dP v (PontryaginDual (Multiplicative A)) = n := by
  unfold dP
  rw [(thetaVEquiv v hd hι).finrank_eq, Module.finrank_fin_fun]

end AdelicToriLean
