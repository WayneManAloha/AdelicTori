import AdelicToriLean.DeltaLattice
import AdelicToriLean.QHatSelfDual

/-!
# The adelic covering module `𝒱_n(G) = Hom(ℚ̂, G)`

`A` discrete, `ι : A → ℚⁿ` injective, `d_j ∈ A` with `ι(d_j) = e_j`, `G = A^∨`, `n = dim_a G`.
`𝒱_n(G)` (`Vn A`) is the group of continuous homomorphisms `ℚ̂ → G`; `ℚ̂` acts by precomposition,
`(r • f)(x) = f(r x)` (`smulV`).

* `theta`: `𝒱_n(G) → ℚ̂ⁿ`, `f ↦ (u_j)` with `f(x)(d_j) = e(ψ(u_j x))`;
* `fu`: `ℚ̂ⁿ → 𝒱_n(G)`, `fu u (x)(a) = e(ψ(x ∑_j ι(a)_j u_j))`, the inverse;
* `thetaLinearEquiv`: `𝒱_n(G) ≅ ℚ̂ⁿ` as `ℚ̂`-modules, so `𝒱_n(G)` is **free of rank `n`**
  (`rank_Vn`); the definition `dim_n Lie_n(G) := rank_ℚ̂ 𝒱_n(G)` gives `n` for every `G`.
-/

open Topology

noncomputable section

namespace AdelicToriLean

/-- `ℚ̂ ≅ ℚ̂^∨`, `u ↦ e(ψ(u ·))`, as additive groups. -/
def chiAddEquiv : QHat ≃+ Additive (PontryaginDual (Multiplicative QHat)) where
  toFun u := Additive.ofMul (chi u)
  invFun χ := (Equiv.ofBijective chi ⟨chi_injective, chi_surjective⟩).symm (Additive.toMul χ)
  left_inv u := (Equiv.ofBijective chi ⟨chi_injective, chi_surjective⟩).symm_apply_apply u
  right_inv χ := by
    show Additive.ofMul (chi ((Equiv.ofBijective chi _).symm _)) = χ
    rw [show chi ((Equiv.ofBijective chi ⟨chi_injective, chi_surjective⟩).symm (Additive.toMul χ))
      = (Equiv.ofBijective chi ⟨chi_injective, chi_surjective⟩)
        ((Equiv.ofBijective chi ⟨chi_injective, chi_surjective⟩).symm (Additive.toMul χ)) from rfl,
      Equiv.apply_symm_apply]; rfl
  map_add' u v := by
    show Additive.ofMul (chi (u + v)) = Additive.ofMul (chi u * chi v)
    rw [chi_add]

theorem chi_chiAddEquiv_symm (χ : PontryaginDual (Multiplicative QHat)) :
    chi (chiAddEquiv.symm (Additive.ofMul χ)) = χ :=
  congrArg Additive.toMul (chiAddEquiv.apply_symm_apply (Additive.ofMul χ))

theorem chiAddEquiv_symm_chi (u : QHat) : chiAddEquiv.symm (Additive.ofMul (chi u)) = u :=
  chiAddEquiv.symm_apply_apply u

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] {n : ℕ}

/-- **The adelic covering module** `𝒱_n(G) = Hom(ℚ̂, G)`, `G = A^∨`. -/
abbrev Vn := ContinuousMonoidHom (Multiplicative QHat) (PontryaginDual (Multiplicative A))

variable {A}

/-- Multiplication by `r` on `ℚ̂`. -/
def mulQ (r : QHat) : ContinuousMonoidHom (Multiplicative QHat) (Multiplicative QHat) :=
  ⟨{ toFun := fun x => Multiplicative.ofAdd (r * Multiplicative.toAdd x)
     map_one' := by simp
     map_mul' := fun x y => by simp [mul_add] },
    continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)⟩

/-- **`ℚ̂` acts on `𝒱_n(G)` by precomposition.** -/
instance smulV : SMul QHat (Additive (Vn A)) where
  smul r f := Additive.ofMul ((Additive.toMul f).comp (mulQ r))

omit [DiscreteTopology A] in
theorem smulV_apply (r : QHat) (f : Vn A) (x : Multiplicative QHat) :
    Additive.toMul (r • Additive.ofMul f) x =
      f (Multiplicative.ofAdd (r * Multiplicative.toAdd x)) := rfl

/-- The character `x ↦ f(x)(a)` of `ℚ̂`. -/
def charOf (f : Vn A) (a : A) : PontryaginDual (Multiplicative QHat) :=
  ⟨{ toFun := fun x => f x (Multiplicative.ofAdd a)
     map_one' := by rw [map_one]; rfl
     map_mul' := fun x y => by rw [map_mul]; rfl },
    (continuous_eval_const (F := PontryaginDual (Multiplicative A))
      (Multiplicative.ofAdd a)).comp f.continuous⟩

omit [DiscreteTopology A] in
theorem charOf_apply (f : Vn A) (a : A) (x : Multiplicative QHat) :
    charOf f a x = f x (Multiplicative.ofAdd a) := rfl

omit [DiscreteTopology A] in
theorem charOf_add (f : Vn A) (a b : A) : charOf f (a + b) = charOf f a * charOf f b := by
  refine PontryaginDual.ext fun x => ?_
  show f x (Multiplicative.ofAdd a * Multiplicative.ofAdd b) = _
  rw [map_mul]; rfl

/-- `a ↦ χ_a`, as a homomorphism to `ℚ̂`. -/
def charHom (f : Vn A) : A →+ QHat :=
  chiAddEquiv.symm.toAddMonoidHom.comp
    { toFun := fun a => Additive.ofMul (charOf f a)
      map_zero' := by
        show Additive.ofMul (charOf f 0) = Additive.ofMul 1
        congr 1; refine PontryaginDual.ext fun x => ?_; show f x 1 = 1; rw [map_one]
      map_add' := fun a b => by rw [charOf_add]; rfl }

omit [DiscreteTopology A] in
theorem chi_charHom (f : Vn A) (a : A) : chi (charHom f a) = charOf f a :=
  chi_chiAddEquiv_symm _

variable (ι : A →+ (Fin n → ℚ))

/-- `w_u(a) = ∑_j ι(a)_j u_j`. -/
def wvec (u : Fin n → QHat) : A →+ QHat where
  toFun a := ∑ j, algebraMap ℚ QHat (ι a j) * u j
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

/-- `fu u (x)(a) = e(ψ(x w_u(a)))`. -/
def fu (u : Fin n → QHat) : Vn A :=
  ⟨{ toFun := fun x =>
        ⟨{ toFun := fun a => chi (wvec ι u (Multiplicative.toAdd a)) x
           map_one' := by simp [chi_zero]
           map_mul' := fun a b => by
             rw [toAdd_mul, map_add, chi_add]; rfl },
          continuous_of_discreteTopology⟩
     map_one' := PontryaginDual.ext fun a => by
       show chi _ 1 = 1; rw [map_one]
     map_mul' := fun x y => PontryaginDual.ext fun a => by
       show chi _ (x * y) = chi _ x * chi _ y; rw [map_mul] },
    by
      apply ContinuousMonoidHom.continuous_of_continuous_uncurry
      change Continuous fun p : Multiplicative QHat × Multiplicative A =>
        chi (wvec ι u (Multiplicative.toAdd p.2)) p.1
      rw [continuous_prod_of_discrete_right]
      intro a
      exact (chi (wvec ι u (Multiplicative.toAdd a))).continuous⟩

theorem fu_apply (u : Fin n → QHat) (x : Multiplicative QHat) (a : A) :
    fu ι u x (Multiplicative.ofAdd a) = chi (wvec ι u a) x := rfl

variable {ι} {d : Fin n → A} (hd : ∀ j, ι (d j) = Pi.single j 1)

omit [TopologicalSpace A] [DiscreteTopology A] in
include hd in
theorem wvec_d (u : Fin n → QHat) (j : Fin n) : wvec ι u (d j) = u j := by
  simp only [wvec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hd, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (Finset.mem_univ j) h

variable (d) in
/-- **`θ : 𝒱_n(G) → ℚ̂ⁿ`**, `θ(f)_j = χ_{d_j}`. -/
def theta (f : Vn A) : Fin n → QHat := fun j => charHom f (d j)

/-- `ℚ̂` is torsion-free. -/
theorem qhat_nsmul_eq_zero {m : ℕ} (hm : 0 < m) {x : QHat} (h : m • x = 0) : x = 0 := by
  rw [nsmul_eq_mul] at h
  have hu : IsUnit (m : QHat) := by
    rw [show (m : QHat) = algebraMap ℚ QHat (m : ℚ) by simp]
    exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hm.ne' : (m : ℚ) ≠ 0)).map _
  exact hu.mul_right_eq_zero.mp h

omit [DiscreteTopology A] in
include hd in
/-- `χ_a = e(ψ(w_{θ f}(a) ·))` for every `a`: the two homomorphisms `A → ℚ̂` agree on the `d_j`,
hence on `F`, hence everywhere (`A/F` torsion, `ℚ̂` torsion-free). -/
theorem charHom_eq (hι : Function.Injective ι) (f : Vn A) : charHom f = wvec ι (theta d f) := by
  set g := charHom f - wvec ι (theta d f)
  have hF : ∀ a ∈ Flat ι, g a = 0 := by
    intro a ha
    choose k hk using ha
    rw [eq_sum_of_int hd hι hk, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_zsmul]
    simp [g, theta, wvec_d hd]
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨m, hm, hma⟩ := torsion_Flat ι a
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hma
  have h0 : m • g a = 0 := by rw [← map_nsmul]; exact hF _ hma
  exact sub_eq_zero.mp (qhat_nsmul_eq_zero hm h0)

include hd in
theorem fu_theta (hι : Function.Injective ι) (f : Vn A) : fu ι (theta d f) = f := by
  refine ContinuousMonoidHom.ext fun x => PontryaginDual.ext fun a => ?_
  show chi (wvec ι (theta d f) (Multiplicative.toAdd a)) x = f x a
  rw [← charHom_eq hd hι, chi_charHom]; rfl

include hd in
theorem theta_fu (u : Fin n → QHat) : theta d (fu ι u) = u := by
  funext j
  show chiAddEquiv.symm (Additive.ofMul (charOf (fu ι u) (d j))) = u j
  have : charOf (fu ι u) (d j) = chi (u j) := by
    refine PontryaginDual.ext fun x => ?_
    show chi (wvec ι u (d j)) x = _
    rw [wvec_d hd]
  rw [this, chiAddEquiv_symm_chi]

omit [DiscreteTopology A] in
theorem theta_mul (f g : Vn A) : theta d (f * g) = theta d f + theta d g := by
  funext j
  show chiAddEquiv.symm (Additive.ofMul (charOf (f * g) (d j))) =
    chiAddEquiv.symm (Additive.ofMul (charOf f (d j))) +
      chiAddEquiv.symm (Additive.ofMul (charOf g (d j)))
  rw [← map_add]
  congr 1

omit [DiscreteTopology A] in
theorem theta_smul (r : QHat) (f : Vn A) :
    theta d (Additive.toMul (r • Additive.ofMul f)) = r • theta d f := by
  funext j
  show charHom _ (d j) = r * charHom f (d j)
  apply chi_injective
  rw [chi_charHom]
  refine PontryaginDual.ext fun x => ?_
  rw [charOf_apply, smulV_apply, ← charOf_apply, ← chi_charHom, chi_apply, chi_apply,
    toAdd_ofAdd]
  congr 2; ring

/-- `θ` as an additive map on `Additive 𝒱_n(G)`. -/
def thetaAdd : Additive (Vn A) →+ (Fin n → QHat) where
  toFun f := theta d (Additive.toMul f)
  map_zero' := by
    have := theta_mul (d := d) (1 : Vn A) 1
    rw [mul_one] at this
    show theta d 1 = 0
    have h := congrArg (fun v => v - theta d (1 : Vn A)) this
    simpa using h.symm
  map_add' f g := theta_mul (Additive.toMul f) (Additive.toMul g)

include hd in
theorem thetaAdd_injective (hι : Function.Injective ι) :
    Function.Injective (thetaAdd (A := A) (d := d)) := by
  intro f g h
  have h' : theta d (Additive.toMul f) = theta d (Additive.toMul g) := h
  apply Additive.toMul.injective
  rw [← fu_theta hd hι (Additive.toMul f), ← fu_theta hd hι (Additive.toMul g), h']

/-- **`𝒱_n(G)` is a `ℚ̂`-module** (the action by precomposition). -/
abbrev moduleV (hι : Function.Injective ι) : Module QHat (Additive (Vn A)) :=
  Function.Injective.module QHat (thetaAdd (A := A) (d := d))
    (thetaAdd_injective hd hι) (fun r f => theta_smul r (Additive.toMul f))

/-- **`𝒱_n(G) ≅ ℚ̂ⁿ` as `ℚ̂`-modules.** -/
def thetaLinearEquiv (hι : Function.Injective ι) :
    letI := moduleV hd hι
    Additive (Vn A) ≃ₗ[QHat] (Fin n → QHat) :=
  letI := moduleV hd hι
  { thetaAdd (A := A) (d := d) with
    invFun := fun u => Additive.ofMul (fu ι u)
    left_inv := fun f => congrArg Additive.ofMul (fu_theta hd hι (Additive.toMul f))
    right_inv := fun u => theta_fu hd u
    map_smul' := fun r f => theta_smul r (Additive.toMul f) }

/-- **`𝒱_n(G)` is free of rank `n = dim_a G`.** -/
theorem rank_Vn (hι : Function.Injective ι) :
    letI := moduleV hd hι
    Module.Free QHat (Additive (Vn A)) ∧ Module.finrank QHat (Additive (Vn A)) = n := by
  let _ := moduleV hd hι
  have e := thetaLinearEquiv hd hι
  exact ⟨Module.Free.of_equiv e.symm, by rw [e.finrank_eq, Module.finrank_fin_fun]⟩

end AdelicToriLean
