import AdelicToriLean.LocalCover
import AdelicToriLean.ArlaReal

/-!
# `dim_n Lie_n(G) = n = dim_a G`

`d_p(L) = dim_{ℚ_p} Hom(ℚ_p, L)` and `dim_n L = sup_p d_p(L)` (`LocalCover.lean`).

* `homNalaEquiv`: `Hom(ℚ_p, Lie_n G) ≅ Hom(ℚ_p, G)` as `ℚ_p`-vector spaces, for every topological
  abelian Hausdorff `G`: `F ↦ (x ↦ F(x)(1))`, inverse `f ↦ (x ↦ (z ↦ f(z_p x)))` (`ℚ_p` is a
  `ℤ̂`-module through `ℤ̂ → ℤ_p`);
* `dP_congr`: `d_p` is invariant under topological isomorphism;
* **`dimNL_nala`: for every finite-dimensional protorus `G`, `d_p(Lie_n G) = dim_a G` for every
  `p`, so `dim_n Lie_n(G) = dim_a G`**; no torus-free hypothesis;
* `dimNL_nala_torus`: the case `G = (ℤⁿ)^∨ = 𝕋ⁿ`, `Lie_n(G) ≅ (ℚ/ℤ)ⁿ`: `dim_n = n`;
* `symmetric_adelic_lie_algebra_dim`: Theorem `symmetric-adelic-lie-algebra` with the dimension
  clause `dim_n Lie_n(G) = n = dim_a Lie_a(G)`.
-/

open Topology IsDedekindDomain TensorProduct

noncomputable section

namespace AdelicToriLean

variable (v : HeightOneSpectrum ℤ)

/-- `z ↦ z_p`, `ℤ̂ → ℚ_p`. -/
def zv (z : ZHat) : v.adicCompletion ℚ := (z : QHat) v

theorem continuous_zv : Continuous (zv v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_subtype_val

theorem zv_oneZ : zv v oneZ = 1 := rfl

theorem zv_add (z z' : ZHat) : zv v (z + z') = zv v z + zv v z' := rfl

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- `f ↦ (x ↦ (z ↦ f(z_p x)))`. -/
def liftNala (f : HomV v G) : HomV v (nala G) :=
  ⟨{ toFun := fun x =>
        ⟨{ toFun := fun z =>
              f (Multiplicative.ofAdd (zv v (Multiplicative.toAdd z) * Multiplicative.toAdd x))
           map_one' := by
             rw [show zv v (Multiplicative.toAdd (1 : Multiplicative ZHat)) = 0 from rfl, zero_mul]
             exact map_one f
           map_mul' := fun z z' => by
             rw [← map_mul]; congr 1
             show Multiplicative.ofAdd (zv v (Multiplicative.toAdd z + Multiplicative.toAdd z') *
               Multiplicative.toAdd x) = _
             rw [zv_add, add_mul]; rfl },
          f.continuous.comp (continuous_ofAdd.comp
            (((continuous_zv v).comp continuous_toAdd).mul continuous_const))⟩
     map_one' := by
       refine ContinuousMonoidHom.ext fun z => ?_
       show f (Multiplicative.ofAdd (zv v _ * 0)) = 1
       rw [mul_zero]; exact map_one f
     map_mul' := fun x y => by
       refine ContinuousMonoidHom.ext fun z => ?_
       show f (Multiplicative.ofAdd (zv v (Multiplicative.toAdd z) *
         (Multiplicative.toAdd x + Multiplicative.toAdd y))) = _
       rw [mul_add, ofAdd_add, map_mul]; rfl },
    by
      apply ContinuousMonoidHom.continuous_of_continuous_uncurry
      change Continuous fun p : Multiplicative (v.adicCompletion ℚ) × Multiplicative ZHat =>
        f (Multiplicative.ofAdd (zv v (Multiplicative.toAdd p.2) * Multiplicative.toAdd p.1))
      exact f.continuous.comp (continuous_ofAdd.comp
        (((continuous_zv v).comp (continuous_toAdd.comp continuous_snd)).mul
          (continuous_toAdd.comp continuous_fst)))⟩

/-- `F ↦ exp_n ∘ F`. -/
def expNala (F : HomV v (nala G)) : HomV v G :=
  ⟨(expn G).comp F.toMonoidHom, (continuous_expn G).comp F.continuous⟩

omit [T2Space G] in
theorem expNala_liftNala (f : HomV v G) : expNala v G (liftNala v G f) = f := by
  refine ContinuousMonoidHom.ext fun x => ?_
  show f (Multiplicative.ofAdd (zv v oneZ * Multiplicative.toAdd x)) = f x
  rw [zv_oneZ, one_mul]; rfl

theorem liftNala_expNala (F : HomV v (nala G)) : liftNala v G (expNala v G F) = F := by
  refine ContinuousMonoidHom.ext fun x => zhatHom_ext ?_
  show F (Multiplicative.ofAdd (zv v oneZ * Multiplicative.toAdd x)) genZ = F x genZ
  rw [zv_oneZ, one_mul]; rfl

/-- **`Hom(ℚ_p, Lie_n G) ≅ Hom(ℚ_p, G)`** as `ℚ_p`-vector spaces. -/
def homNalaEquiv :
    Additive (HomV v (nala G)) ≃ₗ[v.adicCompletion ℚ] Additive (HomV v G) where
  toFun F := Additive.ofMul (expNala v G (Additive.toMul F))
  invFun f := Additive.ofMul (liftNala v G (Additive.toMul f))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := congrArg Additive.ofMul (liftNala_expNala v G (Additive.toMul F))
  right_inv f := congrArg Additive.ofMul (expNala_liftNala v G (Additive.toMul f))

theorem dP_nala : dP v (nala G) = dP v G :=
  (homNalaEquiv v G).finrank_eq

/-- **`d_p` is invariant under topological isomorphism.** -/
theorem dP_congr {L L' : Type*} [CommGroup L] [TopologicalSpace L] [IsTopologicalGroup L]
    [CommGroup L'] [TopologicalSpace L'] [IsTopologicalGroup L'] (e : L ≃ₜ* L') :
    dP v L = dP v L' := by
  let φ : ContinuousMonoidHom L L' := ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩
  let ψ : ContinuousMonoidHom L' L := ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩
  let E : Additive (HomV v L) ≃ₗ[v.adicCompletion ℚ] Additive (HomV v L') :=
    { toFun := fun f => Additive.ofMul (φ.comp (Additive.toMul f))
      invFun := fun f => Additive.ofMul (ψ.comp (Additive.toMul f))
      map_add' := fun f g => by
        apply Additive.toMul.injective
        refine ContinuousMonoidHom.ext fun x => ?_
        show e (Additive.toMul f x * Additive.toMul g x) = e (Additive.toMul f x) * e (Additive.toMul g x)
        exact map_mul e _ _
      map_smul' := fun _ _ => rfl
      left_inv := fun f => by
        apply Additive.toMul.injective
        refine ContinuousMonoidHom.ext fun x => ?_
        exact e.symm_apply_apply _
      right_inv := fun f => by
        apply Additive.toMul.injective
        refine ContinuousMonoidHom.ext fun x => ?_
        exact e.apply_symm_apply _ }
  exact E.finrank_eq

instance : Nonempty (HeightOneSpectrum ℤ) := ⟨Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩⟩

/-- **`dim_n Lie_n(G) = dim_a G`** for every finite-dimensional protorus `G`: `d_p(Lie_n G) = n`
at every prime. -/
theorem dimNL_nala [CompactSpace G] [ConnectedSpace G] [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    (∀ v : HeightOneSpectrum ℤ, dP v (nala G) = dimA G) ∧ dimNL (nala G) = dimA G := by
  have : DiscreteTopology (PontryaginDual G) := discreteTopology_dual
  obtain ⟨ι, hι, hZ⟩ := exists_rank_embedding (dual_additive_torsionFree G)
  choose d hd using hZ
  have hp : ∀ v : HeightOneSpectrum ℤ, dP v (nala G) = dimA G := fun v => by
    rw [dP_nala, dP_congr v (PontryaginDual.toDoubleDual G)]
    exact dP_dual v (A := Additive (PontryaginDual G)) hd hι
  refine ⟨hp, ?_⟩
  unfold dimNL
  simp only [hp, ciSup_const]

/-- **The torus case**: `Lie_n((ℤⁿ)^∨) ≅ (ℚ/ℤ)ⁿ` has `d_p = n` at every `p`, so
`dim_n = n`. -/
theorem dimNL_nala_torus (n : ℕ) :
    (∀ v : HeightOneSpectrum ℤ,
      dP v (nala (PontryaginDual (Multiplicative (Fin n → ℤ)))) = n) ∧
      dimNL (nala (PontryaginDual (Multiplicative (Fin n → ℤ)))) = n := by
  let ι : (Fin n → ℤ) →+ (Fin n → ℚ) :=
    { toFun := fun a j => (a j : ℚ)
      map_zero' := by funext; simp
      map_add' := fun a b => by funext; simp }
  have hι : Function.Injective ι := fun a b h => funext fun j => by
    have := congrFun h j
    simp only [ι, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    exact_mod_cast this
  have hd : ∀ j, ι (Pi.single j 1) = Pi.single j 1 := fun j => by
    funext i; simp only [ι, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.single_apply]
    split_ifs <;> simp
  have hp : ∀ v : HeightOneSpectrum ℤ,
      dP v (nala (PontryaginDual (Multiplicative (Fin n → ℤ)))) = n := fun v => by
    rw [dP_nala]; exact dP_dual v hd hι
  refine ⟨hp, ?_⟩
  unfold dimNL
  simp only [hp, ciSup_const]

/-- **Theorem `symmetric-adelic-lie-algebra`, with the dimension clause**: for a finite-dimensional
protorus `G`, `adla(G) ≅ nala(G) × arla(G)`, `nala(G)` is a divisible periodic LCA group,
`arla(G) ≅ ℝⁿ`, the adelic exponential splits, and `dim_n Lie_n(G) = n = dim_a Lie_a(G)`, where
`dim_n Lie_n(G) = sup_p dim_{ℚ_p} Hom(ℚ_p, Lie_n G)` and `n = dim_a G`. -/
theorem symmetric_adelic_lie_algebra_dim [CompactSpace G] [ConnectedSpace G]
    [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    Nonempty (adla G ≃ₜ* nala G × arla G) ∧
      (T2Space (nala G) ∧ LocallyCompactSpace (nala G) ∧
        ∀ f : nala G, ∃ K : Subgroup (nala G), IsOpen (K : Set (nala G)) ∧
          IsCompact (K : Set (nala G)) ∧ f ∈ K) ∧
      (∀ (f : nala G) (m : ℕ), 0 < m → ∃ g : nala G, g ^ m = f) ∧
      Nonempty (arla G ≃ₜ* Multiplicative (Fin (dimA G) → ℝ)) ∧
      (∀ f : adla G, expAd G f = expn G (adlaEquiv G f).1 * expa G (adlaEquiv G f).2) ∧
      dimNL (nala G) = dimA G :=
  ⟨(symmetric_adelic_lie_algebra_fd G).1, (symmetric_adelic_lie_algebra_fd G).2.1,
    (symmetric_adelic_lie_algebra_fd G).2.2.1, (symmetric_adelic_lie_algebra_fd G).2.2.2.1,
    (symmetric_adelic_lie_algebra_fd G).2.2.2.2, (dimNL_nala G).2⟩

end AdelicToriLean
