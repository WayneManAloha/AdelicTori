import AdelicToriLean.Kumu
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# `a(G)`: the path component of `0`

For a compact abelian group `G` with discrete dual of finite rank, the image of the archimedean
exponential `exp_a : Hom(ℝ, G) → G`, `f ↦ f(1)`, is exactly the path component of the identity
(Hofmann–Morris, *The Structure of Compact Groups*, Theorem 8.30): `range_expa_eq_pathComponent`.

Proof of `⊇`: for a path `γ` from `1` to `g`, lift each `χ ∘ γ` through `exp : ℝ → 𝕋` starting
at `0`; uniqueness of lifts makes `χ ↦ lift(1)` additive, hence of the form `χ ↦ ⟨ι χ, θ⟩`, and
`exp_a(v_θ) = g` because characters separate points.

Also: `a(G)` is divisible and fully invariant, dense (`dense_range_expa`), and for torus-free
`G` of positive dimension `exp_a` is injective, continuous and not open.
-/

open Topology Real unitInterval

noncomputable section

namespace AdelicToriLean

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Images of one-parameter subgroups lie in the path component of `1`. -/
theorem range_expa_subset : Set.range (expa G) ⊆ pathComponent (1 : G) := by
  rintro _ ⟨f, rfl⟩
  refine ⟨⟨⟨fun t : I => f (Multiplicative.ofAdd (t : ℝ)),
    f.continuous.comp (continuous_ofAdd.comp continuous_subtype_val)⟩, ?_, ?_⟩⟩
  · show f (Multiplicative.ofAdd 0) = 1
    exact map_one f
  · show f (Multiplicative.ofAdd 1) = expa G f
    rfl

/-- **`a(G)` is fully invariant.** -/
theorem map_arcSub_le {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : ContinuousMonoidHom G H) : (arcSub G).map (φ : G →* H) ≤ arcSub H := by
  rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
  exact ⟨φ.comp f, rfl⟩

/-- Multiplication by `c` on `ℝ`. -/
def scaleR (c : ℝ) : ContinuousMonoidHom (Multiplicative ℝ) (Multiplicative ℝ) :=
  ⟨{ toFun := fun t => Multiplicative.ofAdd (c * Multiplicative.toAdd t)
     map_one' := by simp
     map_mul' := fun s t => by simp [mul_add] },
    continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)⟩

/-- **`a(G)` is divisible.** -/
theorem arcSub_divisible {g : G} (hg : g ∈ arcSub G) {k : ℕ} (hk : 0 < k) :
    ∃ h ∈ arcSub G, h ^ k = g := by
  obtain ⟨f, rfl⟩ := hg
  refine ⟨expa G (f.comp (scaleR (1 / k))), ⟨_, rfl⟩, ?_⟩
  show f (Multiplicative.ofAdd (1 / k * 1)) ^ k = f (Multiplicative.ofAdd 1)
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul]
  congr 2
  field_simp

section Lift

variable [CompactSpace G] [T2Space G]

/-- The lift of `χ ∘ γ` through `exp : ℝ → 𝕋`, starting at `0`. -/
def liftChar (γ : C(I, G)) (hγ : γ 0 = 1) (χ : PontryaginDual G) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath ((χ : C(G, Circle)).comp γ) 0
    (by show χ (γ 0) = Circle.exp 0; rw [hγ, map_one, Circle.exp_zero])

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem liftChar_spec (γ : C(I, G)) (hγ : γ 0 = 1) (χ : PontryaginDual G) (t : I) :
    Circle.exp (liftChar γ hγ χ t) = χ (γ t) :=
  congrFun (Circle.isCoveringMap_exp.liftPath_lifts _ _ _) t

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem liftChar_zero (γ : C(I, G)) (hγ : γ 0 = 1) (χ : PontryaginDual G) :
    liftChar γ hγ χ 0 = 0 :=
  Circle.isCoveringMap_exp.liftPath_zero _ _ _

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem liftChar_mul (γ : C(I, G)) (hγ : γ 0 = 1) (χ ψ : PontryaginDual G) :
    liftChar γ hγ (χ * ψ) = liftChar γ hγ χ + liftChar γ hγ ψ := by
  symm
  show _ = Circle.isCoveringMap_exp.liftPath _ _ _
  rw [Circle.isCoveringMap_exp.eq_liftPath_iff']
  refine ⟨funext fun t => ?_, ?_⟩
  · show Circle.exp (liftChar γ hγ χ t + liftChar γ hγ ψ t) = (χ * ψ) (γ t)
    rw [Circle.exp_add, liftChar_spec, liftChar_spec]; rfl
  · show liftChar γ hγ χ 0 + liftChar γ hγ ψ 0 = 0
    rw [liftChar_zero, liftChar_zero, add_zero]

/-- `χ ↦ lift(χ ∘ γ)(1)`, an additive map `G^∨ → ℝ`. -/
def liftHom (γ : C(I, G)) (hγ : γ 0 = 1) : Additive (PontryaginDual G) →+ ℝ where
  toFun χ := liftChar γ hγ (Additive.toMul χ) 1
  map_zero' := by
    have h := liftChar_mul γ hγ 1 1
    rw [mul_one] at h
    have := congrArg (fun F : C(I, ℝ) => F 1) h
    simp only [ContinuousMap.add_apply] at this
    show liftChar γ hγ 1 1 = 0
    linarith
  map_add' χ ψ := by
    show liftChar γ hγ (Additive.toMul χ * Additive.toMul ψ) 1 = _
    rw [liftChar_mul]; rfl

variable [DiscreteTopology (PontryaginDual G)] {n : ℕ}
  {ι : Additive (PontryaginDual G) →+ (Fin n → ℚ)} (hι : Function.Injective ι)
  {d : Fin n → Additive (PontryaginDual G)} (hd : ∀ j, ι (d j) = Pi.single j 1)

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [DiscreteTopology (PontryaginDual G)] in
include hι hd in
/-- Every additive `φ : G^∨ → ℝ` is `χ ↦ ⟨ι χ, θ⟩` for some `θ ∈ ℝⁿ`. -/
theorem exists_theta (φ : Additive (PontryaginDual G) →+ ℝ) :
    ∃ θ : Fin n → ℝ, ∀ χ : PontryaginDual G, φ (Additive.ofMul χ) = coef ι θ χ := by
  refine ⟨fun j => φ (d j), fun χ => ?_⟩
  set a := Additive.ofMul χ
  obtain ⟨m, hm, k, hk⟩ := exists_int_multiple (ι a)
  have hsum : m • a = ∑ j, k j • d j := hι (by
    funext i
    simp only [map_nsmul, map_sum, map_zsmul, hd, Pi.smul_apply, Finset.sum_apply,
      Pi.single_apply, nsmul_eq_mul]
    rw [hk i]; simp)
  have h1 := congrArg φ hsum
  simp only [map_nsmul, map_sum, map_zsmul, nsmul_eq_mul, zsmul_eq_mul] at h1
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  apply mul_left_cancel₀ hm'
  rw [h1, coef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrArg (fun q : ℚ => (q : ℝ)) (hk j)
  push_cast at this
  rw [← mul_assoc, this]

include hι hd in
/-- **`exp_a(Hom(ℝ, G))` is the path component of `1`** (Hofmann–Morris, Theorem 8.30). -/
theorem pathComponent_subset_range : pathComponent (1 : G) ⊆ Set.range (expa G) := by
  intro g hg
  obtain ⟨γ⟩ := hg
  obtain ⟨θ, hθ⟩ := exists_theta hι hd (liftHom γ.toContinuousMap γ.source)
  refine ⟨vθ ι θ, ?_⟩
  apply (PontryaginDual.toDoubleDual G).injective
  refine ContinuousMonoidHom.ext fun χ => ?_
  show PontryaginDual.toDoubleDual G (vθ ι θ (Multiplicative.ofAdd 1)) χ = χ g
  rw [toDoubleDual_vθ, phi_apply, toAdd_ofAdd, one_mul, ← hθ χ]
  show Circle.exp (liftChar γ.toContinuousMap γ.source χ 1) = χ g
  rw [liftChar_spec]
  exact congrArg χ γ.target

include hι hd in
theorem range_expa_eq_pathComponent : Set.range (expa G) = pathComponent (1 : G) :=
  le_antisymm range_expa_subset (pathComponent_subset_range hι hd)

include hι hd in
/-- **`exp_a` is not open** for a torus-free `G` of positive dimension. -/
theorem not_isOpenMap_expa (hT : TorusFree G) (hn : 0 < n) : ¬ IsOpenMap (expa G) := by
  intro hopen
  have hinj : Function.Injective (expa G) := by
    intro f f' h
    have e1 := (arlaEquiv hd hι).symm_apply_apply f
    have e2 := (arlaEquiv hd hι).symm_apply_apply f'
    rw [← e1, ← e2]
    congr 1
    apply Multiplicative.toAdd.injective
    apply expa_vθ_injective hd hT
    show expa G ((arlaEquiv hd hι).symm _) = expa G ((arlaEquiv hd hι).symm _)
    rw [e1, e2, h]
  have hU : IsOpen ((expa G).range : Set G) := by
    rw [MonoidHom.coe_range]; exact hopen.isOpen_range
  have hsurj : Function.Surjective (expa G) := by
    have hcl := Subgroup.isClosed_of_isOpen _ hU
    have hd' : Dense (Set.range (expa G)) := dense_range_expa_of hι
    have huniv : ((expa G).range : Set G) = Set.univ := by
      rw [← hcl.closure_eq, MonoidHom.coe_range, hd'.closure_eq]
    intro g
    have : g ∈ ((expa G).range : Set G) := huniv ▸ Set.mem_univ g
    exact this
  have hcont : Continuous (expa G) := continuous_expa G
  let h := (Equiv.ofBijective _ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen
  have : CompactSpace (arla G) := h.symm.compactSpace
  have : CompactSpace (Fin n → ℝ) :=
    (arlaEquiv hd hι).toHomeomorph.compactSpace
  have hc := (isCompact_univ (X := Fin n → ℝ)).image (continuous_apply ⟨0, hn⟩)
  have himg : (fun x : Fin n → ℝ => x ⟨0, hn⟩) '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective fun r => ⟨fun _ => r, rfl⟩
  rw [himg] at hc
  exact noncompact_univ ℝ hc

end Lift

end AdelicToriLean
