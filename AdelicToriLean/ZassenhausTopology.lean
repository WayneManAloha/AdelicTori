import AdelicToriLean.DualTopology
import AdelicToriLean.DeltaExistence

/-!
# Topological half of `zassenhaus-realisation`

Let `A` be a discrete abelian group with `ι : A → ℚⁿ` injective and `d_j ∈ A` with
`ι(d_j) = e_j`; `F = ⟨d_1, …, d_n⟩ ≅ ℤⁿ` and `T = A/F` (for `A = B_K`, `F = 𝒪_K`). Write
`T^∨ = F^⊥ ⊆ A^∨` (`Tperp`), the characters trivial on `F`.

* `Tperp_isDelta`: `T^∨` is a delta-subgroup of `A^∨`, with `A^∨/T^∨ ≅ (ℝ/ℤ)ⁿ`;
* `mem_Tperp_iff`: `T^∨` is the annihilator of all of `ι⁻¹(ℤⁿ)`;
* `resolutionEquiv`: `(δ, x) ↦ δ · exp_a(x)` induces `(T^∨ × ℝⁿ)/ℤⁿ ≅ A^∨`, the kernel being the
  diagonal `ℤⁿ`, `m ↦ (exp_a(m)⁻¹, m)` (`ker_resolution`);
* `dense_diag`: the projection `{exp_a(m) : m ∈ ℤⁿ}` of the diagonal is dense in `T^∨`.
-/

open Topology Real

noncomputable section

namespace AdelicToriLean

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] {n : ℕ}

instance : LocallyCompactSpace (Multiplicative A) := inferInstanceAs (LocallyCompactSpace A)
instance : T2Space (Multiplicative A) := inferInstanceAs (T2Space A)

/-- `T^∨ = F^⊥`: the characters of `A` trivial on every `d_j`. -/
def Tperp (d : Fin n → A) : Subgroup (PontryaginDual (Multiplicative A)) where
  carrier := {χ | ∀ j, χ (Multiplicative.ofAdd (d j)) = 1}
  one_mem' _ := rfl
  mul_mem' {χ ψ} hχ hψ j := by
    show χ _ * ψ _ = 1
    rw [hχ j, hψ j, one_mul]
  inv_mem' {χ} hχ j := by
    show (χ _)⁻¹ = 1
    rw [hχ j, inv_one]

omit [DiscreteTopology A] in
theorem mem_Tperp {d : Fin n → A} {χ : PontryaginDual (Multiplicative A)} :
    χ ∈ Tperp d ↔ ∀ j, χ (Multiplicative.ofAdd (d j)) = 1 := Iff.rfl

variable {ι : A →+ (Fin n → ℚ)} {d : Fin n → A} (hd : ∀ j, ι (d j) = Pi.single j 1)

omit [TopologicalSpace A] [DiscreteTopology A] in
include hd in
/-- An `a` with integral coordinates is `∑ m_j d_j`. -/
theorem eq_sum_of_int (hι : Function.Injective ι) {a : A} {m : Fin n → ℤ}
    (hm : ∀ j, ι a j = m j) : a = ∑ j, m j • d j := hι (by
  funext i
  simp only [map_sum, map_zsmul, hd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  rw [hm i]; simp)

omit [DiscreteTopology A] in
include hd in
/-- **`T^∨` is the annihilator of `F = ι⁻¹(ℤⁿ)`.** -/
theorem mem_Tperp_iff (hι : Function.Injective ι) (χ : PontryaginDual (Multiplicative A)) :
    χ ∈ Tperp d ↔ ∀ a : A, (∀ j, ∃ m : ℤ, ι a j = m) → χ (Multiplicative.ofAdd a) = 1 := by
  constructor
  · intro hχ a ha
    choose m hm using ha
    rw [eq_sum_of_int hd hι hm]
    let f : A →+ Additive Circle := MonoidHom.toAdditiveRight (χ : Multiplicative A →* Circle)
    have hf : ∀ b, f b = Additive.ofMul (χ (Multiplicative.ofAdd b)) := fun _ => rfl
    have : f (∑ j, m j • d j) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_zsmul, hf, hχ j]; simp
    rw [hf] at this
    exact this
  · intro h j
    refine h _ fun i => ⟨if i = j then 1 else 0, ?_⟩
    rw [hd, Pi.single_apply]; split_ifs <;> simp

/-! ### `T^∨` is a delta-subgroup -/

variable (A) in
/-- Evaluation `A → A^∨∨`, an isomorphism (Pontryagin duality). -/
def evalEquiv : Multiplicative A ≃* PontryaginDual (PontryaginDual (Multiplicative A)) :=
  MulEquiv.ofBijective (PontryaginDual.eval : Multiplicative A →ₜ* _)
    ⟨PontryaginDual.eval_injective _, PontryaginDual.eval_surjective _⟩

theorem evalEquiv_apply (a : Multiplicative A) (χ : PontryaginDual (Multiplicative A)) :
    evalEquiv A a χ = χ a := rfl

variable (ι) in
/-- `ι` transported to the dual of `A^∨`. -/
def iotaG : Additive (PontryaginDual (PontryaginDual (Multiplicative A))) →+ (Fin n → ℚ) where
  toFun χ := ι (Multiplicative.toAdd ((evalEquiv A).symm (Additive.toMul χ)))
  map_zero' := by simp
  map_add' χ ψ := by simp [map_mul]

theorem iotaG_injective (hι : Function.Injective ι) : Function.Injective (iotaG ι) := by
  intro χ ψ h
  have := hι h
  have h2 := (evalEquiv A).symm.injective (Multiplicative.toAdd.injective this)
  exact Additive.toMul.injective h2

variable (d) in
/-- The characters `d_j` of `A^∨`. -/
def dG (j : Fin n) : Additive (PontryaginDual (PontryaginDual (Multiplicative A))) :=
  Additive.ofMul (evalEquiv A (Multiplicative.ofAdd (d j)))

include hd in
theorem iotaG_dG (j : Fin n) : iotaG ι (dG d j) = Pi.single j 1 := by
  simp only [iotaG, dG, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul,
    MulEquiv.symm_apply_apply, toAdd_ofAdd]
  exact hd j

theorem ker_qmap_eq :
    (qmap (PontryaginDual (Multiplicative A)) (dG d)).ker = Tperp d := by
  ext χ
  rw [MonoidHom.mem_ker, mem_Tperp, funext_iff]
  rfl

include hd in
/-- **`T^∨ = F^⊥` is a delta-subgroup of `A^∨`**: closed, totally disconnected, with
`A^∨ / T^∨ ≅ (ℝ/ℤ)ⁿ`. -/
theorem Tperp_isDelta (hι : Function.Injective ι) : IsDelta (Tperp d) n := by
  have : DiscreteTopology (PontryaginDual (PontryaginDual (Multiplicative A))) :=
    discreteTopology_dual
  rw [← ker_qmap_eq]
  exact ker_qmap_isDelta _ (iotaG_injective hι) (iotaG_dG hd)

/-! ### The resolution `A^∨ ≅ (T^∨ × ℝⁿ)/ℤⁿ` -/

include hd in
theorem expA_d (x : Multiplicative (Fin n → ℝ)) (j : Fin n) :
    expA ι x (Multiplicative.ofAdd (d j)) = Circle.exp (2 * π * Multiplicative.toAdd x j) := by
  rw [expA_apply, toAdd_ofAdd, hd, ip, Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [Pi.single_eq_of_ne hij]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- `ℤⁿ → ℝⁿ`. -/
def castZ (m : Fin n → ℤ) : Multiplicative (Fin n → ℝ) :=
  Multiplicative.ofAdd fun j => (m j : ℝ)

include hd in
theorem expA_castZ_mem (m : Fin n → ℤ) : expA ι (castZ m) ∈ Tperp d := fun j => by
  rw [expA_d hd, castZ, toAdd_ofAdd, Circle.exp_eq_one]
  exact ⟨m j, by ring⟩

variable (ι d) in
/-- `(δ, x) ↦ δ · exp_a(x)`. -/
def resol : Tperp d × Multiplicative (Fin n → ℝ) →* PontryaginDual (Multiplicative A) :=
  (Tperp d).subtype.coprod (expA ι)

theorem resol_apply (p : Tperp d × Multiplicative (Fin n → ℝ)) :
    resol ι d p = (p.1 : PontryaginDual (Multiplicative A)) * expA ι p.2 := rfl

theorem continuous_resol : Continuous (resol ι d) :=
  (continuous_subtype_val.comp continuous_fst).mul ((continuous_expA ι).comp continuous_snd)

include hd in
theorem resol_surjective : Function.Surjective (resol ι d) := by
  intro g
  have hx : ∀ j, ∃ y : ℝ, Circle.exp (2 * π * y) = g (Multiplicative.ofAdd (d j)) := fun j => by
    obtain ⟨y, hy⟩ := Circle.exp_surjective (g (Multiplicative.ofAdd (d j)))
    exact ⟨y / (2 * π), by rw [mul_div_cancel₀ _ (by positivity)]; exact hy⟩
  choose y hy using hx
  set x : Multiplicative (Fin n → ℝ) := Multiplicative.ofAdd y
  have hmem : g * (expA ι x)⁻¹ ∈ Tperp d := fun j => by
    show g _ * (expA ι x _)⁻¹ = 1
    rw [expA_d hd, toAdd_ofAdd, hy, mul_inv_cancel]
  refine ⟨(⟨_, hmem⟩, x), ?_⟩
  rw [resol_apply]
  simp

include hd in
/-- **The kernel is the diagonal `ℤⁿ`.** -/
theorem ker_resolution (p : Tperp d × Multiplicative (Fin n → ℝ)) :
    resol ι d p = 1 ↔ ∃ m : Fin n → ℤ, p.2 = castZ m ∧
      (p.1 : PontryaginDual (Multiplicative A)) = (expA ι (castZ m))⁻¹ := by
  constructor
  · intro h
    rw [resol_apply] at h
    have hj : ∀ j, ∃ m : ℤ, Multiplicative.toAdd p.2 j = m := fun j => by
      have h1 := DFunLike.congr_fun h (Multiplicative.ofAdd (d j))
      have h2 : (p.1 : PontryaginDual (Multiplicative A)) (Multiplicative.ofAdd (d j)) = 1 :=
        p.1.2 j
      change (p.1 : PontryaginDual (Multiplicative A)) _ * expA ι p.2 _ = 1 at h1
      rw [h2, one_mul, expA_d hd, Circle.exp_eq_one] at h1
      obtain ⟨m, hm⟩ := h1
      exact ⟨m, by
        have := pi_pos
        have : 2 * π * Multiplicative.toAdd p.2 j = 2 * π * m := by rw [hm]; ring
        exact mul_left_cancel₀ (by positivity) this⟩
    choose m hm using hj
    have hp2 : p.2 = castZ m := Multiplicative.toAdd.injective (funext hm)
    refine ⟨m, hp2, ?_⟩
    rw [← hp2]
    exact eq_inv_of_mul_eq_one_left h
  · rintro ⟨m, h2, h1⟩
    rw [resol_apply, h1, h2, inv_mul_cancel]

instance : SigmaCompactSpace (Multiplicative (Fin n → ℝ)) :=
  inferInstanceAs (SigmaCompactSpace (Fin n → ℝ))

include hd in
/-- **`A^∨ ≅ (T^∨ × ℝⁿ)/ℤⁿ`** as topological groups. -/
def resolutionEquiv (hι : Function.Injective ι) :
    (Tperp d × Multiplicative (Fin n → ℝ)) ⧸ (resol ι d).ker ≃ₜ*
      PontryaginDual (Multiplicative A) := by
  have hcl : IsClosed (Tperp d : Set (PontryaginDual (Multiplicative A))) :=
    (Tperp_isDelta hd hι).closed
  haveI : CompactSpace (Tperp d) := isCompact_iff_compactSpace.mp hcl.isCompact
  haveI : BaireSpace (PontryaginDual (Multiplicative A)) :=
    BaireSpace.of_t2Space_locallyCompactSpace
  have hs := resol_surjective (ι := ι) hd
  have hopen : IsOpenMap (resol ι d) :=
    MonoidHom.isOpenMap_of_sigmaCompact _ hs continuous_resol
  have hq : IsOpenQuotientMap (resol ι d) := ⟨hs, continuous_resol, hopen⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective (resol ι d) hs
  have hc : Continuous e :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr continuous_resol
  have hc' : Continuous e.symm := by
    rw [← hq.continuous_comp_iff]
    refine continuous_quot_mk.congr fun p => ?_
    apply e.injective
    rw [Function.comp_apply, MulEquiv.apply_symm_apply]
    rfl
  exact { e with continuous_toFun := hc, continuous_invFun := hc' }

/-! ### Density of the diagonal in `T^∨` -/

/-- Characters of a compact abelian group separate points from closed subgroups. -/
theorem exists_char_sep {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] {C : Subgroup G} (hC : IsClosed (C : Set G)) {x : G}
    (hx : x ∉ C) : ∃ χ : PontryaginDual G, (∀ c ∈ C, χ c = 1) ∧ χ x ≠ 1 := by
  have : IsClosed (C : Set G) := hC
  have hne : (x : G ⧸ C) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : PontryaginDual (G ⧸ C), ψ x ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hne
    apply PontryaginDual.eval_injective (G ⧸ C)
    ext ψ
    simp [PontryaginDual.eval_apply, h ψ]
  refine ⟨ψ.comp ⟨QuotientGroup.mk' C, continuous_quot_mk⟩, fun c hc => ?_, hψ⟩
  show ψ ((c : G) : G ⧸ C) = 1
  rw [(QuotientGroup.eq_one_iff _).mpr hc, map_one]

include hd in
/-- **The projection of the diagonal `ℤⁿ` is dense in `T^∨`.** -/
theorem dense_diag (hι : Function.Injective ι) :
    Dense (Set.range fun m : Fin n → ℤ =>
      (⟨expA ι (castZ m), expA_castZ_mem hd m⟩ : Tperp d)) := by
  set G := PontryaginDual (Multiplicative A)
  let Sz : Multiplicative (Fin n → ℤ) →* G :=
    (expA ι).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.pi fun j =>
      (Int.castAddHom ℝ).comp (Pi.evalAddMonoidHom (fun _ => ℤ) j)))
  have hSz : ∀ m, Sz m = expA ι (castZ (Multiplicative.toAdd m)) := fun _ => rfl
  set H := Sz.range.topologicalClosure
  rw [IsInducing.subtypeVal.dense_iff]
  rintro ⟨δ, hδ⟩
  by_contra hδH
  have hset : (Subtype.val '' Set.range fun m : Fin n → ℤ =>
      (⟨expA ι (castZ m), expA_castZ_mem hd m⟩ : Tperp d)) = ((Sz.range : Subgroup G) : Set G) := by
    ext g
    simp only [Set.mem_image, Set.mem_range, MonoidHom.coe_range]
    constructor
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩; exact ⟨Multiplicative.ofAdd m, rfl⟩
    · rintro ⟨m, rfl⟩; exact ⟨_, ⟨Multiplicative.toAdd m, rfl⟩, rfl⟩
  have hδH' : δ ∉ H := by
    intro h; apply hδH
    have h' : δ ∈ closure ((Sz.range : Subgroup G) : Set G) := h
    convert h' using 2
    exact hset
  obtain ⟨ψ, hψH, hψδ⟩ := exists_char_sep Sz.range.isClosed_topologicalClosure hδH'
  obtain ⟨a, rfl⟩ := PontryaginDual.eval_surjective (Multiplicative A) ψ
  apply hψδ
  rw [PontryaginDual.eval_apply]
  refine (mem_Tperp_iff hd hι δ).mp hδ (Multiplicative.toAdd a) fun j => ?_
  have h1 := hψH (Sz (Multiplicative.ofAdd (Pi.single j 1)))
    (Sz.range.le_topologicalClosure ⟨_, rfl⟩)
  rw [PontryaginDual.eval_apply, hSz, expA_apply, toAdd_ofAdd, castZ, toAdd_ofAdd, ip,
    Finset.sum_eq_single j, Circle.exp_eq_one] at h1
  · obtain ⟨m, hm⟩ := h1
    refine ⟨m, ?_⟩
    have := pi_pos
    simp only [Pi.single_eq_same, Int.cast_one, one_mul] at hm
    have : 2 * π * ((ι (Multiplicative.toAdd a) j : ℚ) : ℝ) = 2 * π * m := by rw [hm]; ring
    exact_mod_cast mul_left_cancel₀ (by positivity) this
  · intro i _ hij; simp [Pi.single_eq_of_ne hij]
  · intro h; exact absurd (Finset.mem_univ j) h

end AdelicToriLean
