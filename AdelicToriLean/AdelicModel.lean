import AdelicToriLean.AdelicKernel
import Pontryagin.Duality

/-!
# The adelic model of the dual of a lattice `ℤⁿ ⊆ D ⊆ ℚⁿ`

Let `D` be a discrete abelian group with an injective homomorphism `ι : D → ℚⁿ` whose image
contains `ℤⁿ` (in the paper, `D = G^∨` and `ι` identifies `G^∨` with a group between `ℤⁿ` and
`ℚⁿ`). The paper's map is

`Φ : 𝔸ⁿ → D^∨`,  `Φ(a)(d) = e(⟪a, ι d⟫)`,  `e : ℝ/ℤ ≅ 𝕋`.

* `Phi_add`, `continuous_Phi`: `Φ` is a continuous homomorphism;
* `Phi_eq_one_iff`, `ker_Phi`: `Φ(a) = 1` iff `a ∈ C + Λ̃` (by `annihilator_eq`);
* `exists_mem_K_add_diag`: every `a ∈ 𝔸ⁿ` is `k + diag r` with `k ∈ K = (ℤ̂ × [0, 1])ⁿ`;
* `Phi_surjective`: **`Φ` is onto `D^∨`**. Its image is compact (`Φ(K)`), hence closed; if it
  were proper, the vendored duality theorem would give a nonzero `d ∈ D` with `⟪a, ι d⟫ = 0` for
  all `a`, which fails for a suitable real vector `a`.
-/

open IsDedekindDomain

noncomputable section

namespace AdelicToriLean

variable {n : ℕ} {D : Type*} [CommGroup D] [TopologicalSpace D] [DiscreteTopology D]

theorem pairing_zero (a : An n) : pairing (0 : Fin n → ℚ) a = 0 := by
  rw [pairing_apply]; simp [pair1_zero]

/-- `Φ(a) ∈ D^∨`, `Φ(a)(d) = e(⟪a, ι d⟫)`. -/
def Phi (ι : Additive D →+ (Fin n → ℚ)) (a : An n) : PontryaginDual D :=
  ⟨{ toFun := fun d => AddCircle.toCircle (pairing (ι (Additive.ofMul d)) a)
     map_one' := by
       simp only [ofMul_one, map_zero, pairing_zero]
       exact AddCircle.toCircle_zero
     map_mul' := fun d d' => by
       simp only [ofMul_mul, map_add, pairing_add, AddCircle.toCircle_add] }, by
    exact continuous_of_discreteTopology⟩

variable (ι : Additive D →+ (Fin n → ℚ))

theorem Phi_apply (a : An n) (d : D) :
    Phi ι a d = AddCircle.toCircle (pairing (ι (Additive.ofMul d)) a) := rfl

theorem Phi_add (a b : An n) : Phi ι (a + b) = Phi ι a * Phi ι b := by
  ext d
  simp only [Phi_apply, map_add, AddCircle.toCircle_add]
  rfl

theorem Phi_zero : Phi ι 0 = 1 := by
  ext d
  simp only [Phi_apply, map_zero, AddCircle.toCircle_zero, PontryaginDual.one_apply]

theorem Phi_neg (a : An n) : Phi ι (-a) = (Phi ι a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← Phi_add, neg_add_cancel, Phi_zero]

theorem continuous_Phi : Continuous (Phi ι) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : An n × D => AddCircle.toCircle (pairing (ι (Additive.ofMul p.2)) p.1))
  refine continuous_prod_of_discrete_right.mpr fun d => ?_
  show Continuous fun a : An n => AddCircle.toCircle (pairing (ι (Additive.ofMul d)) a)
  have h1 := continuous_pairing (n := n) (ι (Additive.ofMul d))
  exact AddCircle.continuous_toCircle.comp h1

theorem Phi_eq_one_iff (a : An n) :
    Phi ι a = 1 ↔ ∀ d : D, pairing (ι (Additive.ofMul d)) a = 0 := by
  constructor
  · intro h d
    have := congrArg (fun χ : PontryaginDual D => χ d) h
    simp only [Phi_apply, PontryaginDual.one_apply] at this
    rw [← AddCircle.toCircle_zero] at this
    exact AddCircle.injective_toCircle one_ne_zero this
  · intro h
    ext d
    rw [Phi_apply, h d, AddCircle.toCircle_zero, PontryaginDual.one_apply]

/-- **Kernel of `Φ`**: `Φ(a) = 1` iff `a = (u, 0) + diag r` with `u ∈ C` and `r ∈ ℚⁿ`. -/
theorem ker_Phi (hZ : ∀ j : Fin n, Pi.single j 1 ∈ Set.range ι) (a : An n) :
    Phi ι a = 1 ↔ ∃ u ∈ annC (Set.range ι), ∃ r : Fin n → ℚ, a = finPart u + diag r := by
  rw [Phi_eq_one_iff, ← annihilator_eq hZ a]
  constructor
  · rintro h _ ⟨d, rfl⟩; exact h (Additive.toMul d)
  · intro h d; exact h _ ⟨_, rfl⟩

theorem Phi_diag (r : Fin n → ℚ) : Phi ι (diag r) = 1 :=
  (Phi_eq_one_iff ι _).mpr fun _ => pairing_diag _ r

/-- `K = (ℤ̂ × [0, 1])ⁿ`. -/
def Kset (n : ℕ) : Set (An n) := Set.univ.pi fun _ => (ZHat : Set QHat) ×ˢ Set.Icc (0 : ℝ) 1

theorem isCompact_Kset (n : ℕ) : IsCompact (Kset n) :=
  isCompact_univ_pi fun _ => isCompact_ZHat.prod isCompact_Icc

/-- **Fundamental domain.** Every `a ∈ 𝔸ⁿ` is `k + diag r` with `k ∈ K`. -/
theorem exists_mem_K_add_diag (a : An n) : ∃ k ∈ Kset n, ∃ r : Fin n → ℚ, a = k + diag r := by
  have hsa : ∀ i, ∃ r : ℚ, ∃ z ∈ ZHat, (a i).1 = algebraMap ℚ QHat r + z :=
    fun i => exists_rat_add_ZHat (a i).1
  choose r z hz hrz using hsa
  set m : Fin n → ℤ := fun i => ⌊(a i).2 - (r i : ℝ)⌋
  set r' : Fin n → ℚ := fun i => r i + m i
  set k : An n := fun i => (z i - algebraMap ℚ QHat (m i : ℚ), (a i).2 - (r i : ℝ) - m i)
  refine ⟨k, fun i _ => ⟨ZHat.sub_mem (hz i) (algebraMap_int_mem_ZHat (m i)),
    Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, r', ?_⟩
  funext i
  refine Prod.ext ?_ ?_
  · show (a i).1 = (z i - algebraMap ℚ QHat (m i : ℚ)) + algebraMap ℚ QHat (r' i)
    simp only [r', map_add, hrz i]; ring
  · show (a i).2 = ((a i).2 - (r i : ℝ) - m i) + ((r' i : ℚ) : ℝ)
    simp only [r']; push_cast; ring

theorem range_Phi_eq_image : Set.range (Phi ι) = Phi ι '' Kset n := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨k, hk, r, rfl⟩ := exists_mem_K_add_diag a
    exact ⟨k, hk, by rw [Phi_add, Phi_diag, mul_one]⟩
  · rintro _ ⟨a, _, rfl⟩; exact ⟨a, rfl⟩

/-- The image of `Φ` as a subgroup of `D^∨`. -/
def rangePhi : Subgroup (PontryaginDual D) where
  carrier := Set.range (Phi ι)
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, Phi_add ι a b⟩
  one_mem' := ⟨0, Phi_zero ι⟩
  inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, Phi_neg ι a⟩

theorem isClosed_rangePhi : IsClosed (rangePhi ι : Set (PontryaginDual D)) := by
  show IsClosed (Set.range (Phi ι))
  rw [range_Phi_eq_image]
  exact ((isCompact_Kset n).image (continuous_Phi ι)).isClosed

/-- `⟪(0, x e_j), b⟫ = -b_j x`. -/
theorem pairing_realSingle (b : Fin n → ℚ) (j : Fin n) (x : ℝ) :
    pairing b (Pi.single j ((0 : QHat), x)) = -realChar (b j) x := by
  rw [pairing_apply, Finset.sum_eq_single j]
  · simp [pair1_apply, finChar]
  · intro i _ hij; rw [Pi.single_eq_of_ne hij, map_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem half_ne_zero : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
  rw [Ne, AddCircle.coe_eq_zero_iff]
  rintro ⟨m, hm⟩
  rw [zsmul_one] at hm
  have h1 : (0 : ℝ) < m := by linarith
  have h2 : (m : ℝ) < 1 := by linarith
  have h1' : (0 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < (1 : ℤ) := by exact_mod_cast h2
  omega

/-- **`Φ` is surjective.** -/
theorem Phi_surjective (hι : Function.Injective ι) : Function.Surjective (Phi ι) := by
  classical
  intro x
  by_contra hx
  have hxH : x ∉ rangePhi ι := by rintro ⟨a, rfl⟩; exact hx ⟨a, rfl⟩
  set H := rangePhi ι
  have : IsClosed (H : Set (PontryaginDual D)) := isClosed_rangePhi ι
  -- the compact Hausdorff quotient `D^∨ / H`
  have hne : (QuotientGroup.mk x : PontryaginDual D ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have hinj := PontryaginDual.eval_injective (PontryaginDual D ⧸ H)
  have hev : PontryaginDual.eval (QuotientGroup.mk x : PontryaginDual D ⧸ H) ≠ 1 := by
    intro h
    apply hne
    apply hinj
    rw [h, map_one]
  obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual (PontryaginDual D ⧸ H), χ (QuotientGroup.mk x) ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hev (PontryaginDual.ext fun χ => by
      rw [PontryaginDual.eval_apply, hall χ, PontryaginDual.one_apply])
  -- pull back to a character of `D^∨` trivial on `H`
  let ψ : PontryaginDual (PontryaginDual D) :=
    ⟨χ.toMonoidHom.comp (QuotientGroup.mk' H), χ.continuous.comp continuous_quot_mk⟩
  have hψH : ∀ a, ψ (Phi ι a) = 1 := by
    intro a
    show χ (QuotientGroup.mk (Phi ι a)) = 1
    have hmem : Phi ι a ∈ H := Set.mem_range_self a
    rw [(QuotientGroup.eq_one_iff _).mpr hmem, map_one]
  have hψx : ψ x ≠ 1 := hχ
  -- by duality, `ψ` is evaluation at some `d ∈ D`
  obtain ⟨d, hd⟩ := PontryaginDual.eval_surjective D ψ
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hψx
    rw [← hd, map_one, PontryaginDual.one_apply]
  have hpair : ∀ a, pairing (ι (Additive.ofMul d)) a = 0 := by
    intro a
    have h := hψH a
    rw [← hd, PontryaginDual.eval_apply, Phi_apply, ← AddCircle.toCircle_zero] at h
    exact AddCircle.injective_toCircle one_ne_zero h
  have hιd : ι (Additive.ofMul d) ≠ 0 := by
    intro h
    apply hd1
    have : ι (Additive.ofMul d) = ι 0 := by rw [h, map_zero]
    exact Additive.ofMul.injective (hι this)
  obtain ⟨j, hj⟩ : ∃ j, ι (Additive.ofMul d) j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hιd (funext hall)
  set q := ι (Additive.ofMul d) j
  have h := hpair (Pi.single j ((0 : QHat), 1 / (2 * (q : ℝ))))
  rw [pairing_realSingle] at h
  simp only [realChar, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
    QuotientAddGroup.mk'_apply, neg_eq_zero] at h
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hj
  rw [show (q : ℝ) * (1 / (2 * (q : ℝ))) = 1 / 2 by field_simp] at h
  exact half_ne_zero h

end AdelicToriLean
