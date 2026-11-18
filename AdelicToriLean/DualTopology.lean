import AdelicToriLean.Kumu

/-!
# Remark `dense-subgroups-dual-topologies`

Let `A` be a discrete torsion-free abelian group with `ι : A → ℚⁿ` injective of full rank
(`ℚ ι(A) = ℚⁿ`) and no free summands, so `Hom(A, ℤ) = 0`. With
`exp_a : ℝⁿ → A^∨`, `exp_a(x)(a) = e^{2πi⟨x, ι a⟩}`:

* `expA_injective`: `exp_a` is injective;
* `dense_expA_A`: `B = exp_a(ι(A))` is dense in the compact Hausdorff group `A^∨`;
* `expA_A_injective`: `a ↦ exp_a(ι a)` is injective, so `B ≅ A`.

Hence the completion of `A` in its dual topology (transported from `B ⊆ A^∨`) is `A^∨`
(`dense_subgroups_dual_topologies`). `hom_eq_zero_of_noFreeSummand`: no free summands gives
`Hom(A, ℤ) = 0`.
-/

open Topology Real

noncomputable section

namespace AdelicToriLean

/-- No free summands gives `Hom(A, ℤ) = 0`: a nonzero `f : A → ℤ` splits off a copy of `ℤ`. -/
theorem hom_eq_zero_of_noFreeSummand {A : Type*} [AddCommGroup A]
    (h : ∀ B C : AddSubgroup A, IsCompl B C → IsEmpty (C ≃+ ℤ)) (f : A →+ ℤ) : f = 0 := by
  by_contra hf
  obtain ⟨a0, ha0⟩ : ∃ a, f a ≠ 0 := by
    by_contra h'; simp only [not_exists, not_not] at h'; exact hf (AddMonoidHom.ext h')
  -- the least positive value `d`
  have hex : ∃ k : ℕ, 0 < k ∧ ∃ a, f a = k :=
    ⟨(f a0).natAbs, Int.natAbs_pos.mpr ha0, by
      rcases Int.natAbs_eq (f a0) with h1 | h1
      · exact ⟨a0, by omega⟩
      · exact ⟨-a0, by rw [map_neg]; omega⟩⟩
  classical
  set d := Nat.find hex
  obtain ⟨hd, a1, ha1⟩ := Nat.find_spec hex
  replace ha1 : f a1 = (d : ℤ) := ha1
  replace hd : 0 < d := hd
  -- every value is a multiple of `d`
  have hdvd : ∀ a, (d : ℤ) ∣ f a := by
    intro a
    have hr := Int.emod_emod_of_dvd (f a) (dvd_refl (d : ℤ))
    set r := f a % d
    have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hd.ne')
    have hrd : r < d := Int.emod_lt_of_pos _ (by exact_mod_cast hd)
    have hval : f (a - (f a / d) • a1) = r := by
      rw [map_sub, map_zsmul, ha1, smul_eq_mul]
      show _ = f a % (d : ℤ)
      rw [Int.emod_def]
      ring
    by_contra hnd
    have hr_pos : 0 < r := lt_of_le_of_ne hr0 (fun h0 => hnd (Int.dvd_of_emod_eq_zero h0.symm))
    have hmin := Nat.find_min' hex
      (show 0 < r.toNat ∧ ∃ a, f a = (r.toNat : ℤ) from ⟨by omega, _, by rw [hval]; omega⟩)
    omega
  set g : A →+ ℤ :=
    { toFun := fun a => f a / d
      map_zero' := by simp
      map_add' := fun a b => by
        rw [map_add, Int.add_ediv_of_dvd_left (hdvd a)] }
  have hg1 : g a1 = 1 := by
    show f a1 / d = 1
    rw [ha1]; exact Int.ediv_self (by exact_mod_cast hd.ne')
  set C : AddSubgroup A := AddSubgroup.zmultiples a1
  have hcompl : IsCompl g.ker C := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨hx1, ⟨k, rfl⟩⟩
      have : g (k • a1) = 0 := hx1
      rw [map_zsmul, hg1, smul_eq_mul, mul_one] at this
      simp [this]
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : x - g x • a1 ∈ g.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, map_zsmul, hg1, smul_eq_mul, mul_one, sub_self]
      have := AddSubgroup.add_mem_sup hx (AddSubgroup.zsmul_mem_zmultiples a1 (g x))
      simpa using this
  have hiso : C ≃+ ℤ :=
    { toFun := fun c => g c.1
      invFun := fun k => ⟨k • a1, AddSubgroup.zsmul_mem_zmultiples a1 k⟩
      left_inv := by
        rintro ⟨_, k, rfl⟩
        apply Subtype.ext
        show (g (k • a1)) • a1 = k • a1
        rw [map_zsmul, hg1, smul_eq_mul, mul_one]
      right_inv := fun k => by
        show g (k • a1) = k
        rw [map_zsmul, hg1, smul_eq_mul, mul_one]
      map_add' := fun x y => map_add g x.1 y.1 }
  exact (h _ _ hcompl).false hiso

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] {n : ℕ}
  (ι : A →+ (Fin n → ℚ))

instance : DiscreteTopology (Multiplicative A) := inferInstanceAs (DiscreteTopology A)

instance : CompactSpace (PontryaginDual (Multiplicative A)) :=
  inferInstanceAs (CompactSpace (ContinuousMonoidHom (Multiplicative A) Circle))

/-- `⟨x, v⟩ = ∑ xᵢ vᵢ`. -/
def ip (x : Fin n → ℝ) (v : Fin n → ℚ) : ℝ := ∑ i, x i * (v i : ℝ)

omit [TopologicalSpace A] [DiscreteTopology A] in
theorem ip_add_right (x : Fin n → ℝ) (v w : Fin n → ℚ) : ip x (v + w) = ip x v + ip x w := by
  simp [ip, mul_add, Finset.sum_add_distrib]

/-- **The archimedean exponential** `exp_a : ℝⁿ → A^∨`, `x ↦ (a ↦ e^{2πi⟨x, ι a⟩})`. -/
def expA : Multiplicative (Fin n → ℝ) →* PontryaginDual (Multiplicative A) where
  toFun x :=
    ⟨{ toFun := fun a => Circle.exp (2 * π * ip (Multiplicative.toAdd x)
          (ι (Multiplicative.toAdd a)))
       map_one' := by simp [ip]
       map_mul' := fun a b => by
         simp only [toAdd_mul, map_add, ip_add_right, mul_add, Circle.exp_add] },
      continuous_of_discreteTopology⟩
  map_one' := ContinuousMonoidHom.ext fun a => by
    show Circle.exp (2 * π * ip 0 _) = 1
    simp [ip]
  map_mul' x y := ContinuousMonoidHom.ext fun a => by
    show Circle.exp (2 * π * ip (Multiplicative.toAdd x + Multiplicative.toAdd y) _) =
      Circle.exp (2 * π * ip (Multiplicative.toAdd x) _) *
        Circle.exp (2 * π * ip (Multiplicative.toAdd y) _)
    rw [← Circle.exp_add, ← mul_add]
    congr 2
    simp [ip, add_mul, Finset.sum_add_distrib]

theorem expA_apply (x : Multiplicative (Fin n → ℝ)) (a : Multiplicative A) :
    expA ι x a = Circle.exp (2 * π * ip (Multiplicative.toAdd x) (ι (Multiplicative.toAdd a))) :=
  rfl

theorem continuous_expA : Continuous (expA ι) := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous fun p : Multiplicative (Fin n → ℝ) × Multiplicative A =>
    Circle.exp (2 * π * ip (Multiplicative.toAdd p.1) (ι (Multiplicative.toAdd p.2)))
  rw [continuous_prod_of_discrete_right]
  intro a
  show Continuous fun x : Multiplicative (Fin n → ℝ) =>
    Circle.exp (2 * π * ∑ i, Multiplicative.toAdd x i * ((ι (Multiplicative.toAdd a) i : ℚ) : ℝ))
  exact Circle.exp.continuous.comp (continuous_const.mul (continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_toAdd).mul continuous_const))

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- An additive `s : A → ℝ` with `e^{2πi s} ≡ 1` is integer-valued, hence `0` when
`Hom(A, ℤ) = 0`. -/
theorem eq_zero_of_exp (hZ : ∀ f : A →+ ℤ, f = 0) (s : A →+ ℝ)
    (h : ∀ a, Circle.exp (2 * π * s a) = 1) : ∀ a, s a = 0 := by
  have hint : ∀ a, ∃ m : ℤ, s a = m := fun a => by
    obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp (h a)
    exact ⟨m, by
      have := pi_pos
      have : 2 * π * s a = 2 * π * m := by rw [hm]; ring
      exact mul_left_cancel₀ (by positivity) this⟩
  choose m hm using hint
  set f : A →+ ℤ :=
    { toFun := m
      map_zero' := by
        apply Int.cast_injective (α := ℝ); rw [← hm, map_zero, Int.cast_zero]
      map_add' := fun a b => by
        apply Int.cast_injective (α := ℝ)
        rw [← hm, Int.cast_add, ← hm, ← hm, map_add] }
  intro a
  rw [hm a]
  have : m a = 0 := DFunLike.congr_fun (hZ f) a
  rw [this, Int.cast_zero]

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- `⟨x, ι a⟩ = 0` for all `a` forces `x = 0` (full rank). -/
theorem eq_zero_of_ip (hQ : ∀ v : Fin n → ℚ, ∃ m : ℕ, 0 < m ∧ ∃ a, ι a = m • v)
    (x : Fin n → ℝ) (h : ∀ a, ip x (ι a) = 0) : x = 0 := by
  funext j
  obtain ⟨m, hm, a, ha⟩ := hQ (Pi.single j 1)
  have := h a
  rw [ha, ip, Finset.sum_eq_single j] at this
  · simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, Rat.cast_natCast] at this
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    exact (mul_eq_zero.mp this).resolve_right hm'
  · intro i _ hij; simp [Pi.single_eq_of_ne hij]
  · intro h'; exact absurd (Finset.mem_univ j) h'

variable {ι}
variable (hQ : ∀ v : Fin n → ℚ, ∃ m : ℕ, 0 < m ∧ ∃ a, ι a = m • v) (hZ : ∀ f : A →+ ℤ, f = 0)
include hQ hZ

/-- **`exp_a : ℝⁿ → A^∨` is injective.** -/
theorem expA_injective : Function.Injective (expA ι) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set s : A →+ ℝ :=
    { toFun := fun a => ip (Multiplicative.toAdd x) (ι a)
      map_zero' := by simp [ip]
      map_add' := fun a b => by rw [map_add, ip_add_right] }
  have h0 := eq_zero_of_exp hZ s fun a => by
    have := DFunLike.congr_fun hx (Multiplicative.ofAdd a)
    rw [PontryaginDual.one_apply] at this
    exact this
  exact Multiplicative.toAdd.injective (eq_zero_of_ip ι hQ _ h0)

/-- The embedding `a ↦ ι a ∈ ℝⁿ`. -/
def realEmb (a : A) : Multiplicative (Fin n → ℝ) := Multiplicative.ofAdd fun i => (ι a i : ℝ)

omit [TopologicalSpace A] [DiscreteTopology A] hQ hZ in
theorem ip_comm (a b : A) : ip (Multiplicative.toAdd (realEmb (ι := ι) a)) (ι b) =
    ip (Multiplicative.toAdd (realEmb (ι := ι) b)) (ι a) := by
  simp only [ip, realEmb, toAdd_ofAdd, mul_comm]

/-- **`a ↦ exp_a(ι a)` is injective**: `B = exp_a(ι(A)) ≅ A`. -/
theorem expA_A_injective (hι : Function.Injective ι) :
    Function.Injective fun a : A => expA ι (realEmb (ι := ι) a) := by
  intro a b h
  have h1 := expA_injective hQ hZ h
  apply hι
  funext i
  have := congrFun (congrArg Multiplicative.toAdd h1) i
  simp only [realEmb, toAdd_ofAdd] at this
  exact_mod_cast this

/-- **`B = exp_a(ι(A))` is dense in `A^∨`.** -/
theorem dense_expA_A (hι : Function.Injective ι) :
    Dense (Set.range fun a : A => expA ι (realEmb (ι := ι) a)) := by
  by_contra hden
  set Bsub : Subgroup (PontryaginDual (Multiplicative A)) :=
    ((expA ι).comp
      { toFun := fun a : Multiplicative A => realEmb (ι := ι) (Multiplicative.toAdd a)
        map_one' := by
          show Multiplicative.ofAdd (fun i => ((ι 0 i : ℚ) : ℝ)) = Multiplicative.ofAdd 0
          congr 1; funext i; simp
        map_mul' := fun a b => by
          show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
          rw [← ofAdd_add]; congr 1; funext i; simp }).range
  have hB : ¬ Dense (Bsub : Set (PontryaginDual (Multiplicative A))) := by
    intro h; apply hden
    convert h using 1
    ext χ
    simp only [Set.mem_range, Bsub, MonoidHom.coe_range, MonoidHom.coe_comp, MonoidHom.coe_mk,
      OneHom.coe_mk, Function.comp_apply]
    exact ⟨fun ⟨a, ha⟩ => ⟨Multiplicative.ofAdd a, ha⟩, fun ⟨a, ha⟩ => ⟨Multiplicative.toAdd a, ha⟩⟩
  obtain ⟨χ, hχ, hχ1⟩ := exists_char_of_not_dense hB
  obtain ⟨a', rfl⟩ := (PontryaginDual.toDoubleDual (Multiplicative A)).surjective χ
  apply hχ1
  -- `⟨ι a, ι a'⟩ ∈ ℤ` for all `a`, so `ι a' = 0`
  set s : A →+ ℝ :=
    { toFun := fun a => ip (Multiplicative.toAdd (realEmb (ι := ι) a')) (ι a)
      map_zero' := by simp [ip]
      map_add' := fun a b => by rw [map_add, ip_add_right] }
  have h0 := eq_zero_of_exp hZ s fun a => by
    have := hχ _ ⟨Multiplicative.ofAdd a, rfl⟩
    change expA ι (realEmb (ι := ι) a) a' = 1 at this
    rw [expA_apply, ip_comm] at this
    exact this
  have hx := eq_zero_of_ip ι hQ _ h0
  have ha' : Multiplicative.toAdd a' = 0 := hι (by
    funext i
    have := congrFun hx i
    simp only [realEmb, toAdd_ofAdd, Pi.zero_apply] at this
    rw [map_zero, Pi.zero_apply]
    exact_mod_cast this)
  have : a' = 1 := Multiplicative.toAdd.injective ha'
  rw [this, map_one]

/-- **Remark `dense-subgroups-dual-topologies`.** For `A` discrete torsion-free of rank `n`
(`ι : A → ℚⁿ` of full rank) with `Hom(A, ℤ) = 0`: `exp_a : ℝⁿ → A^∨` is continuous and
injective, and `B = exp_a(ι(A)) ≅ A` is dense in the compact Hausdorff group `A^∨`; so `A^∨`
is the completion of `A` in its dual topology. -/
theorem dense_subgroups_dual_topologies (hι : Function.Injective ι) :
    Continuous (expA ι) ∧ Function.Injective (expA ι) ∧
      Function.Injective (fun a : A => expA ι (realEmb (ι := ι) a)) ∧
      Dense (Set.range fun a : A => expA ι (realEmb (ι := ι) a)) ∧
      CompactSpace (PontryaginDual (Multiplicative A)) ∧ T2Space (PontryaginDual (Multiplicative A)) :=
  ⟨continuous_expA ι, expA_injective hQ hZ, expA_A_injective hQ hZ hι, dense_expA_A hQ hZ hι,
    inferInstance, inferInstance⟩

end AdelicToriLean
