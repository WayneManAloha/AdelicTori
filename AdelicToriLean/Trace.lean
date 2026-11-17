import AdelicToriLean.Commute

/-!
# Trace duality: the commutator `Dt` vanishes

`Wt ψ t` is the transpose of `Dt ψ t` for the trace form: `τ (W a) y = τ a (Dt y)`.

* `dual_mem`: for `a ∈ 𝓞 K` and the `m` of `uniform_defect`, `m · W a ∈ dual(1) · P k`.
* `commutes`: `Dt ψ t = 0`, i.e. `ψ (t y) = t ψ y` for all `t ∈ 𝓞 K`, `y ∈ K`.
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean.DegreeOnePrimes

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K) (ψ : K →ₗ[ℚ] K)

/-- Transpose of `Dt ψ t` for the trace form. -/
def Wt (t : 𝓞 K) : K →ₗ[ℚ] K :=
  ((Algebra.traceForm ℚ K).toDual (traceForm_nondegenerate ℚ K)).symm.toLinearMap ∘ₗ
    (LinearMap.lcomp ℚ ℚ (Dt ψ t)) ∘ₗ Algebra.traceForm ℚ K

theorem Wt_spec (t : 𝓞 K) (a y : K) :
    Algebra.traceForm ℚ K (Wt ψ t a) y = Algebra.traceForm ℚ K a (Dt ψ t y) := by
  simp [Wt, LinearMap.BilinForm.apply_toDual_symm_apply, LinearMap.lcomp_apply]

theorem trace_int (a o : 𝓞 K) :
    Algebra.traceForm ℚ K (a : K) (o : K) ∈ (algebraMap ℤ ℚ).range := by
  have ha : (a : K) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.mem_one_iff _ |>.mpr ⟨a, rfl⟩)
  rw [FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)] at ha
  exact ha _ ((FractionalIdeal.mem_one_iff _).mpr ⟨o, rfl⟩)

theorem Ik_inv (k : ℕ) : ((D.Ik k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (((D.q k : ℕ) : K)⁻¹) * D.Pf k := by
  rw [D.Ik_frac k, mul_inv, FractionalIdeal.spanSingleton_inv, Pinv, inv_inv]

/-- Step 3: `m · W a ∈ dual(1) · P k`. -/
theorem dual_mem (t : 𝓞 K) (k : ℕ) (m : ℕ)
    (hm : ∀ y ∈ D.Ik k, ∃ o : 𝓞 K, (m : K) * Dt ψ t (y : K) = ((D.q k : ℕ) : K) * o) (a : 𝓞 K) :
    (m : K) * Wt ψ t (a : K) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) * D.Pf k := by
  have hq : ((D.q k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (D.q_prime k).ne_zero
  set x : K := (((m : ℚ) / (D.q k : ℚ)) : ℚ) • Wt ψ t (a : K)
  have hx : x ∈ FractionalIdeal.dual ℤ ℚ ((D.Ik k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) (D.Ik_ne_zero k)]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    obtain ⟨o, ho⟩ := hm y' hy'
    have e1 : Algebra.traceForm ℚ K x (algebraMap (𝓞 K) K y') =
        ((m : ℚ) / (D.q k : ℚ)) * Algebra.traceForm ℚ K (a : K) (Dt ψ t (y' : K)) := by
      simp only [x, LinearMap.map_smul₂, smul_eq_mul]
      rw [Wt_spec]
    have e2 : (m : ℚ) • Dt ψ t (y' : K) = (D.q k : ℚ) • (o : K) := by
      rw [Rat.smul_def, Rat.smul_def]; push_cast; exact ho
    have e3 : (m : ℚ) * Algebra.traceForm ℚ K (a : K) (Dt ψ t (y' : K)) =
        (D.q k : ℚ) * Algebra.traceForm ℚ K (a : K) (o : K) := by
      rw [← smul_eq_mul, ← LinearMap.map_smul, e2, LinearMap.map_smul, smul_eq_mul]
    rw [e1, div_mul_eq_mul_div, e3, mul_div_cancel_left₀ _ hq]
    exact trace_int a o
  have hdual := FractionalIdeal.dual_eq_mul_inv ℤ ℚ ((D.Ik k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
  rw [hdual, D.Ik_inv k] at hx
  have hqK : ((D.q k : ℕ) : K) ≠ 0 := D.q_ne_zero_K k
  have hmem : ((D.q k : ℕ) : K) * x ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ ((D.q k : ℕ) : K) *
      (FractionalIdeal.dual ℤ ℚ 1 *
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (((D.q k : ℕ) : K)⁻¹) * D.Pf k)) :=
    FractionalIdeal.mem_singleton_mul.mpr ⟨x, hx, rfl⟩
  have hid : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((D.q k : ℕ) : K) *
      (FractionalIdeal.dual ℤ ℚ 1 *
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (((D.q k : ℕ) : K)⁻¹) * D.Pf k)) =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) * D.Pf k := by
    rw [mul_left_comm, ← mul_assoc (FractionalIdeal.spanSingleton _ _),
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hqK,
      FractionalIdeal.spanSingleton_one, one_mul]
  rw [hid] at hmem
  convert hmem using 1
  simp only [x, Rat.smul_def]
  push_cast
  field_simp

end AdelicToriLean.DegreeOnePrimes
