import AdelicToriLean.RatFract
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# The standard character of the finite adeles of `ℚ`

`ℚ̂ = 𝔸ᶠ[ℤ, ℚ]` is Mathlib's ring of finite adeles: the restricted product of the completions
`ℚ_v` over the nonzero primes `v` of `ℤ`, with respect to `ℤ_v`. The paper's pairing uses
`u ↦ ∑_p {u_p}_p ∈ ℝ/ℤ`. Here:

* `frV v`: the fractional part on `ℚ_v`, transported from `ℚ_p` (`Padic.adicCompletionEquiv`);
* `psi : ℚ̂ →+ ℝ/ℤ`, `psi u = ∑ᶠ v, {u_v}_v`;
* `continuous_psi`;
* `psi_eq_zero_of_integral`: `psi` vanishes on `∏ ℤ_v`;
* `psi_algebraMap`: **diagonal identity** `psi r = r (mod 1)` for `r ∈ ℚ`.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum

noncomputable section

namespace AdelicToriLean

/-- The ring of finite adeles of `ℚ` (Mathlib's `𝔸ᶠ[ℤ, ℚ]`). -/
abbrev QHat := FiniteAdeleRing ℤ ℚ

/-- The fractional part on the completion `ℚ_v`. -/
def frV (v : HeightOneSpectrum ℤ) : v.adicCompletion ℚ →+ AddCircle (1 : ℝ) :=
  AddMonoidHom.mk' (fun x => fr (primesEquiv v) (adicCompletion.padicEquiv v x))
    (fun x y => by simp only [map_add])

theorem continuous_frV (v : HeightOneSpectrum ℤ) : Continuous (frV v) := by
  have : Fact ((primesEquiv v : ℕ).Prime) := ⟨(primesEquiv v).prop⟩
  exact (continuous_fractP _).comp (adicCompletion.padicEquiv v).continuous

theorem frV_eq_zero_of_mem {v : HeightOneSpectrum ℤ} {x : v.adicCompletion ℚ}
    (hx : x ∈ v.adicCompletionIntegers ℚ) : frV v x = 0 := by
  have : Fact ((primesEquiv v : ℕ).Prime) := ⟨(primesEquiv v).prop⟩
  have h := (adicCompletion.padicEquiv_bijOn v).mapsTo hx
  exact fractP_eq_zero_of_norm_le _ h

theorem frV_rat (v : HeightOneSpectrum ℤ) (r : ℚ) :
    frV v (algebraMap ℚ (v.adicCompletion ℚ) r) = fr (primesEquiv v) (r : ℚ_[primesEquiv v]) := by
  simp only [frV, AddMonoidHom.mk'_apply]
  rw [show adicCompletion.padicEquiv v (algebraMap ℚ (v.adicCompletion ℚ) r) =
      algebraMap ℚ ℚ_[primesEquiv v] r from (adicCompletion.padicEquiv v).commutes r, eq_ratCast]

theorem support_frV_finite (a : QHat) :
    (Function.support fun v : HeightOneSpectrum ℤ => frV v (a v)).Finite := by
  have h : ∀ᶠ v in Filter.cofinite, a v ∈ v.adicCompletionIntegers ℚ := a.eventually
  rw [Filter.eventually_cofinite] at h
  refine h.subset fun v hv => ?_
  intro hint
  exact hv (frV_eq_zero_of_mem hint)

/-- **The standard character** `ψ : ℚ̂ → ℝ/ℤ`, `ψ(u) = ∑_p {u_p}_p`. -/
def psi : QHat →+ AddCircle (1 : ℝ) where
  toFun a := ∑ᶠ v : HeightOneSpectrum ℤ, frV v (a v)
  map_zero' := by
    exact finsum_eq_zero_of_forall_eq_zero fun v => by
      rw [show (0 : QHat) v = 0 from rfl, map_zero]
  map_add' a b := by
    rw [← finsum_add_distrib (support_frV_finite a) (support_frV_finite b)]
    exact finsum_congr fun v => by rw [show (a + b) v = a v + b v from rfl, map_add]

theorem psi_apply (a : QHat) : psi a = ∑ᶠ v : HeightOneSpectrum ℤ, frV v (a v) := rfl

/-- `ψ` vanishes on the integral adeles `∏_v ℤ_v`. -/
theorem psi_eq_zero_of_integral {a : QHat} (ha : ∀ v, a v ∈ v.adicCompletionIntegers ℚ) :
    psi a = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun v => frV_eq_zero_of_mem (ha v)

/-- The integral adeles form an open subset of `ℚ̂`. -/
theorem isOpen_integral :
    IsOpen {a : QHat | ∀ v, a v ∈ v.adicCompletionIntegers ℚ} := by
  have hAopen : Fact (∀ v : HeightOneSpectrum ℤ,
      IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isOpen_forall_mem hAopen.out

/-- `ψ` is continuous. -/
theorem continuous_psi : Continuous psi := by
  refine continuous_of_continuousAt_zero psi ?_
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [isOpen_integral.mem_nhds (fun v => (v.adicCompletionIntegers ℚ).zero_mem)]
    with a ha
  rw [psi_eq_zero_of_integral ha, map_zero]

/-- **Diagonal identity.** For `r ∈ ℚ`, `ψ(r) = r (mod 1)`. -/
theorem psi_algebraMap (r : ℚ) : psi (algebraMap ℚ QHat r) = ((r : ℝ) : AddCircle (1 : ℝ)) := by
  rw [psi_apply]
  have : ∀ v : HeightOneSpectrum ℤ, frV v ((algebraMap ℚ QHat r) v) =
      fr (primesEquiv v) (r : ℚ_[primesEquiv v]) := fun v => frV_rat v r
  rw [finsum_congr this]
  rw [finsum_comp_equiv (primesEquiv (R := ℤ)) (f := fun p : Nat.Primes => fr p (r : ℚ_[p]))]
  exact (sum_fract_rat r).2

end AdelicToriLean
