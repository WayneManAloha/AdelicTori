import Mathlib

/-!
# The group of integers `B_K = Σ_k 𝔭_k⁻¹`: setup

`K` is a number field and `𝓞 K` its ring of integers.

The only number-theoretic input is the structure `DegreeOnePrimes K`: an infinite sequence of
ideals `P k` of `𝓞 K` with `Ideal.absNorm (P k) = q k`, where the `q k` are pairwise distinct
rational primes. This is an explicit external hypothesis. Its existence (infinitely many
degree-one primes, e.g. completely split primes) is classical but not proved here.

`BK D` is the `𝓞 K`-submodule `Σ_k (P k)⁻¹` of `K`.
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean

variable (K : Type*) [Field K] [NumberField K]

/-- External hypothesis: degree-one primes over pairwise distinct rational primes. -/
structure DegreeOnePrimes where
  q : ℕ → ℕ
  P : ℕ → Ideal (𝓞 K)
  q_prime : ∀ k, (q k).Prime
  q_inj : Function.Injective q
  norm_eq : ∀ k, Ideal.absNorm (P k) = q k

variable {K}

namespace DegreeOnePrimes

variable (D : DegreeOnePrimes K)

theorem isPrime (k : ℕ) : (D.P k).IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm (by rw [D.norm_eq k]; exact (Nat.prime_iff.mp (D.q_prime k)).irreducible)

theorem ne_bot (k : ℕ) : D.P k ≠ ⊥ := by
  intro h; have := D.norm_eq k; rw [h, Ideal.absNorm_bot] at this; exact (D.q_prime k).ne_zero this.symm

theorem q_mem (k : ℕ) : ((D.q k : ℕ) : 𝓞 K) ∈ D.P k := by
  have := Ideal.absNorm_mem (D.P k); rwa [D.norm_eq k] at this

/-- `P k` as a fractional ideal of `K`. -/
abbrev Pf (k : ℕ) : FractionalIdeal (𝓞 K)⁰ K := (D.P k : FractionalIdeal (𝓞 K)⁰ K)

/-- `(P k)⁻¹`. -/
abbrev Pinv (k : ℕ) : FractionalIdeal (𝓞 K)⁰ K := (D.Pf k)⁻¹

theorem Pf_ne_zero (k : ℕ) : D.Pf k ≠ 0 := by
  simpa [Pf] using D.ne_bot k

theorem Pf_mul_Pinv (k : ℕ) : D.Pf k * D.Pinv k = 1 := mul_inv_cancel₀ (D.Pf_ne_zero k)

theorem one_le_Pinv (k : ℕ) : 1 ≤ D.Pinv k := by
  have := FractionalIdeal.inv_anti_mono (D.Pf_ne_zero k) one_ne_zero FractionalIdeal.coeIdeal_le_one
  rwa [inv_one] at this

/-- `B_K = Σ_k (P k)⁻¹` as an `𝓞 K`-submodule of `K`. -/
def BK : Submodule (𝓞 K) K := ⨆ k, ((D.Pinv k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

/-- `𝓞 K` as a submodule of `K`. -/
abbrev OK (_D : DegreeOnePrimes K) : Submodule (𝓞 K) K := ((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

theorem Pinv_le_BK (k : ℕ) : ((D.Pinv k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ D.BK :=
  le_iSup (fun k => ((D.Pinv k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) k

theorem OK_le_BK : D.OK ≤ D.BK :=
  le_trans (FractionalIdeal.coe_le_coe.mpr (D.one_le_Pinv 0)) (D.Pinv_le_BK 0)

/-- `q_k · (P k)⁻¹ ⊆ 𝓞 K`. -/
theorem q_smul_Pinv (k : ℕ) {x : K} (hx : x ∈ (D.Pinv k : Submodule (𝓞 K) K)) :
    ((D.q k : ℕ) : K) * x ∈ D.OK := by
  have h1 : (algebraMap (𝓞 K) K ((D.q k : ℕ) : 𝓞 K)) ∈ (D.Pf k : Submodule (𝓞 K) K) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, D.q_mem k, rfl⟩
  have h2 := FractionalIdeal.mul_mem_mul h1 hx
  rw [D.Pf_mul_Pinv k] at h2
  simpa using h2

end DegreeOnePrimes

end AdelicToriLean
