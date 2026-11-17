import AdelicToriLean.Basic

/-!
# Local structure of `B_K` at the primes `q_k`

`locSub D k` is the `𝓞 K`-submodule of elements `x` with `m x ∈ (P k)⁻¹` for some integer `m`
prime to `q k`. Every `(P j)⁻¹` lies in it, hence so does `B_K` (`BK_le_locSub`).
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean.DegreeOnePrimes

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

theorem q_not_dvd_q {j k : ℕ} (h : j ≠ k) : ¬ D.q k ∣ D.q j := by
  intro hd
  have := (Nat.prime_dvd_prime_iff_eq (D.q_prime k) (D.q_prime j)).mp hd
  exact h (D.q_inj this.symm)

/-- Elements that become elements of `(P k)⁻¹` after multiplying by an integer prime to `q k`. -/
def locSub (k : ℕ) : Submodule (𝓞 K) K where
  carrier := {x | ∃ m : ℕ, ¬ D.q k ∣ m ∧ (m : K) * x ∈ (D.Pinv k : Submodule (𝓞 K) K)}
  add_mem' := by
    rintro x y ⟨m, hm, hx⟩ ⟨n, hn, hy⟩
    refine ⟨m * n, fun h => ((Nat.Prime.dvd_mul (D.q_prime k)).mp h).elim hm hn, ?_⟩
    have e : ((m * n : ℕ) : K) * (x + y) = (n : 𝓞 K) • ((m : K) * x) + (m : 𝓞 K) • ((n : K) * y) := by
      simp only [Algebra.smul_def, map_natCast]; push_cast; ring
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hy)
  zero_mem' := ⟨1, (D.q_prime k).not_dvd_one, by simp⟩
  smul_mem' := by
    rintro c x ⟨m, hm, hx⟩
    refine ⟨m, hm, ?_⟩
    have e : (m : K) * (c • x) = c • ((m : K) * x) := by
      simp only [Algebra.smul_def]; ring
    rw [e]; exact Submodule.smul_mem _ _ hx

theorem OK_le_Pinv (k : ℕ) : D.OK ≤ (D.Pinv k : Submodule (𝓞 K) K) :=
  FractionalIdeal.coe_le_coe.mpr (D.one_le_Pinv k)

theorem Pinv_le_locSub (j k : ℕ) : (D.Pinv j : Submodule (𝓞 K) K) ≤ D.locSub k := by
  intro x hx
  by_cases h : j = k
  · subst h; exact ⟨1, (D.q_prime j).not_dvd_one, by simpa using hx⟩
  · exact ⟨D.q j, D.q_not_dvd_q h, D.OK_le_Pinv k (D.q_smul_Pinv j hx)⟩

theorem BK_le_locSub (k : ℕ) : D.BK ≤ D.locSub k :=
  iSup_le fun j => D.Pinv_le_locSub j k

/-- Every element of `B_K` lies in `(P k)⁻¹` after multiplication by an integer prime to `q k`. -/
theorem exists_mul_mem_Pinv (k : ℕ) {x : K} (hx : x ∈ D.BK) :
    ∃ m : ℕ, ¬ D.q k ∣ m ∧ (m : K) * x ∈ (D.Pinv k : Submodule (𝓞 K) K) :=
  D.BK_le_locSub k hx

end AdelicToriLean.DegreeOnePrimes
