import AdelicToriLean.PadicFract
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The diagonal identity for the fractional parts of a rational number

For `r ∈ ℚ`, `{r}_p = 0` for all but finitely many primes `p`, and
`∑_p {r}_p = r (mod 1)` (`sum_fract_rat`). This is the arithmetic content of the paper's
statement that the diagonal `ℚ ⊆ 𝔸` is annihilated by the standard character.
-/

open Padic

noncomputable section

namespace AdelicToriLean

instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.prop⟩

/-- The fractional part at a prime `p : Nat.Primes`. -/
def fr (p : Nat.Primes) : ℚ_[p] →+ AddCircle (1 : ℝ) :=
  fractP p

/-- A rational with denominator a power of `p` is a `q`-adic integer for every prime `q ≠ p`. -/
theorem mem_zP_of_mem_zInvP {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) {s : ℚ}
    (hs : s ∈ zInvP p) : (s : ℚ_[q]) ∈ zP q := by
  obtain ⟨k, hk⟩ := hs
  rw [mem_zP]
  apply Padic.norm_rat_le_one
  intro hqd
  have : q ∣ p ^ k := hqd.trans hk
  have := (Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).mp (hq.out.dvd_of_dvd_pow this)
  exact hpq this.symm

/-- If `q` does not divide the denominator of `r`, then `{r}_q = 0`. -/
theorem fr_eq_zero_of_not_dvd (q : Nat.Primes) {r : ℚ} (h : ¬ (q : ℕ) ∣ r.den) :
    fr q (r : ℚ_[q]) = 0 := by
  exact fractP_eq_zero_of_norm_le q (Padic.norm_rat_le_one h)

/-- **Diagonal identity.** For `r ∈ ℚ`, the fractional parts `{r}_p` vanish for all but finitely
many `p`, and `∑ᶠ p, {r}_p = r (mod 1)`. -/
theorem sum_fract_rat (r : ℚ) :
    (Function.support fun p : Nat.Primes => fr p (r : ℚ_[p])).Finite ∧
      ∑ᶠ p : Nat.Primes, fr p (r : ℚ_[p]) = ((r : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  -- the finite set of primes dividing the denominator
  have hDfin : {p : Nat.Primes | (p : ℕ) ∣ r.den}.Finite :=
    ((Nat.divisors r.den).finite_toSet.preimage (Subtype.val_injective.injOn)).subset
      fun p hp => Nat.mem_divisors.mpr ⟨hp, r.den_ne_zero⟩
  set D : Finset Nat.Primes := hDfin.toFinset
  have hmemD : ∀ p : Nat.Primes, p ∈ D ↔ (p : ℕ) ∣ r.den := fun p => hDfin.mem_toFinset
  have hD : ∀ p : Nat.Primes, p ∉ D → fr p (r : ℚ_[p]) = 0 := by
    intro p hp
    apply fr_eq_zero_of_not_dvd
    intro hdvd
    exact hp ((hmemD p).mpr hdvd)
  have hsupp : (Function.support fun p : Nat.Primes => fr p (r : ℚ_[p])) ⊆ D := by
    intro p hp; by_contra h; exact hp (hD p h)
  refine ⟨D.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  -- representatives `s p ∈ ℤ[1/p]` with `r - s p ∈ ℤ_p`
  have hs : ∀ p : Nat.Primes, ∃ s : ℚ, s ∈ zInvP p ∧
      (-(s : ℚ_[p]) + (r : ℚ_[p])) ∈ zP p := by
    intro p
    obtain ⟨⟨s, hs⟩, hsx⟩ := toQuot_surjective p (QuotientAddGroup.mk' (zP p) (r : ℚ_[p]))
    exact ⟨s, hs, QuotientAddGroup.eq.mp hsx⟩
  choose s hsmem hsr using hs
  have hfr : ∀ p : Nat.Primes, fr p (r : ℚ_[p]) = ((s p : ℝ) : AddCircle (1 : ℝ)) := by
    intro p
    have h1 : fr p (r : ℚ_[p]) = fr p ((s p : ℚ) : ℚ_[p]) := by
      have : (r : ℚ_[p]) = (s p : ℚ_[p]) + (-(s p : ℚ_[p]) + (r : ℚ_[p])) := by ring
      rw [this, map_add]
      simp only [fr]
      rw [fractP_eq_zero_of_norm_le p (hsr p), add_zero]
    rw [h1]
    exact fractP_rat p (hsmem p)
  -- `t = r - ∑_{p ∈ D} s p` is an integer
  set t : ℚ := r - ∑ p ∈ D, s p
  have ht : ∀ q : Nat.Primes, (t : ℚ_[q]) ∈ zP q := by
    intro q
    have hother : ∀ p ∈ D, p ≠ q → ((s p : ℚ) : ℚ_[q]) ∈ zP q := fun p _ hpq => by
      exact mem_zP_of_mem_zInvP (fun h => hpq (Subtype.ext h)) (hsmem p)
    by_cases hqD : q ∈ D
    · have hsplit : (t : ℚ_[q]) = (-(s q : ℚ_[q]) + (r : ℚ_[q])) -
          ∑ p ∈ D.erase q, ((s p : ℚ) : ℚ_[q]) := by
        simp only [t, Rat.cast_sub, Rat.cast_sum]
        rw [← Finset.add_sum_erase D _ hqD]
        ring
      rw [hsplit]
      refine (zP q).sub_mem (hsr q) ((zP q).sum_mem fun p hp => ?_)
      exact hother p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
    · have hr : (r : ℚ_[q]) ∈ zP q := by
        rw [mem_zP]
        apply Padic.norm_rat_le_one
        intro hdvd
        exact hqD ((hmemD q).mpr hdvd)
      have : (t : ℚ_[q]) = (r : ℚ_[q]) - ∑ p ∈ D, ((s p : ℚ) : ℚ_[q]) := by
        simp [t]
      rw [this]
      exact (zP q).sub_mem hr ((zP q).sum_mem fun p hp =>
        hother p hp (fun h => hqD (h ▸ hp)))
  have htden : t.den = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have : Fact q.Prime := ⟨hq⟩
    exact not_dvd_den_of_norm_le q (ht ⟨q, hq⟩) hqd
  -- conclude
  rw [Finset.sum_congr rfl fun p _ => hfr p]
  have hsum : ∑ p ∈ D, ((s p : ℝ) : AddCircle (1 : ℝ)) =
      (((∑ p ∈ D, s p : ℚ) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [Rat.cast_sum]
    exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (fun p => ((s p : ℚ) : ℝ)) D).symm
  rw [hsum, show (∑ p ∈ D, s p : ℚ) = r - t by simp [t]]
  have ht' : (t : ℝ) = (t.num : ℝ) := by
    exact_mod_cast (Rat.coe_int_num_of_den_eq_one htden).symm
  rw [show ((r - t : ℚ) : ℝ) = (r : ℝ) - (t.num : ℝ) by push_cast; rw [ht']]
  have hz : (((t.num : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨t.num, by simp⟩
  rw [AddCircle.coe_sub, hz, sub_zero]

end AdelicToriLean
