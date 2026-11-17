import AdelicToriLean.Trace

/-!
# The commutator vanishes

* `natCast_not_mem`: an integer prime to `q k` is not in `P k`.
* `eq_zero_of_mem_all`: an element of `𝓞 K` lying in every `P k` is zero (the `q k` are
  pairwise distinct).
* `commutes`: if `ψ(B_K) ⊆ B_K` and `ψ(𝓞 K) ⊆ 𝓞 K`, then `ψ (t y) = t ψ y` for `t ∈ 𝓞 K`.
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean.DegreeOnePrimes

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

theorem natCast_not_mem (k : ℕ) {m : ℕ} (hm : ¬ D.q k ∣ m) : (m : 𝓞 K) ∉ D.P k := by
  intro h
  have hcop : Nat.Coprime m (D.q k) :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (D.q_prime k)).mpr hm)
  have hb : ((Nat.gcd m (D.q k) : ℕ) : ℤ) = m * Nat.gcdA m (D.q k) + D.q k * Nat.gcdB m (D.q k) :=
    Nat.gcd_eq_gcd_ab m (D.q k)
  rw [hcop, Nat.cast_one] at hb
  have h1 : (1 : 𝓞 K) ∈ D.P k := by
    have : ((1 : ℤ) : 𝓞 K) = (m : 𝓞 K) * (Nat.gcdA m (D.q k) : 𝓞 K) +
        ((D.q k : ℕ) : 𝓞 K) * (Nat.gcdB m (D.q k) : 𝓞 K) := by
      rw [hb]; push_cast; ring
    rw [Int.cast_one] at this
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h) (Ideal.mul_mem_right _ _ (D.q_mem k))
  exact (D.isPrime k).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem eq_zero_of_mem_all (o : 𝓞 K) (h : ∀ k, o ∈ D.P k) : o = 0 := by
  by_contra ho
  set N := Ideal.absNorm (Ideal.span {o})
  have hN : N ≠ 0 := by
    intro h0
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h0
    exact ho h0
  have hdvd : ∀ k, D.q k ∈ N.divisors := by
    intro k
    rw [Nat.mem_divisors]
    refine ⟨?_, hN⟩
    rw [← D.norm_eq k]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr (h k))
  have hfin : (Set.range D.q).Finite :=
    (N.divisors.finite_toSet).subset (by rintro _ ⟨k, rfl⟩; exact hdvd k)
  exact Set.infinite_range_of_injective D.q_inj hfin

variable (ψ : K →ₗ[ℚ] K)

theorem spanSingleton_mul_dual_le {f : 𝓞 K}
    (hf : ∀ b ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      IsLocalization.IsInteger (𝓞 K) (f • b)) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (f : K) * FractionalIdeal.dual ℤ ℚ 1 ≤ 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hx
  obtain ⟨r, hr⟩ := hf y hy
  refine (FractionalIdeal.mem_one_iff _).mpr ⟨r, ?_⟩
  rw [hr, Algebra.smul_def]

/-- **The commutator vanishes.** -/
theorem commutes (hB : ∀ x ∈ D.BK, ψ x ∈ D.BK) (hO : ∀ x ∈ D.OK, ψ x ∈ D.OK) (t : 𝓞 K) :
    Dt ψ t = 0 := by
  classical
  obtain ⟨f, hf0, hf⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)).isFractional
  set b := RingOfIntegers.basis K
  obtain ⟨g, hg0, hg⟩ :=
    exists_integral_multiples ℤ ℚ (Finset.univ.image (fun i => Wt ψ t (b i : K)))
  have hle := spanSingleton_mul_dual_le (K := K) hf
  have key : ∀ i, Wt ψ t (b i : K) = 0 := by
    intro i
    have hint : IsIntegral ℤ (g • Wt ψ t (b i : K)) :=
      hg _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    let w : 𝓞 K := ⟨g • Wt ψ t (b i : K), hint⟩
    have hall : ∀ k, f * w ∈ D.P k := by
      intro k
      obtain ⟨m, hm, hmy⟩ := D.uniform_defect ψ hB hO t k
      have h1 := D.dual_mem ψ t k m hmy (b i)
      have h2 : (f : K) * ((m : K) * Wt ψ t (b i : K)) ∈ (D.Pf k : Submodule (𝓞 K) K) := by
        have h3 : (f : K) * ((m : K) * Wt ψ t (b i : K)) ∈
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (f : K) *
              (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) * D.Pf k) :=
          FractionalIdeal.mem_singleton_mul.mpr ⟨_, h1, rfl⟩
        rw [← mul_assoc] at h3
        have h4 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (f : K) *
            FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) * D.Pf k ≤ D.Pf k := by
          calc _ ≤ 1 * D.Pf k := mul_le_mul_left hle _
            _ = D.Pf k := one_mul _
        exact h4 h3
      have h5 : (((m : 𝓞 K) * (f * w) : 𝓞 K) : K) ∈ (D.Pf k : Submodule (𝓞 K) K) := by
        have e : (((m : 𝓞 K) * (f * w) : 𝓞 K) : K) =
            (g : 𝓞 K) • ((f : K) * ((m : K) * Wt ψ t (b i : K))) := by
          have hwK : ((w : 𝓞 K) : K) = (g : K) * Wt ψ t (b i : K) := by
            show g • Wt ψ t (b i : K) = _; rw [zsmul_eq_mul]
          simp only [RingOfIntegers.coe_eq_algebraMap] at hwK ⊢
          rw [map_mul, map_mul, map_natCast, hwK, Algebra.smul_def, map_intCast]; ring
        rw [e]; exact Submodule.smul_mem _ _ h2
      obtain ⟨p, hp, hpe⟩ := (FractionalIdeal.mem_coeIdeal _).mp h5
      have hp' : p = (m : 𝓞 K) * (f * w) := (IsFractionRing.injective (𝓞 K) K) hpe
      rw [hp'] at hp
      exact ((D.isPrime k).mem_or_mem hp).resolve_left (D.natCast_not_mem k hm)
    have h0 := D.eq_zero_of_mem_all _ hall
    have hw : w = 0 := (mul_eq_zero.mp h0).resolve_left (nonZeroDivisors.ne_zero hf0)
    have hw' : g • Wt ψ t (b i : K) = 0 := congrArg (fun z : 𝓞 K => (z : K)) hw
    rw [zsmul_eq_mul] at hw'
    exact (mul_eq_zero.mp hw').resolve_left (by exact_mod_cast hg0)
  have hW : Wt ψ t = 0 := by
    apply (integralBasis K).ext
    intro i
    rw [integralBasis_apply]
    exact key i
  ext y
  have hsep := (traceForm_nondegenerate ℚ K).2
  apply hsep
  intro a
  rw [← Wt_spec, hW]
  simp

end AdelicToriLean.DegreeOnePrimes
