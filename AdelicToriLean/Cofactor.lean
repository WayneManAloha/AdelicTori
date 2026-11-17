import AdelicToriLean.Localization

/-!
# The cofactor ideal `I_k` and residues of degree-one primes

* `Ik D k` is the ideal with `P k * Ik k = (q k)`, i.e. `I_k = q_k (P k)⁻¹`.
* `mem_Ik_iff`: `y ∈ I_k ↔ y / q_k ∈ (P k)⁻¹`.
* `exists_int_sub_mem`: every element of `𝓞 K` is congruent to a rational integer modulo `P k`
  (`P k` has degree one).
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean.DegreeOnePrimes

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

theorem exists_cofactor (k : ℕ) :
    ∃ I : Ideal (𝓞 K), D.P k * I = Ideal.span {((D.q k : ℕ) : 𝓞 K)} := by
  have : D.P k ∣ Ideal.span {((D.q k : ℕ) : 𝓞 K)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (D.q_mem k))
  obtain ⟨I, hI⟩ := this
  exact ⟨I, hI.symm⟩

/-- The cofactor ideal: `P k * Ik k = (q k)`. -/
def Ik (k : ℕ) : Ideal (𝓞 K) := Classical.choose (D.exists_cofactor k)

theorem P_mul_Ik (k : ℕ) : D.P k * D.Ik k = Ideal.span {((D.q k : ℕ) : 𝓞 K)} :=
  Classical.choose_spec (D.exists_cofactor k)

theorem q_ne_zero_K (k : ℕ) : ((D.q k : ℕ) : K) ≠ 0 := by
  exact_mod_cast (D.q_prime k).ne_zero

/-- As fractional ideals, `I_k = q_k · (P k)⁻¹`. -/
theorem Ik_frac (k : ℕ) :
    ((D.Ik k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((D.q k : ℕ) : K) * D.Pinv k := by
  have h := congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K)) (D.P_mul_Ik k)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at h
  have hP := D.Pf_ne_zero k
  calc ((D.Ik k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = D.Pinv k * (D.Pf k * (D.Ik k : FractionalIdeal (𝓞 K)⁰ K)) := by
        rw [← mul_assoc, Pinv, inv_mul_cancel₀ hP, one_mul]
    _ = _ := by
        rw [h, mul_comm]
        congr 1

theorem mem_Ik_iff (k : ℕ) (y : 𝓞 K) :
    y ∈ D.Ik k ↔ (y : K) / ((D.q k : ℕ) : K) ∈ (D.Pinv k : Submodule (𝓞 K) K) := by
  have hiff : y ∈ D.Ik k ↔ (y : K) ∈ ((D.Ik k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_coeIdeal]
    constructor
    · intro h; exact ⟨y, h, rfl⟩
    · rintro ⟨y', hy', he⟩
      have : y' = y := (IsFractionRing.injective (𝓞 K) K) he
      rwa [← this]
  rw [hiff, D.Ik_frac k, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, he⟩
    have : (y : K) / ((D.q k : ℕ) : K) = z := by
      rw [he]; field_simp [D.q_ne_zero_K k]
    rw [this]; exact hz
  · intro h
    exact ⟨_, h, by field_simp [D.q_ne_zero_K k]⟩

theorem isMaximal (k : ℕ) : (D.P k).IsMaximal :=
  (D.isPrime k).isMaximal (D.ne_bot k)

/-- Degree one: every element of `𝓞 K` is congruent to a rational integer modulo `P k`. -/
theorem exists_int_sub_mem (k : ℕ) (t : 𝓞 K) : ∃ c : ℤ, t - (c : 𝓞 K) ∈ D.P k := by
  have := D.isMaximal k
  have : Fact (D.q k).Prime := ⟨D.q_prime k⟩
  let R := 𝓞 K ⧸ D.P k
  have hcard : Nat.card R = D.q k := by
    rw [← D.norm_eq k, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (D.q_prime k).ne_zero)
  have : CharP R (D.q k) := by
    rw [CharP.charP_iff_prime_eq_zero (D.q_prime k)]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (D.q_mem k)
  let f : ZMod (D.q k) →+* R := ZMod.castHom (dvd_refl _) R
  have hinj : Function.Injective f := f.injective
  have hbij : Function.Bijective f := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_zmod]
  obtain ⟨c, hc⟩ := hbij.2 (Ideal.Quotient.mk _ t)
  refine ⟨(c.val : ℤ), ?_⟩
  rw [← Ideal.Quotient.eq, ← hc]
  show (ZMod.castHom (dvd_refl _) R) c = Ideal.Quotient.mk _ ((c.val : ℤ) : 𝓞 K)
  rw [ZMod.castHom_apply, Int.cast_natCast, map_natCast, ZMod.natCast_val]

theorem card_quot (k : ℕ) : Nat.card (𝓞 K ⧸ D.P k) = D.q k := by
  rw [← D.norm_eq k, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end AdelicToriLean.DegreeOnePrimes
