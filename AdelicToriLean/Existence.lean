import AdelicToriLean.Basic
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Localization.Integral

/-!
# Existence of the input `DegreeOnePrimes K`

Every number field has infinitely many degree-one primes over pairwise distinct rational primes.

* `schur`: a nonconstant integer polynomial has infinitely many prime divisors of its values.
* `exponent_ne_zero`: for an integral primitive element `θ`, some nonzero integer lies in the
  conductor of `ℤ[θ]` in `𝓞 K`.
* `exists_degreeOnePrimes`: `Nonempty (DegreeOnePrimes K)`.

For `p` prime to the conductor with `p ∣ f(n)` (`f = minpoly ℤ θ`), Mathlib's Kummer–Dedekind
isomorphism `𝓞 K / p ≅ 𝔽_p[X]/(f̄)` composed with evaluation at `n` is a surjective ring map
`𝓞 K → 𝔽_p`; its kernel has absolute norm `p`.
-/

open NumberField Polynomial IntermediateField

noncomputable section

namespace AdelicToriLean

/-- **Schur.** A nonconstant integer polynomial has infinitely many prime divisors of its values. -/
theorem schur (f : ℤ[X]) (hf : 0 < f.natDegree) :
    {p : ℕ | p.Prime ∧ ∃ n : ℤ, (p : ℤ) ∣ f.eval n}.Infinite := by
  intro hfin
  set S := hfin.toFinset
  set c := f.eval 0
  have hmemS : ∀ p : ℕ, p.Prime → (∃ n : ℤ, (p : ℤ) ∣ f.eval n) → p ∈ S := fun p hp hn =>
    hfin.mem_toFinset.mpr ⟨hp, hn⟩
  by_cases hc : c = 0
  · obtain ⟨p, hpS, hp⟩ : ∃ p, p ∉ S ∧ p.Prime := by
      obtain ⟨p, hge, hp⟩ := Nat.exists_infinite_primes (S.sup id + 1)
      refine ⟨p, fun h => ?_, hp⟩
      have := Finset.le_sup (f := id) h
      simp only [id] at this
      omega
    refine hpS (hmemS p hp ⟨p, ?_⟩)
    have h := Polynomial.sub_dvd_eval_sub (p : ℤ) 0 f
    have h0 : f.eval 0 = 0 := hc
    rwa [h0, sub_zero, sub_zero] at h
  · set N : ℤ := ∏ p ∈ S, (p : ℤ)
    have hN : N ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      have := (hfin.mem_toFinset.mp hp).1.ne_zero
      exact_mod_cast this
    have h1 : f - C c ≠ 0 := by
      intro h
      have : f = C c := sub_eq_zero.mp h
      rw [this, natDegree_C] at hf
      exact lt_irrefl 0 hf
    have h2 : f + C c ≠ 0 := by
      intro h
      have : f = C (-c) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h
      rw [this, natDegree_C] at hf
      exact lt_irrefl 0 hf
    set R := (f - C c) * (f + C c)
    have hR : R ≠ 0 := mul_ne_zero h1 h2
    have hbad : {k : ℕ | R.IsRoot (c * N * k)}.Finite := by
      refine ((R.roots.toFinset.finite_toSet.preimage (f := fun k : ℕ => c * N * k) ?_)).subset ?_
      · intro a _ b _ hab
        have hcN : c * N ≠ 0 := mul_ne_zero hc hN
        have := mul_left_cancel₀ hcN hab
        exact_mod_cast this
      · intro k hk
        simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
        exact (mem_roots hR).mpr hk
    obtain ⟨k, hk⟩ := hbad.exists_notMem
    simp only [Set.mem_ofPred_eq] at hk
    set v := f.eval (c * N * k)
    obtain ⟨t, ht⟩ : c * N * k ∣ v - c := by
      have := Polynomial.sub_dvd_eval_sub (c * N * k) 0 f
      simpa using this
    set u := 1 + N * k * t
    have hv : v = c * u := by
      have : v = c + c * N * k * t := by linear_combination ht
      rw [this]; ring
    have hu : u.natAbs ≠ 1 := by
      intro h
      rcases Int.natAbs_eq_iff.mp h with h | h
      · apply hk
        simp only [IsRoot, R, eval_mul, eval_sub, eval_add, eval_C]
        rw [show f.eval (c * N * k) = v from rfl, hv, h]; ring
      · apply hk
        simp only [IsRoot, R, eval_mul, eval_sub, eval_add, eval_C]
        rw [show f.eval (c * N * k) = v from rfl, hv, h]; push_cast; ring
    obtain ⟨q, hq, hqu⟩ := Nat.exists_prime_and_dvd hu
    have hqu' : (q : ℤ) ∣ u := Int.natCast_dvd.mpr hqu
    have hqS : q ∈ S := hmemS q hq ⟨c * N * k, by rw [show f.eval _ = v from rfl, hv]
                                                  exact dvd_mul_of_dvd_right hqu' c⟩
    have hqN : (q : ℤ) ∣ N := Finset.dvd_prod_of_mem _ hqS
    have : (q : ℤ) ∣ 1 := by
      have h3 : (q : ℤ) ∣ N * k * t := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hqN _) _
      have := (Int.dvd_add_right h3).mp (by rw [add_comm]; exact hqu')
      exact this
    have := Int.eq_one_of_dvd_one (by positivity) this
    exact hq.one_lt.ne' (by exact_mod_cast this)

variable {K : Type*} [Field K] [NumberField K]

/-- An integral primitive element. -/
theorem exists_integral_primitive : ∃ b : 𝓞 K, ℚ⟮(b : K)⟯ = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  have hyα : IsIntegral ℤ (y • α) := hint α (Finset.mem_singleton_self α)
  refine ⟨⟨y • α, hyα⟩, eq_top_iff.mpr ?_⟩
  rw [← hα, IntermediateField.adjoin_simple_le_iff]
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hmem : y • α ∈ ℚ⟮y • α⟯ := IntermediateField.mem_adjoin_simple_self ℚ _
  have : α = algebraMap ℚ K ((y : ℚ)⁻¹) * (y • α) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, Algebra.smul_def, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hy', map_one, one_mul]
  have key : algebraMap ℚ K ((y : ℚ)⁻¹) * (y • α) ∈ ℚ⟮y • α⟯ :=
    mul_mem (IntermediateField.algebraMap_mem _ _) hmem
  rw [← this] at key
  exact key

/-- Every element of `K` is, up to a nonzero integer, an element of `ℤ[θ]`. -/
theorem exists_int_mul_mem_adjoin {θ : 𝓞 K} (hθ : ℚ⟮(θ : K)⟯ = ⊤) (x : K) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ z ∈ Algebra.adjoin ℤ {θ}, (m : K) * x = (z : K) := by
  have hint : IsIntegral ℚ (θ : K) := Algebra.IsIntegral.isIntegral _
  have hx : x ∈ Algebra.adjoin ℚ {(θ : K)} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨1, one_ne_zero, θ, Algebra.subset_adjoin rfl, by simp [hy]⟩
  | algebraMap r =>
    refine ⟨r.den, by exact_mod_cast r.den_nz, (r.num : 𝓞 K), Subalgebra.intCast_mem _ _, ?_⟩
    have : (r.den : K) * algebraMap ℚ K r = r.num := by
      rw [show (r.den : K) = algebraMap ℚ K r.den by simp, ← map_mul, Rat.den_mul_eq_num]
      simp
    push_cast; exact_mod_cast this
  | add a b _ _ ha hb =>
    obtain ⟨m₁, hm₁, z₁, hz₁, e₁⟩ := ha
    obtain ⟨m₂, hm₂, z₂, hz₂, e₂⟩ := hb
    refine ⟨m₁ * m₂, mul_ne_zero hm₁ hm₂, (m₂ : 𝓞 K) * z₁ + (m₁ : 𝓞 K) * z₂,
      add_mem (mul_mem (Subalgebra.intCast_mem _ _) hz₁) (mul_mem (Subalgebra.intCast_mem _ _) hz₂),
      ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast] at e₁ e₂ ⊢
    push_cast
    linear_combination (m₂ : K) * e₁ + (m₁ : K) * e₂
  | mul a b _ _ ha hb =>
    obtain ⟨m₁, hm₁, z₁, hz₁, e₁⟩ := ha
    obtain ⟨m₂, hm₂, z₂, hz₂, e₂⟩ := hb
    refine ⟨m₁ * m₂, mul_ne_zero hm₁ hm₂, z₁ * z₂, mul_mem hz₁ hz₂, ?_⟩
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e₁ e₂ ⊢
    push_cast
    linear_combination ((m₂ : K) * b) * e₁ + (algebraMap (𝓞 K) K z₁) * e₂

/-- For an integral primitive element, the conductor of `ℤ[θ]` contains a nonzero integer. -/
theorem exponent_ne_zero {θ : 𝓞 K} (hθ : ℚ⟮(θ : K)⟯ = ⊤) : RingOfIntegers.exponent θ ≠ 0 := by
  classical
  let b := RingOfIntegers.basis K
  have hm : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ (m : 𝓞 K) * b i ∈ Algebra.adjoin ℤ {θ} := fun i => by
    obtain ⟨m, hm, z, hz, e⟩ := exists_int_mul_mem_adjoin hθ (b i : K)
    refine ⟨m, hm, ?_⟩
    have : (m : 𝓞 K) * b i = z := by
      apply RingOfIntegers.coe_injective
      push_cast; exact e
    rw [this]; exact hz
  choose m hm0 hmem using hm
  set d : ℤ := ∏ i, m i
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hm0 i
  have hcond : (d : 𝓞 K) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro x
    rw [← b.sum_repr x, Finset.mul_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    have : (d : 𝓞 K) * (b.repr x i • b i) =
        ((∏ j ∈ Finset.univ.erase i, m j) * b.repr x i : ℤ) * ((m i : 𝓞 K) * b i) := by
      rw [zsmul_eq_mul, show d = m i * ∏ j ∈ Finset.univ.erase i, m j from
        (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm]
      push_cast; ring
    rw [this]
    exact mul_mem (Subalgebra.intCast_mem _ _) (hmem i)
  intro h0
  rw [RingOfIntegers.exponent, Ideal.absNorm_eq_zero_iff] at h0
  have : (d : ℤ) ∈ Ideal.under ℤ (conductor ℤ θ) := by
    rw [Ideal.under_def, Ideal.mem_comap]; simpa using hcond
  rw [h0, Ideal.mem_bot] at this
  exact hd this

/-- A surjective ring map `𝓞 K → 𝔽_p` from a root of `minpoly ℤ θ` modulo `p`, for `p` prime to
the conductor. -/
theorem exists_surj_zmod {θ : 𝓞 K} {p : ℕ} [hp : Fact p.Prime]
    (hpe : ¬ p ∣ RingOfIntegers.exponent θ) {n : ℤ} (hn : (p : ℤ) ∣ (minpoly ℤ θ).eval n) :
    ∃ ψ : 𝓞 K →+* ZMod p, Function.Surjective ψ := by
  let Φ := RingOfIntegers.ZModXQuotSpanEquivQuotSpan (K := K) (θ := θ) (p := p) hpe
  have hroot : eval (n : ZMod p) (map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)) = 0 := by
    rw [eval_intCast_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hn
  let ev : (ZMod p)[X] ⧸ Ideal.span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} →+* ZMod p :=
    Ideal.Quotient.lift _ (evalRingHom (n : ZMod p)) (fun a ha => by
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hroot])
  exact ⟨ev.comp (Φ.symm.toRingHom.comp (Ideal.Quotient.mk _)), ZMod.ringHom_surjective _⟩

/-- **Existence of the external input.** Every number field has infinitely many degree-one primes
lying over pairwise distinct rational primes. -/
theorem exists_degreeOnePrimes : Nonempty (DegreeOnePrimes K) := by
  classical
  obtain ⟨θ, hθ⟩ := exists_integral_primitive (K := K)
  have hdeg : 0 < (minpoly ℤ θ).natDegree := minpoly.natDegree_pos θ.isIntegral
  set T := {p : ℕ | p.Prime ∧ ∃ n : ℤ, (p : ℤ) ∣ (minpoly ℤ θ).eval n} \
    {p : ℕ | p ∣ RingOfIntegers.exponent θ}
  have hfinE : {p : ℕ | p ∣ RingOfIntegers.exponent θ}.Finite :=
    (Nat.divisors (RingOfIntegers.exponent θ)).finite_toSet.subset fun p hp =>
      Nat.mem_divisors.mpr ⟨hp, exponent_ne_zero hθ⟩
  have hT : T.Infinite := (schur _ hdeg).sdiff hfinE
  let e := hT.natEmbedding
  have he : ∀ k, (e k : ℕ) ∈ T := fun k => (e k).2
  have hprime : ∀ k, (e k : ℕ).Prime := fun k => (he k).1.1
  have hψ : ∀ k, ∃ ψ : 𝓞 K →+* ZMod (e k : ℕ), Function.Surjective ψ := fun k => by
    have : Fact (e k : ℕ).Prime := ⟨hprime k⟩
    obtain ⟨n, hn⟩ := (he k).1.2
    exact exists_surj_zmod (he k).2 hn
  choose ψ hψs using hψ
  refine ⟨{ q := fun k => (e k : ℕ), P := fun k => RingHom.ker (ψ k), q_prime := hprime,
            q_inj := fun a b h => e.injective (Subtype.ext h), norm_eq := fun k => ?_ }⟩
  have : NeZero (e k : ℕ) := ⟨(hprime k).ne_zero⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (hψs k)).toEquiv, Nat.card_zmod]

end AdelicToriLean
