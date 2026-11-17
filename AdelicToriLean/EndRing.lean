import AdelicToriLean.Kill

/-!
# `End(B_K) = 𝓞 K` and `ℚ End(B_K) = K`

* `eq_mul_of_commutes`: a `ℚ`-linear map of `K` commuting with every `t ∈ 𝓞 K` is multiplication
  by its value at `1`.
* `isIntegral_of_bounded`: if `d α^n ∈ 𝓞 K` for all `n`, then `α` is integral over `ℤ`.
* `mem_OK_of_multiplier`: if `α B_K ⊆ B_K`, then `α ∈ 𝓞 K`.
* `quasiEnd_eq_mul`: every `ℚ`-linear `φ : K → K` with `n φ(B_K) ⊆ B_K` for some `n ≠ 0`
  is multiplication by an element of `K`  (`ℚ End(B_K) = K`).
* `linearEnd_eq_mul`: every `ℚ`-linear `φ` with `φ(B_K) ⊆ B_K` is multiplication by an element
  of `𝓞 K`.
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean.DegreeOnePrimes

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

theorem exists_int_mul_mem (x : K) : ∃ n : ℤ, n ≠ 0 ∧ ∃ o : 𝓞 K, (o : K) = (n : K) * x := by
  classical
  obtain ⟨n, hn, h⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset K)
  refine ⟨n, hn, ⟨n • x, h x (Finset.mem_singleton_self x)⟩, ?_⟩
  show n • x = _
  rw [zsmul_eq_mul]

theorem eq_mul_of_commutes (ψ : K →ₗ[ℚ] K) (h : ∀ t : 𝓞 K, Dt ψ t = 0) (x : K) :
    ψ x = x * ψ 1 := by
  obtain ⟨n, hn, o, ho⟩ := exists_int_mul_mem x
  have h1 := congrArg (fun F : K →ₗ[ℚ] K => F 1) (h o)
  simp only [Dt_apply, LinearMap.zero_apply, mul_one, sub_eq_zero] at h1
  rw [ho, map_intMul ψ] at h1
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
  apply mul_left_cancel₀ hnK
  rw [h1]; ring

theorem isIntegral_of_bounded (α : K) (d : ℕ) (hd : d ≠ 0)
    (h : ∀ n : ℕ, ∃ o : 𝓞 K, (o : K) = (d : K) * α ^ n) : IsIntegral ℤ α := by
  classical
  let L : 𝓞 K →ₗ[ℤ] K := ((d : K)⁻¹ • LinearMap.id) ∘ₗ (Algebra.linearMap (𝓞 K) K).restrictScalars ℤ
  set N : Submodule ℤ K := Submodule.map L ⊤
  have hN : N.FG := (Module.Finite.fg_top).map L
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have hpow : ∀ n : ℕ, α ^ n ∈ N := by
    intro n
    obtain ⟨o, ho⟩ := h n
    refine ⟨o, Submodule.mem_top, ?_⟩
    simp only [L, LinearMap.comp_apply, LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    rw [← RingOfIntegers.coe_eq_algebraMap, ho]; field_simp
  have hle : (Algebra.adjoin ℤ {α}).toSubmodule ≤ N := by
    intro y hy
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpow i)
  exact IsIntegral.of_mem_of_fg _ (hN.of_le hle) α (Algebra.self_mem_adjoin_singleton ℤ α)

/-- Multiplication by `d = ∏_{k∈s} q_k` sends `𝓞 K + Σ_{k∈s} (P k)⁻¹` into `𝓞 K`. -/
theorem prod_mul_mem (s : Finset ℕ) {x : K}
    (hx : x ∈ D.OK ⊔ ⨆ k ∈ s, ((D.Pinv k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    ((∏ k ∈ s, D.q k : ℕ) : K) * x ∈ D.OK := by
  classical
  let T : Submodule (𝓞 K) K :=
    { carrier := {x | ((∏ k ∈ s, D.q k : ℕ) : K) * x ∈ D.OK}
      add_mem' := by
        intro a b ha hb; simp only [Set.mem_ofPred_eq, mul_add] at *; exact Submodule.add_mem _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at *
        have : ((∏ k ∈ s, D.q k : ℕ) : K) * (c • a) = c • (((∏ k ∈ s, D.q k : ℕ) : K) * a) := by
          simp only [Algebra.smul_def]; ring
        rw [this]; exact Submodule.smul_mem _ _ ha }
  have hT : D.OK ⊔ ⨆ k ∈ s, ((D.Pinv k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ T := by
    refine sup_le ?_ (iSup₂_le fun k hk => ?_)
    · intro y hy
      show _ ∈ D.OK
      obtain ⟨o, rfl⟩ := (D.mem_OK_iff).mp hy
      exact (D.mem_OK_iff).mpr ⟨((∏ k ∈ s, D.q k : ℕ) : 𝓞 K) * o, by push_cast; rfl⟩
    · intro y hy
      show _ ∈ D.OK
      have hq := D.q_smul_Pinv k hy
      obtain ⟨o, ho⟩ := (D.mem_OK_iff).mp hq
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem D.q hk
      refine (D.mem_OK_iff).mpr ⟨(c : 𝓞 K) * o, ?_⟩
      rw [hc]
      simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast] at ho ⊢
      push_cast; rw [ho]; ring
  exact hT hx

/-- Elements of `B_K` become elements of `𝓞 K + Σ_{k∈s} (P k)⁻¹` after multiplication by an
integer prime to `∏_{k∈s} q_k`. -/
theorem BK_le_coprime (s : Finset ℕ) {x : K} (hx : x ∈ D.BK) :
    ∃ e : ℕ, Nat.Coprime e (∏ k ∈ s, D.q k) ∧ (e : K) * x ∈
      D.OK ⊔ ⨆ k ∈ s, ((D.Pinv k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  classical
  set X := D.OK ⊔ ⨆ k ∈ s, ((D.Pinv k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  set d := ∏ k ∈ s, D.q k
  let S : Submodule (𝓞 K) K :=
    { carrier := {x | ∃ e : ℕ, Nat.Coprime e d ∧ (e : K) * x ∈ X}
      add_mem' := by
        rintro a b ⟨e, he, ha⟩ ⟨f, hf, hb⟩
        refine ⟨e * f, Nat.coprime_mul_iff_left.mpr ⟨he, hf⟩, ?_⟩
        have : ((e * f : ℕ) : K) * (a + b) = (f : 𝓞 K) • ((e : K) * a) + (e : 𝓞 K) • ((f : K) * b) := by
          simp only [Algebra.smul_def, map_natCast]; push_cast; ring
        rw [this]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)
      zero_mem' := ⟨1, Nat.coprime_one_left _, by simp⟩
      smul_mem' := by
        rintro c a ⟨e, he, ha⟩
        refine ⟨e, he, ?_⟩
        have : (e : K) * (c • a) = c • ((e : K) * a) := by simp only [Algebra.smul_def]; ring
        rw [this]; exact Submodule.smul_mem _ _ ha }
  have hBS : D.BK ≤ S := by
    refine iSup_le fun j => ?_
    intro y hy
    by_cases hj : j ∈ s
    · exact ⟨1, Nat.coprime_one_left _, by
        rw [Nat.cast_one, one_mul]
        exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj hy))⟩
    · refine ⟨D.q j, ?_, Submodule.mem_sup_left (D.q_smul_Pinv j hy)⟩
      refine Nat.Coprime.prod_right fun k hk => ?_
      exact (Nat.coprime_primes (D.q_prime j) (D.q_prime k)).mpr
        (fun h => hj (by rw [D.q_inj h]; exact hk))
  exact hBS hx

/-- **Multipliers of `B_K` are algebraic integers.** -/
theorem mem_OK_of_multiplier {α : K} (hα : ∀ x ∈ D.BK, α * x ∈ D.BK) : ∃ o : 𝓞 K, (o : K) = α := by
  classical
  have h1 : (1 : K) ∈ D.BK := D.OK_le_BK ((D.mem_OK_iff).mpr ⟨1, by simp⟩)
  have hpow : ∀ n : ℕ, α ^ n ∈ D.BK := by
    intro n; induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ']; exact hα _ ih
  have hαB : α ∈ D.BK := by simpa using hα 1 h1
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hαB
  set d := ∏ k ∈ s, D.q k
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => (D.q_prime k).ne_zero
  have hdα : (d : K) * α ∈ D.OK := D.prod_mul_mem s (Submodule.mem_sup_right hs)
  have hbound : ∀ n : ℕ, ∃ o : 𝓞 K, (o : K) = (d : K) * α ^ n := by
    intro n
    obtain ⟨e, he, hex⟩ := D.BK_le_coprime s (hpow n)
    obtain ⟨o1, ho1⟩ := (D.mem_OK_iff).mp (D.prod_mul_mem s hex)
    obtain ⟨o2, ho2⟩ := (D.mem_OK_iff).mp hdα
    -- `1 = a e + b d^n` in `ℤ`
    have hcop : Nat.Coprime e (d ^ n) := Nat.Coprime.pow_right n he
    have hb : ((Nat.gcd e (d ^ n) : ℕ) : ℤ) = e * Nat.gcdA e (d ^ n) + (d ^ n : ℕ) * Nat.gcdB e (d ^ n) :=
      Nat.gcd_eq_gcd_ab e (d ^ n)
    rw [hcop, Nat.cast_one] at hb
    refine ⟨(Nat.gcdA e (d ^ n) : 𝓞 K) * o1 + (Nat.gcdB e (d ^ n) : 𝓞 K) * o2 ^ n * (d : 𝓞 K), ?_⟩
    have hK : ((1 : ℤ) : K) = (e : K) * (Nat.gcdA e (d ^ n) : K) + ((d : K) ^ n) * (Nat.gcdB e (d ^ n) : K) := by
      rw [hb]; push_cast; ring
    rw [Int.cast_one] at hK
    calc _ = (Nat.gcdA e (d ^ n) : K) * (d * (e * α ^ n)) + (Nat.gcdB e (d ^ n) : K) * ((d : K) * α) ^ n * d := by
          simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul, map_intCast, map_pow, map_natCast] at ho1 ho2 ⊢
          rw [ho1, ho2]
      _ = (d : K) * α ^ n * ((e : K) * (Nat.gcdA e (d ^ n) : K) + ((d : K) ^ n) * (Nat.gcdB e (d ^ n) : K)) := by ring
      _ = _ := by rw [← hK, mul_one]
  have hint := isIntegral_of_bounded α d hd hbound
  exact ⟨⟨α, hint⟩, rfl⟩

/-- **`End(B_K) = 𝓞 K`**, for `ℚ`-linear maps of `K` preserving `B_K`. -/
theorem linearEnd_eq_mul (φ : K →ₗ[ℚ] K) (hφ : ∀ x ∈ D.BK, φ x ∈ D.BK) :
    ∃ o : 𝓞 K, ∀ x : K, φ x = (o : K) * x := by
  classical
  -- clear denominators on `𝓞 K`
  obtain ⟨n, hn, hn'⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun i => φ (RingOfIntegers.basis K i : K)))
  let ψ : K →ₗ[ℚ] K := (n : ℚ) • φ
  have hψ : ∀ x, ψ x = (n : K) * φ x := fun x => by
    simp [ψ, Rat.smul_def]
  have hψB : ∀ x ∈ D.BK, ψ x ∈ D.BK := fun x hx => by
    rw [hψ]
    have : (n : K) * φ x = ((n : 𝓞 K)) • φ x := by simp [Algebra.smul_def]
    rw [this]; exact Submodule.smul_mem _ _ (hφ x hx)
  have hψO : ∀ x ∈ D.OK, ψ x ∈ D.OK := by
    intro x hx
    obtain ⟨o, rfl⟩ := (D.mem_OK_iff).mp hx
    clear hx
    have ho : o ∈ Submodule.span ℤ (Set.range (RingOfIntegers.basis K)) := by
      rw [(RingOfIntegers.basis K).span_eq]; exact Submodule.mem_top
    induction ho using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      have hint := hn' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      refine (D.mem_OK_iff).mpr ⟨⟨_, hint⟩, ?_⟩
      show n • φ _ = ψ _
      rw [hψ, zsmul_eq_mul]
    | zero => simp
    | add a b _ _ ha hb =>
      have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by push_cast; rfl
      rw [this, map_add]; exact Submodule.add_mem _ ha hb
    | smul z a _ ha =>
      have : ((z • a : 𝓞 K) : K) = (z : ℚ) • (a : K) := by
        rw [Rat.smul_def, zsmul_eq_mul]; push_cast; rfl
      rw [this, map_smul]
      have : (z : ℚ) • ψ (a : K) = ((z : 𝓞 K)) • ψ (a : K) := by
        rw [Rat.smul_def, Algebra.smul_def]; simp
      rw [this]; exact Submodule.smul_mem _ _ ha
  have hcomm : ∀ t : 𝓞 K, Dt ψ t = 0 := D.commutes ψ hψB hψO
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
  have hφmul : ∀ x, φ x = x * φ 1 := by
    intro x
    have := eq_mul_of_commutes ψ hcomm x
    rw [hψ, hψ] at this
    apply mul_left_cancel₀ hnK
    rw [this]; ring
  have hmult : ∀ x ∈ D.BK, φ 1 * x ∈ D.BK := fun x hx => by
    rw [mul_comm, ← hφmul]; exact hφ x hx
  obtain ⟨o, ho⟩ := D.mem_OK_of_multiplier hmult
  exact ⟨o, fun x => by rw [hφmul, ho, mul_comm]⟩

/-- **`ℚ End(B_K) = K`**: every quasi-endomorphism is multiplication by an element of `K`. -/
theorem quasiEnd_eq_mul (φ : K →ₗ[ℚ] K) (n : ℕ) (hn : n ≠ 0)
    (hφ : ∀ x ∈ D.BK, (n : K) * φ x ∈ D.BK) : ∃ α : K, ∀ x : K, φ x = α * x := by
  let ψ : K →ₗ[ℚ] K := (n : ℚ) • φ
  have hψ : ∀ x, ψ x = (n : K) * φ x := fun x => by simp [ψ, Rat.smul_def]
  obtain ⟨o, ho⟩ := D.linearEnd_eq_mul ψ (fun x hx => by rw [hψ]; exact hφ x hx)
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
  refine ⟨(o : K) / n, fun x => ?_⟩
  have := ho x
  rw [hψ] at this
  field_simp
  rw [mul_comm]; exact this

end AdelicToriLean.DegreeOnePrimes
