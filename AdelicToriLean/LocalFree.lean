import AdelicToriLean.Quotient

/-!
# Local freeness and `t(ℤ)`-homogeneity

* `sandwich_free`: a `ℤ`-submodule `L` of `K` with `𝓞 K ≤ L` and `c L ⊆ 𝓞 K` (`c ≠ 0`) is free
  of rank `[K : ℚ]`.
* `locallyFree`: for every prime `ℓ` there is a free `ℤ`-submodule `L ≤ B_K` of rank `[K : ℚ]`
  such that every `x ∈ B_K` has `e x ∈ L` for some integer `e` prime to `ℓ`
  (i.e. `(B_K)_(ℓ) ≅ ℤ_(ℓ)^n`).
* `freeOfFiniteQuot`: if `𝓞 K ≤ B ≤ K` and `B / 𝓞 K` is finite, then `B` is free of rank `n`
  (so every group of integers without free summands has `B / 𝓞 K` infinite).
* `homogeneous`: for `[K : ℚ] ≥ 2`, every nonzero `x ∈ B_K` is divisible in `B_K` by only finitely
  many primes, and by only finitely many powers of each prime (type `t(ℤ)`).
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean.DegreeOnePrimes

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

/-- `𝓞 K` as a `ℤ`-submodule of `K`. -/
abbrev OZ : Submodule ℤ K := D.OK.restrictScalars ℤ

theorem sandwich_free (L : Submodule ℤ K) (h1 : D.OZ ≤ L) (c : ℕ) (hc : c ≠ 0)
    (h2 : ∀ x ∈ L, (c : K) * x ∈ D.OK) :
    Module.Free ℤ L ∧ Module.Finite ℤ L ∧ Module.finrank ℤ L = Module.finrank ℚ K := by
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
  -- the injective map `L → 𝓞 K`, `x ↦ c x`
  let g : L →ₗ[ℤ] 𝓞 K :=
    { toFun := fun x => ⟨(c : K) * x, by
        obtain ⟨o, ho⟩ := (D.mem_OK_iff).mp (h2 x x.2)
        rw [← ho]; exact o.2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show (c : K) * ((x : K) + (y : K)) = (c : K) * x + (c : K) * y
        ring
      map_smul' := fun z x => by
        apply Subtype.ext
        show (c : K) * (z • (x : K)) = z • ((c : K) * x)
        simp only [zsmul_eq_mul]; ring }
  have hg : Function.Injective g := by
    intro x y hxy
    have : (c : K) * x = (c : K) * y := congrArg (fun z : 𝓞 K => (z : K)) hxy
    exact Subtype.ext (mul_left_cancel₀ hcK this)
  have hfin : Module.Finite ℤ L := Module.Finite.of_injective g hg
  have hfree : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  refine ⟨hfree, hfin, le_antisymm ?_ ?_⟩
  · rw [← RingOfIntegers.rank]
    exact LinearMap.finrank_le_finrank_of_injective hg
  · rw [← RingOfIntegers.rank]
    let f : 𝓞 K →ₗ[ℤ] L :=
      { toFun := fun o => ⟨(o : K), h1 (D.coe_mem_OK o)⟩
        map_add' := fun a b => by ext; simp
        map_smul' := fun n a => by ext; simp }
    refine LinearMap.finrank_le_finrank_of_injective (f := f) (fun a b hab => ?_)
    have h := congrArg (fun z : L => (z : K)) hab
    exact (IsFractionRing.injective (𝓞 K) K) h

/-- **Local freeness**: `(B_K)_(ℓ)` is free of rank `[K : ℚ]` for every prime `ℓ`. -/
theorem locallyFree (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ L : Submodule ℤ K, L ≤ D.BK.restrictScalars ℤ ∧ Module.Free ℤ L ∧ Module.Finite ℤ L ∧
      Module.finrank ℤ L = Module.finrank ℚ K ∧
      ∀ x ∈ D.BK, ∃ e : ℕ, ¬ ℓ ∣ e ∧ (e : K) * x ∈ L := by
  by_cases h : ∃ k, D.q k = ℓ
  · obtain ⟨k, rfl⟩ := h
    let L : Submodule ℤ K := (D.Pinv k : Submodule (𝓞 K) K).restrictScalars ℤ
    obtain ⟨hfree, hfin, hrank⟩ := D.sandwich_free L (fun x hx => D.OK_le_Pinv k hx) (D.q k)
      (D.q_prime k).ne_zero (fun x hx => D.q_smul_Pinv k hx)
    exact ⟨L, fun x hx => D.Pinv_le_BK k hx, hfree, hfin, hrank, fun x hx =>
      D.exists_mul_mem_Pinv k hx⟩
  · push Not at h
    obtain ⟨hfree, hfin, hrank⟩ := D.sandwich_free D.OZ le_rfl 1 one_ne_zero
      (fun x hx => by simpa using hx)
    exact ⟨D.OZ, fun x hx => D.OK_le_BK hx, hfree, hfin, hrank, fun x hx =>
      D.exists_coprime_mul_mem_OK hℓ h hx⟩

/-- A group `𝓞 K ≤ B ≤ K` with `B / 𝓞 K` finite is free of rank `[K : ℚ]`. -/
theorem freeOfFiniteQuot (B : Submodule ℤ K) (hOB : D.OZ ≤ B)
    [Finite (B ⧸ (D.OZ.comap B.subtype))] :
    Module.Free ℤ B ∧ Module.Finite ℤ B ∧ Module.finrank ℤ B = Module.finrank ℚ K := by
  set c := Nat.card (B ⧸ (D.OZ.comap B.subtype))
  have hc : c ≠ 0 := Nat.card_pos.ne'
  refine D.sandwich_free B hOB c hc (fun x hx => ?_)
  have h := card_nsmul_eq_zero' (G := B ⧸ (D.OZ.comap B.subtype)) (x := Submodule.Quotient.mk ⟨x, hx⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  have : ((c • (⟨x, hx⟩ : B) : B) : K) = (c : K) * x := by simp [nsmul_eq_mul]
  rw [← this]; exact h

/-! ### Homogeneity -/

local notation "n" => Module.finrank ℚ K

theorem absNorm_natCast (c : ℕ) : Ideal.absNorm (Ideal.span {(c : 𝓞 K)}) = c ^ n := by
  rw [Ideal.absNorm_span_singleton, ← RingOfIntegers.rank]
  have : (c : 𝓞 K) = algebraMap ℤ (𝓞 K) (c : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap]
  simp [Int.natAbs_pow]

theorem absNorm_span_mul (c : ℕ) (w : 𝓞 K) :
    Ideal.absNorm (Ideal.span {(c : 𝓞 K) * w}) = c ^ n * Ideal.absNorm (Ideal.span {w}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul, absNorm_natCast]

theorem absNorm_Ik (k : ℕ) : Ideal.absNorm (D.Ik k) = D.q k ^ (n - 1) := by
  have h := congrArg Ideal.absNorm (D.P_mul_Ik k)
  rw [map_mul, D.norm_eq k, absNorm_natCast] at h
  have hn : 1 ≤ n := Module.finrank_pos
  have hq := (D.q_prime k).pos
  have : D.q k ^ n = D.q k * D.q k ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [this] at h
  exact Nat.eq_of_mul_eq_mul_left hq h

theorem exp_le (N m : ℕ) (hN : 1 ≤ N) (hm : 2 ≤ m) : N ≤ (N - 1) * m + (m - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + 1 := ⟨N - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 2 := ⟨m - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : b + 2 - 1 = b + 1 := by omega
  rw [this]; nlinarith

theorem coprime_pow_dvd {ℓ e a A : ℕ} (hℓ : ℓ.Prime) (he : ¬ ℓ ∣ e) (h : ℓ ^ a ∣ e ^ n * A) :
    ℓ ^ a ∣ A := by
  have hcop : Nat.Coprime (ℓ ^ a) (e ^ n) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr he)
  exact hcop.dvd_of_dvd_mul_left h

/-- If `x = ℓ^N y` with `y ∈ B_K` and `[K : ℚ] ≥ 2`, then `ℓ^N` divides the norm of `d x`. -/
theorem pow_dvd_norm (hn : 2 ≤ n) {x : K} (d : ℤ) (o : 𝓞 K) (ho : (o : K) = (d : K) * x)
    {ℓ N : ℕ} (hℓ : ℓ.Prime) (hN : 1 ≤ N) {y : K} (hy : y ∈ D.BK) (hxy : x = ((ℓ ^ N : ℕ) : K) * y) :
    ℓ ^ N ∣ Ideal.absNorm (Ideal.span {o}) := by
  by_cases hq : ∃ k, D.q k = ℓ
  · obtain ⟨k, rfl⟩ := hq
    obtain ⟨m, hm, hmy⟩ := D.exists_mul_mem_Pinv k hy
    have hdmy : (d : K) * ((m : K) * y) ∈ (D.Pinv k : Submodule (𝓞 K) K) := by
      have : (d : K) * ((m : K) * y) = (d : 𝓞 K) • ((m : K) * y) := by simp [Algebra.smul_def]
      rw [this]; exact Submodule.smul_mem _ _ hmy
    obtain ⟨w, hw⟩ := (D.mem_OK_iff).mp (D.q_smul_Pinv k hdmy)
    have hwI : w ∈ D.Ik k := by
      rw [D.mem_Ik_iff, hw]
      have : ((D.q k : ℕ) : K) * ((d : K) * ((m : K) * y)) / ((D.q k : ℕ) : K) =
          (d : K) * ((m : K) * y) := by field_simp [D.q_ne_zero_K k]
      rw [this]; exact hdmy
    have hmo : (m : 𝓞 K) * o = ((D.q k ^ (N - 1) : ℕ) : 𝓞 K) * w := by
      apply IsFractionRing.injective (𝓞 K) K
      simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast] at ho hw ⊢
      rw [ho, hw, hxy]
      have : D.q k ^ N = D.q k * D.q k ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]; push_cast; ring
    have hmem : (m : 𝓞 K) * o ∈ Ideal.span {((D.q k ^ (N - 1) : ℕ) : 𝓞 K)} * D.Ik k := by
      rw [hmo]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hwI
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le
      ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    rw [map_mul, absNorm_natCast, D.absNorm_Ik, absNorm_span_mul, ← pow_mul, ← pow_add] at hdvd
    have h1 := coprime_pow_dvd (D.q_prime k) hm hdvd
    exact dvd_trans (pow_dvd_pow _ (exp_le N n hN hn)) h1
  · push Not at hq
    obtain ⟨e, he, hey⟩ := D.exists_coprime_mul_mem_OK hℓ hq hy
    obtain ⟨w, hw⟩ := (D.mem_OK_iff).mp hey
    have heo : (e : 𝓞 K) * o = ((ℓ ^ N : ℕ) : 𝓞 K) * ((d : 𝓞 K) * w) := by
      apply IsFractionRing.injective (𝓞 K) K
      simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast, map_intCast] at ho hw ⊢
      rw [ho, hw, hxy]; push_cast; ring
    have hmem : (e : 𝓞 K) * o ∈ Ideal.span {((ℓ ^ N : ℕ) : 𝓞 K)} := by
      rw [heo]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
    rw [absNorm_natCast, absNorm_span_mul, ← pow_mul] at hdvd
    have h1 := coprime_pow_dvd hℓ he hdvd
    have hn1 : N ≤ N * n := Nat.le_mul_of_pos_right N (by omega)
    exact dvd_trans (pow_dvd_pow _ hn1) h1

/-- **`t(ℤ)`-homogeneity** (`[K : ℚ] ≥ 2`): every nonzero `x ∈ B_K` is divisible in `B_K` by only
finitely many primes, and by only finitely many powers of each prime. -/
theorem homogeneous (hn : 2 ≤ n) {x : K} (hx0 : x ≠ 0) :
    {ℓ : ℕ | ℓ.Prime ∧ ∃ y ∈ D.BK, x = (ℓ : K) * y}.Finite ∧
      ∀ ℓ : ℕ, ℓ.Prime → ∃ N : ℕ, ¬ ∃ y ∈ D.BK, x = ((ℓ ^ N : ℕ) : K) * y := by
  obtain ⟨d, hd, o', ho'⟩ := exists_int_mul_mem x
  have hA : Ideal.absNorm (Ideal.span {o'}) ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    have : (d : K) * x = 0 := by rw [← ho', h]; simp
    exact (mul_ne_zero (by exact_mod_cast hd) hx0) this
  refine ⟨?_, fun ℓ hℓ => ⟨Ideal.absNorm (Ideal.span {o'}), ?_⟩⟩
  · refine (Nat.divisors (Ideal.absNorm (Ideal.span {o'}))).finite_toSet.subset ?_
    rintro ℓ ⟨hℓ, y, hy, hxy⟩
    rw [Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, hA⟩
    have := D.pow_dvd_norm hn d o' ho' hℓ le_rfl hy (by rw [hxy]; simp)
    simpa using this
  · rintro ⟨y, hy, hxy⟩
    have hN : 1 ≤ Ideal.absNorm (Ideal.span {o'}) := Nat.one_le_iff_ne_zero.mpr hA
    have h := D.pow_dvd_norm hn d o' ho' hℓ hN hy hxy
    have hlt : Ideal.absNorm (Ideal.span {o'}) < ℓ ^ Ideal.absNorm (Ideal.span {o'}) :=
      Nat.lt_pow_self hℓ.one_lt
    exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

end AdelicToriLean.DegreeOnePrimes
