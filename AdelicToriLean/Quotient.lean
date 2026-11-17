import AdelicToriLean.Endomorphisms

/-!
# The quotient `B_K / 𝓞 K`

* `primary_q`: if `x ∈ B_K` and `q_k^N x ∈ 𝓞 K`, then `x ∈ (P k)⁻¹`.
* `primary_other`: if `ℓ` is a prime different from every `q_k`, `x ∈ B_K` and `ℓ^N x ∈ 𝓞 K`,
  then `x ∈ 𝓞 K`.
* `card_PinvQuot`: `(P k)⁻¹ / 𝓞 K` has exactly `q_k` elements, hence is cyclic of order `q_k`.

Together: the `ℓ`-primary component of `B_K / 𝓞 K` is `(P k)⁻¹ / 𝓞 K ≅ ℤ/q_k` if `ℓ = q_k`
and trivial otherwise.
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean.DegreeOnePrimes

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

omit [NumberField K] in
theorem bezout_mem (S : Submodule (𝓞 K) K) {a b : ℕ} (hab : Nat.Coprime a b) {x : K}
    (ha : (a : K) * x ∈ S) (hb : (b : K) * x ∈ S) : x ∈ S := by
  have h : ((Nat.gcd a b : ℕ) : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := Nat.gcd_eq_gcd_ab a b
  rw [hab, Nat.cast_one] at h
  have e : x = (Nat.gcdA a b : 𝓞 K) • ((a : K) * x) + (Nat.gcdB a b : 𝓞 K) • ((b : K) * x) := by
    have hK : ((1 : ℤ) : K) = (a : K) * (Nat.gcdA a b : K) + (b : K) * (Nat.gcdB a b : K) := by
      rw [h]; push_cast; ring
    rw [Int.cast_one] at hK
    simp only [Algebra.smul_def, map_intCast]
    linear_combination x * hK
  rw [e]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)

theorem primary_q (k N : ℕ) {x : K} (hx : x ∈ D.BK) (hN : ((D.q k ^ N : ℕ) : K) * x ∈ D.OK) :
    x ∈ (D.Pinv k : Submodule (𝓞 K) K) := by
  obtain ⟨m, hm, hmx⟩ := D.exists_mul_mem_Pinv k hx
  have hcop : Nat.Coprime m (D.q k ^ N) :=
    Nat.Coprime.pow_right N (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (D.q_prime k)).mpr hm))
  exact bezout_mem _ hcop hmx (D.OK_le_Pinv k hN)

/-- Elements of `B_K` become integral after multiplication by an integer prime to `ℓ`,
for `ℓ` outside the `q_k`. -/
theorem exists_coprime_mul_mem_OK {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ∀ k, D.q k ≠ ℓ) {x : K}
    (hx : x ∈ D.BK) : ∃ e : ℕ, ¬ ℓ ∣ e ∧ (e : K) * x ∈ D.OK := by
  let S : Submodule (𝓞 K) K :=
    { carrier := {x | ∃ e : ℕ, ¬ ℓ ∣ e ∧ (e : K) * x ∈ D.OK}
      add_mem' := by
        rintro a b ⟨e, he, ha⟩ ⟨f, hf, hb⟩
        refine ⟨e * f, fun h => ((Nat.Prime.dvd_mul hℓ).mp h).elim he hf, ?_⟩
        have : ((e * f : ℕ) : K) * (a + b) = (f : 𝓞 K) • ((e : K) * a) + (e : 𝓞 K) • ((f : K) * b) := by
          simp only [Algebra.smul_def, map_natCast]; push_cast; ring
        rw [this]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)
      zero_mem' := ⟨1, hℓ.not_dvd_one, by simp⟩
      smul_mem' := by
        rintro c a ⟨e, he, ha⟩
        refine ⟨e, he, ?_⟩
        have : (e : K) * (c • a) = c • ((e : K) * a) := by simp only [Algebra.smul_def]; ring
        rw [this]; exact Submodule.smul_mem _ _ ha }
  have hBS : D.BK ≤ S := by
    refine iSup_le fun j => ?_
    intro y hy
    exact ⟨D.q j, fun h => hℓq j ((Nat.prime_dvd_prime_iff_eq hℓ (D.q_prime j)).mp h).symm,
      D.q_smul_Pinv j hy⟩
  exact hBS hx

theorem primary_other {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ∀ k, D.q k ≠ ℓ) (N : ℕ) {x : K}
    (hx : x ∈ D.BK) (hN : ((ℓ ^ N : ℕ) : K) * x ∈ D.OK) : x ∈ D.OK := by
  obtain ⟨e, he, hex⟩ := D.exists_coprime_mul_mem_OK hℓ hℓq hx
  have hcop : Nat.Coprime e (ℓ ^ N) :=
    Nat.Coprime.pow_right N (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr he))
  exact bezout_mem _ hcop hex hN

/-! ### `(P k)⁻¹ / 𝓞 K` has `q_k` elements -/

theorem Pinv_ne_one (k : ℕ) : D.Pinv k ≠ 1 := by
  intro h
  have : D.Pf k = 1 := by rw [← inv_inv (D.Pf k), ← Pinv, h, inv_one]
  have h2 : D.P k = ⊤ := by
    rw [Pf, ← FractionalIdeal.coeIdeal_top] at this
    exact FractionalIdeal.coeIdeal_injective this
  exact (D.isPrime k).ne_top h2

theorem exists_gen (k : ℕ) : ∃ u ∈ (D.Pinv k : Submodule (𝓞 K) K), u ∉ D.OK := by
  by_contra h
  push Not at h
  exact D.Pinv_ne_one k (le_antisymm (fun x hx => h x hx) (D.one_le_Pinv k))

/-- `(P k)⁻¹ = 𝓞 K + 𝓞 K u` for any `u ∈ (P k)⁻¹ ∖ 𝓞 K`. -/
theorem Pinv_eq_sup (k : ℕ) {u : K} (hu : u ∈ (D.Pinv k : Submodule (𝓞 K) K)) (hu0 : u ∉ D.OK) :
    D.Pinv k = 1 ⊔ FractionalIdeal.spanSingleton (𝓞 K)⁰ u := by
  set I : FractionalIdeal (𝓞 K)⁰ K := 1 ⊔ FractionalIdeal.spanSingleton (𝓞 K)⁰ u
  have hI1 : 1 ≤ I := le_sup_left
  have huI : u ∈ I := (le_sup_right : FractionalIdeal.spanSingleton (𝓞 K)⁰ u ≤ I)
    (FractionalIdeal.mem_spanSingleton_self _ _)
  have hIle : I ≤ D.Pinv k := sup_le (D.one_le_Pinv k)
    ((FractionalIdeal.spanSingleton_le_iff_mem).mpr hu)
  have hI0 : I ≠ 0 := fun h => by
    have := hI1; rw [h] at this
    exact (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) (le_antisymm this bot_le)
  have hJ1 : I⁻¹ ≤ 1 := by
    have := FractionalIdeal.inv_anti_mono (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) hI0 hI1
    rwa [inv_one] at this
  have hPJ : D.Pf k ≤ I⁻¹ := by
    have := FractionalIdeal.inv_anti_mono hI0 (inv_ne_zero (D.Pf_ne_zero k)) hIle
    simpa only [Pinv, inv_inv] using this
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ1
  have hPJ' : D.P k ≤ J := by
    rw [← hJ] at hPJ; exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mp hPJ
  have hJne : J ≠ ⊤ := by
    intro hJt
    rw [hJt, FractionalIdeal.coeIdeal_top] at hJ
    have : I = 1 := by rw [← inv_inv I, ← hJ, inv_one]
    exact hu0 (by have h := huI; rw [this] at h; exact h)
  have hJP : J = D.P k := ((D.isMaximal k).eq_of_le hJne hPJ').symm
  calc D.Pinv k = (D.Pf k)⁻¹ := rfl
    _ = (I⁻¹)⁻¹ := by rw [← hJ, hJP]
    _ = I := inv_inv I

theorem mem_Pinv_iff (k : ℕ) {u : K} (hu : u ∈ (D.Pinv k : Submodule (𝓞 K) K)) (hu0 : u ∉ D.OK)
    {x : K} : x ∈ (D.Pinv k : Submodule (𝓞 K) K) ↔ ∃ a b : 𝓞 K, x = (a : K) + (b : K) * u := by
  rw [D.Pinv_eq_sup k hu hu0, FractionalIdeal.coe_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := (D.mem_OK_iff).mp hy
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).mp hz
    exact ⟨a, b, by rw [Algebra.smul_def]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, D.coe_mem_OK a, _, (FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).mpr ⟨b, by
      rw [Algebra.smul_def]⟩, rfl⟩

theorem mul_gen_mem_OK_iff (k : ℕ) {u : K} (hu : u ∈ (D.Pinv k : Submodule (𝓞 K) K))
    (hu0 : u ∉ D.OK) (b : 𝓞 K) : (b : K) * u ∈ D.OK ↔ b ∈ D.P k := by
  constructor
  · intro h
    by_contra hb
    -- `P k + (b) = ⊤`
    obtain ⟨p, hp, r, hpr⟩ : ∃ p ∈ D.P k, ∃ r : 𝓞 K, p + r * b = 1 := by
      have hsup : D.P k ⊔ Ideal.span {b} = ⊤ :=
        (D.isMaximal k).1.2 _ (lt_of_le_of_ne le_sup_left (fun he => hb (he ▸
          Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))))
      have h1 : (1 : 𝓞 K) ∈ D.P k ⊔ Ideal.span {b} := hsup ▸ Submodule.mem_top
      obtain ⟨p, hp, y, hy, hpy⟩ := Submodule.mem_sup.mp h1
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨p, hp, r, hpy⟩
    have hpu : (p : K) * u ∈ D.OK := by
      have h1 := FractionalIdeal.mul_mem_mul (D.coe_mem_Pf k hp) hu
      rw [D.Pf_mul_Pinv k] at h1; exact h1
    have : u = (p : K) * u + (r : 𝓞 K) • ((b : K) * u) := by
      have hK : ((p + r * b : 𝓞 K) : K) = 1 := by rw [hpr]; simp
      simp only [Algebra.smul_def]
      calc u = ((p + r * b : 𝓞 K) : K) * u := by rw [hK, one_mul]
        _ = _ := by simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul]; ring
    exact hu0 (by rw [this]; exact Submodule.add_mem _ hpu (Submodule.smul_mem _ _ h))
  · intro hb
    have h1 := FractionalIdeal.mul_mem_mul (D.coe_mem_Pf k hb) hu
    rw [D.Pf_mul_Pinv k] at h1; exact h1

/-- The quotient `(P k)⁻¹ / 𝓞 K` as an additive group. -/
abbrev PinvQuot (k : ℕ) : Type _ :=
  (D.Pinv k : Submodule (𝓞 K) K) ⧸ (D.OK.comap (D.Pinv k : Submodule (𝓞 K) K).subtype).toAddSubgroup

/-- **`(P k)⁻¹ / 𝓞 K ≅ 𝓞 K / P k`**, a group with `q k` elements. -/
theorem card_PinvQuot (k : ℕ) : Nat.card (D.PinvQuot k) = D.q k := by
  obtain ⟨u, hu, hu0⟩ := D.exists_gen k
  let φ : 𝓞 K →+ D.PinvQuot k :=
    (QuotientAddGroup.mk' _).comp
      { toFun := fun b => ⟨(b : K) * u, by
          have : (b : K) * u = b • u := by simp [Algebra.smul_def]
          rw [this]; exact Submodule.smul_mem _ _ hu⟩
        map_zero' := by ext; simp
        map_add' := fun a b => by ext; push_cast; ring }
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, b, hab⟩ := (D.mem_Pinv_iff k hu hu0).mp hx
    refine ⟨b, ?_⟩
    show QuotientAddGroup.mk _ = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq]
    show (-((b : K) * u) + x) ∈ D.OK
    have e : -((b : K) * u) + x = (a : K) := by rw [hab]; ring
    rw [e]; exact D.coe_mem_OK a
  have hker : φ.ker = (D.P k).toAddSubgroup := by
    ext b
    rw [AddMonoidHom.mem_ker]
    show QuotientAddGroup.mk _ = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff]
    show ((b : K) * u) ∈ D.OK ↔ b ∈ D.P k
    exact D.mul_gen_mem_OK_iff k hu hu0 b
  have e := (QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)
  rw [← Nat.card_congr e.toEquiv]
  show AddSubgroup.index (D.P k).toAddSubgroup = _
  rw [← D.norm_eq k, Ideal.absNorm_apply]; rfl

theorem isAddCyclic_PinvQuot (k : ℕ) : IsAddCyclic (D.PinvQuot k) := by
  have : Fact (D.q k).Prime := ⟨D.q_prime k⟩
  exact isAddCyclic_of_prime_card (D.card_PinvQuot k)

end AdelicToriLean.DegreeOnePrimes
