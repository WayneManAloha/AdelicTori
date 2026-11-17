import AdelicToriLean.Cofactor

/-!
# Every quasi-endomorphism of `B_K` preserving `𝓞 K` commutes with `𝓞 K`

Let `ψ : K →ₗ[ℚ] K` with `ψ(B_K) ⊆ B_K` and `ψ(𝓞 K) ⊆ 𝓞 K`. For `t ∈ 𝓞 K` put
`Dt = ψ ∘ (t ·) - (t ·) ∘ ψ`. Then `Dt = 0` (`commutes`).

Proof (trace duality; no Galois closure):
1. For `y ∈ I_k = q_k (P k)⁻¹`, some `m` prime to `q_k` has `m ψ(y) ∈ I_k` (`local_mul`).
2. With `t ≡ c (mod P k)`, `c ∈ ℤ`, `m Dt(y) ∈ q_k 𝓞 K` for `y ∈ I_k` (`defect`), uniformly in `y`
   for one `m` (`uniform_defect`, since `I_k` is finitely generated over `ℤ`).
3. Transposing `Dt` through the trace form gives `W`, with `m W(a) ∈ dual(1) · P k` for `a ∈ 𝓞 K`
   (`dual_mem`). Clearing denominators by a factor independent of `k`, `W(a)` times a fixed nonzero
   element lies in every `P k`, hence is zero.
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean.DegreeOnePrimes

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

/-- `I_k` as a submodule of `K`. -/
abbrev Jk (k : ℕ) : Submodule (𝓞 K) K := ((D.Ik k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

theorem mem_OK_iff {x : K} : x ∈ D.OK ↔ ∃ o : 𝓞 K, (o : K) = x := by
  rw [OK, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]

theorem coe_mem_OK (o : 𝓞 K) : (o : K) ∈ D.OK := (D.mem_OK_iff).mpr ⟨o, rfl⟩

theorem Ik_ne_zero (k : ℕ) : ((D.Ik k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [D.Ik_frac k]
  exact mul_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (D.q_ne_zero_K k))
    (inv_ne_zero (D.Pf_ne_zero k))

/-- `P k · I_k = (q k)` as fractional ideals. -/
theorem Pf_mul_Ik (k : ℕ) : D.Pf k * ((D.Ik k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ ((D.q k : ℕ) : K) := by
  rw [D.Ik_frac k, mul_left_comm, D.Pf_mul_Pinv k, mul_one]

/-- An element of `P k · I_k` is `q k` times an element of `𝓞 K`. -/
theorem mul_mem_Pf_Ik (k : ℕ) {x y : K} (hx : x ∈ (D.Pf k : Submodule (𝓞 K) K)) (hy : y ∈ D.Jk k) :
    ∃ o : 𝓞 K, x * y = ((D.q k : ℕ) : K) * o := by
  have h := FractionalIdeal.mul_mem_mul hx hy
  rw [D.Pf_mul_Ik k, FractionalIdeal.mem_spanSingleton] at h
  obtain ⟨o, ho⟩ := h
  exact ⟨o, by rw [← ho, Algebra.smul_def, mul_comm]⟩

theorem coe_mem_Pf (k : ℕ) {p : 𝓞 K} (hp : p ∈ D.P k) : (p : K) ∈ (D.Pf k : Submodule (𝓞 K) K) :=
  (FractionalIdeal.mem_coeIdeal _).mpr ⟨p, hp, rfl⟩

theorem coe_mem_Jk (k : ℕ) {p : 𝓞 K} (hp : p ∈ D.Ik k) : (p : K) ∈ D.Jk k :=
  (FractionalIdeal.mem_coeIdeal _).mpr ⟨p, hp, rfl⟩

variable (ψ : K →ₗ[ℚ] K)

theorem map_natMul (n : ℕ) (x : K) : ψ ((n : K) * x) = (n : K) * ψ x := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

theorem map_intMul (n : ℤ) (x : K) : ψ ((n : K) * x) = (n : K) * ψ x := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

/-- Step 1. -/
theorem local_mul (hB : ∀ x ∈ D.BK, ψ x ∈ D.BK) (k : ℕ) {y : K} (hy : y ∈ D.Jk k) :
    ∃ m : ℕ, ¬ D.q k ∣ m ∧ (m : K) * ψ y ∈ D.Jk k := by
  have hy' : y ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ ((D.q k : ℕ) : K) * D.Pinv k := by
    rw [← D.Ik_frac k]; exact hy
  obtain ⟨z, hz, rfl⟩ := FractionalIdeal.mem_singleton_mul.mp hy'
  obtain ⟨m, hm, hmz⟩ := D.exists_mul_mem_Pinv k (hB z (D.Pinv_le_BK k hz))
  refine ⟨m, hm, ?_⟩
  show _ ∈ ((D.Ik k : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
  rw [D.Ik_frac k, map_natMul ψ]
  exact FractionalIdeal.mem_singleton_mul.mpr ⟨_, hmz, by ring⟩

/-- The commutator `Dt = ψ ∘ (t ·) - (t ·) ∘ ψ`. -/
def Dt (t : 𝓞 K) : K →ₗ[ℚ] K := ψ ∘ₗ LinearMap.mulLeft ℚ (t : K) - LinearMap.mulLeft ℚ (t : K) ∘ₗ ψ

theorem Dt_apply (t : 𝓞 K) (y : K) : Dt ψ t y = ψ ((t : K) * y) - (t : K) * ψ y := rfl

/-- Step 2. -/
theorem defect (hB : ∀ x ∈ D.BK, ψ x ∈ D.BK) (hO : ∀ x ∈ D.OK, ψ x ∈ D.OK) (t : 𝓞 K) (k : ℕ)
    {y : K} (hy : y ∈ D.Jk k) :
    ∃ m : ℕ, ¬ D.q k ∣ m ∧ ∃ o : 𝓞 K, (m : K) * Dt ψ t y = ((D.q k : ℕ) : K) * o := by
  obtain ⟨c, hc⟩ := D.exists_int_sub_mem k t
  set π : 𝓞 K := t - (c : 𝓞 K)
  have hπ : ((π : 𝓞 K) : K) ∈ (D.Pf k : Submodule (𝓞 K) K) := D.coe_mem_Pf k hc
  have hD : Dt ψ t y = ψ ((π : K) * y) - (π : K) * ψ y := by
    rw [Dt_apply]
    have : ((π : 𝓞 K) : K) = (t : K) - (c : K) := by simp [π]
    rw [this, sub_mul, map_sub, map_intMul ψ, sub_mul]; ring
  obtain ⟨o1, ho1⟩ := D.mul_mem_Pf_Ik k hπ hy
  obtain ⟨m, hm, hmy⟩ := D.local_mul ψ hB k hy
  obtain ⟨o2, ho2⟩ := D.mul_mem_Pf_Ik k hπ hmy
  obtain ⟨o3, ho3⟩ := (D.mem_OK_iff).mp (hO _ (D.coe_mem_OK o1))
  refine ⟨m, hm, (m : 𝓞 K) * o3 - o2, ?_⟩
  rw [hD, ho1, map_natMul ψ, ← ho3]
  have : (m : K) * ((π : K) * ψ y) = (π : K) * ((m : K) * ψ y) := by ring
  rw [mul_sub, this, ho2]
  push_cast; ring

/-- Step 2, uniform over `I_k`. -/
theorem uniform_defect (hB : ∀ x ∈ D.BK, ψ x ∈ D.BK) (hO : ∀ x ∈ D.OK, ψ x ∈ D.OK) (t : 𝓞 K)
    (k : ℕ) : ∃ m : ℕ, ¬ D.q k ∣ m ∧ ∀ y ∈ D.Ik k,
      ∃ o : 𝓞 K, (m : K) * Dt ψ t (y : K) = ((D.q k : ℕ) : K) * o := by
  classical
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian ((D.Ik k).restrictScalars ℤ))
  -- a single `m` for the finitely many generators
  have hgen : ∀ T : Finset (𝓞 K), (∀ s ∈ T, s ∈ D.Ik k) → ∃ m : ℕ, ¬ D.q k ∣ m ∧
      ∀ s ∈ T, ∃ o : 𝓞 K, (m : K) * Dt ψ t (s : K) = ((D.q k : ℕ) : K) * o := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨1, (D.q_prime k).not_dvd_one, by simp⟩
    | insert a T haT ih =>
      intro hT
      obtain ⟨m, hm, hmT⟩ := ih (fun s hs => hT s (Finset.mem_insert_of_mem hs))
      obtain ⟨n, hn, o, ho⟩ := D.defect ψ hB hO t k (D.coe_mem_Jk k (hT a (Finset.mem_insert_self a T)))
      refine ⟨m * n, fun h => ((Nat.Prime.dvd_mul (D.q_prime k)).mp h).elim hm hn, ?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact ⟨(m : 𝓞 K) * o, by push_cast; rw [mul_assoc, ho]; ring⟩
      · obtain ⟨o', ho'⟩ := hmT s hs
        exact ⟨(n : 𝓞 K) * o', by push_cast; rw [mul_comm (m : K), mul_assoc, ho']; ring⟩
  have hSk : ∀ s ∈ S, s ∈ D.Ik k := fun s hs => by
    have : s ∈ Submodule.span ℤ (S : Set (𝓞 K)) := Submodule.subset_span hs
    rw [hS] at this; exact this
  obtain ⟨m, hm, hmS⟩ := hgen S hSk
  refine ⟨m, hm, fun y hy => ?_⟩
  have hy' : y ∈ Submodule.span ℤ (S : Set (𝓞 K)) := by rw [hS]; exact hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem s hs => exact hmS s hs
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨oa, hoa⟩ := ha; obtain ⟨ob, hob⟩ := hb
    exact ⟨oa + ob, by push_cast; rw [map_add, mul_add, hoa, hob]; ring⟩
  | smul z a _ ha =>
    obtain ⟨oa, hoa⟩ := ha
    refine ⟨(z : 𝓞 K) * oa, ?_⟩
    have : ((z • a : 𝓞 K) : K) = (z : K) * (a : K) := by simp [zsmul_eq_mul]
    have hz : (((z : 𝓞 K) : 𝓞 K) : K) = (z : K) := by simp
    rw [this, map_intMul (Dt ψ t), mul_left_comm, hoa]; simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_intCast]; ring

end AdelicToriLean.DegreeOnePrimes
