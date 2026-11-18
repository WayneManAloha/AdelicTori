import AdelicToriLean.NonarchDim
import AdelicToriLean.Paper

/-!
# `dim_n(B_K^∨) = 1`

For the group of integers `B_K = Σ_k 𝔭_k⁻¹`, `T_K = B_K/𝒪_K` (`TKq D`) is the discrete dual of the
delta-subgroup `T_K^∨` of `B_K^∨`. Every `T_K[p]` has at most `p` elements
(`card_ptors_TK_le`), and every finite quotient of `T_K` still has nonzero `q_k`-torsion for some
`k` (`exists_prank_quot`), so `dim_n(T_K^∨) = 1` (`dimN_TK`). With Lemma 6 / Corollary 4 of
Lewis 2019 (`dimN_eq_of_finiteIndex`), `dim_n(B_K^∨) = 1`.
-/

open NumberField

noncomputable section

namespace AdelicToriLean

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

/-- `T_K = B_K / 𝒪_K`. -/
abbrev TKq : Type _ := D.BK ⧸ (D.OK.comap D.BK.subtype).toAddSubgroup

/-- `(P k)⁻¹ / 𝒪_K → B_K / 𝒪_K`. -/
def phiK (k : ℕ) : D.PinvQuot k →+ TKq D :=
  QuotientAddGroup.map _ _ (Submodule.inclusion (D.Pinv_le_BK k)).toAddMonoidHom
    (fun _ hx => hx)

theorem phiK_mk (k : ℕ) (x : (D.Pinv k : Submodule (𝓞 K) K)) :
    phiK D k (x : D.PinvQuot k) =
      ((⟨(x : K), D.Pinv_le_BK k x.2⟩ : D.BK) : TKq D) := rfl

instance (k : ℕ) : Finite (D.PinvQuot k) :=
  Nat.finite_of_card_ne_zero (by rw [D.card_PinvQuot k]; exact (D.q_prime k).ne_zero)

theorem phiK_injective (k : ℕ) : Function.Injective (phiK D k) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  induction y using QuotientAddGroup.induction_on with | H x => ?_
  rw [phiK_mk, QuotientAddGroup.eq_zero_iff] at hy
  exact (QuotientAddGroup.eq_zero_iff _).mpr hy

/-- `T_K[q_k]` lies in the image of `(P k)⁻¹ / 𝒪_K`. -/
theorem ptors_le_range {k : ℕ} : ptors (TKq D) (D.q k) ≤ (phiK D k).range := by
  intro y hy
  induction y using QuotientAddGroup.induction_on with | H x => ?_
  have h1 : ((D.q k • x : D.BK) : TKq D) = 0 := by rw [QuotientAddGroup.mk_nsmul]; exact hy
  have h2 : ((D.q k ^ 1 : ℕ) : K) * (x : K) ∈ D.OK := by
    have := (QuotientAddGroup.eq_zero_iff _).mp h1
    simpa [nsmul_eq_mul] using this
  have hx := primary_component_q D k 1 x.2 h2
  exact ⟨((⟨(x : K), hx⟩ : (D.Pinv k : Submodule (𝓞 K) K)) : D.PinvQuot k), rfl⟩

/-- For `p` different from every `q_k`, `T_K[p] = 0`. -/
theorem ptors_eq_bot {p : ℕ} (hp : p.Prime) (hpq : ∀ k, D.q k ≠ p) : ptors (TKq D) p = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  induction y using QuotientAddGroup.induction_on with | H x => ?_
  have h1 : ((p • x : D.BK) : TKq D) = 0 := by rw [QuotientAddGroup.mk_nsmul]; exact hy
  have h2 : ((p ^ 1 : ℕ) : K) * (x : K) ∈ D.OK := by
    have := (QuotientAddGroup.eq_zero_iff _).mp h1
    simpa [nsmul_eq_mul] using this
  exact (AddSubgroup.mem_bot).mpr
    ((QuotientAddGroup.eq_zero_iff _).mpr (primary_component_other D hp hpq 1 x.2 h2))

theorem finite_ptors_TK {p : ℕ} (hp : p.Prime) : Finite (ptors (TKq D) p) := by
  by_cases h : ∃ k, D.q k = p
  · obtain ⟨k, rfl⟩ := h
    have : Finite (phiK D k).range :=
      Finite.of_surjective _ (phiK D k).rangeRestrict_surjective
    exact Finite.of_injective (AddSubgroup.inclusion (ptors_le_range D))
      (AddSubgroup.inclusion_injective _)
  · push Not at h
    rw [ptors_eq_bot D hp h]
    infer_instance

/-- **`|T_K[p]| ≤ p`**: every `p`-primary part of `T_K` is cyclic of order `p` or trivial. -/
theorem card_ptors_TK_le {p : ℕ} (hp : p.Prime) : Nat.card (ptors (TKq D) p) ≤ p := by
  by_cases h : ∃ k, D.q k = p
  · obtain ⟨k, rfl⟩ := h
    have : Finite (phiK D k).range :=
      Finite.of_surjective _ (phiK D k).rangeRestrict_surjective
    calc Nat.card (ptors (TKq D) (D.q k)) ≤ Nat.card (phiK D k).range :=
          Nat.card_le_card_of_injective _ (AddSubgroup.inclusion_injective (ptors_le_range D))
      _ ≤ Nat.card (D.PinvQuot k) :=
          Nat.card_le_card_of_surjective _ (phiK D k).rangeRestrict_surjective
      _ = D.q k := D.card_PinvQuot k
  · push Not at h
    rw [ptors_eq_bot D hp h, AddSubgroup.card_bot]
    exact hp.one_lt.le

/-- Every finite quotient of `T_K` has nonzero `q_k`-torsion for some `k`. -/
theorem exists_prank_quot (E : AddSubgroup (TKq D)) (hE : Finite E) :
    ∃ p, p.Prime ∧ 1 ≤ prank (TKq D ⧸ E) p := by
  -- a `k` with `q_k ∤ |E|`
  have hfin : {k | D.q k ∣ Nat.card E}.Finite := by
    have hpos : 0 < Nat.card E := Nat.card_pos
    refine ((Nat.divisors (Nat.card E)).finite_toSet.preimage
      (D.q_inj.injOn)).subset fun k hk => ?_
    simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors]
    exact ⟨hk, hpos.ne'⟩
  obtain ⟨k, hk⟩ := hfin.infinite_compl.nonempty
  have hq : (D.q k).Prime := D.q_prime k
  have : Fact (D.q k).Prime := ⟨hq⟩
  -- a nonzero `y ∈ (P k)⁻¹ / 𝒪_K`
  have h1 : 1 < Nat.card (D.PinvQuot k) := by rw [D.card_PinvQuot k]; exact hq.one_lt
  have := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨y, hy⟩ := exists_ne (0 : D.PinvQuot k)
  set t := phiK D k y
  have ht0 : t ≠ 0 := fun h => hy (phiK_injective D k (h.trans (map_zero _).symm))
  have htq : D.q k • t = 0 := by
    rw [← map_nsmul, ← D.card_PinvQuot k, card_nsmul_eq_zero', map_zero]
  have hord : addOrderOf t = D.q k := addOrderOf_eq_prime htq ht0
  have htE : ((t : TKq D) : TKq D ⧸ E) ≠ 0 := by
    intro h
    have hmem := (QuotientAddGroup.eq_zero_iff t).mp h
    apply hk
    show D.q k ∣ Nat.card E
    rw [← hord]
    have := addOrderOf_dvd_natCard (⟨t, hmem⟩ : E)
    rwa [AddSubgroup.addOrderOf_mk] at this
  have : Finite (ptors (TKq D) (D.q k)) := finite_ptors_TK D hq
  have : Finite (ptors (TKq D ⧸ E) (D.q k)) := finite_ptors_quot E (D.q k)
  refine ⟨D.q k, hq, one_le_prank hq ?_ htE⟩
  rw [← QuotientAddGroup.mk_nsmul, htq, QuotientAddGroup.mk_zero]

/-- **`dim_n(T_K^∨) = 1`.** -/
theorem dimN_TK : dimN (TKq D) = 1 :=
  dimN_eq_one (fun _ hp => card_ptors_TK_le D hp) (exists_prank_quot D)

end AdelicToriLean
