import AdelicToriLean.DimLattice
import AdelicToriLean.ZassenhausTopology

/-!
# Arnold, Theorem 0.2: the calibration of `d_p`

Arnold, *Finite Rank Torsion Free Abelian Groups and Rings*, p. 3, Theorem 0.2: for
`0 → F → A → T → 0` with `A` torsion-free,
`dim T[p] + p-rank(A) = p-rank(F) + p-rank(T)`, `p-rank(X) = dim_{𝔽_p} X/pX`.

* `arnold_0_2`: `|T[p]| · |A/pA| = |F/pF| · |T/pT|` (indices), for any torsion-free `A` and
  `F ≤ A`, `T = A/F`;
* `arnold_Zn`: for `F = ι⁻¹(ℤⁿ) ≅ ℤⁿ` (full rank), `|T[p]| · |A/pA| = pⁿ · |T/pT|`.

For `G = A^∨` and `L = Lie_n(G)`: `L_p[p] ≅ G[p] ≅ (A/pA)^∨`, and `|T[p]|/|T/pT| = p^{r_p}` with
`r_p` the number of `ℤ(p^∞)` summands of `T_p`, which by duality is `dim_{ℚ_p}(L_p/Tor L_p)`. So
`arnold_Zn` is the identity `dim_{ℚ_p}(L_p/Tor L_p) + dim_{𝔽_p} L_p[p] = n`: the intrinsic local
count agrees with `d_p(Lie_n G) = n` (`dimNL_nala`). The two duality identifications are paper
arguments.
-/

noncomputable section

namespace AdelicToriLean

variable {A : Type*} [AddCommGroup A]

/-- `T/pT` for `T = A/F`. -/
abbrev modP (T : Type*) [AddCommGroup T] (p : ℕ) := T ⧸ (mulP T p).range

/-- **Arnold, Theorem 0.2.** For `A` torsion-free, `F ≤ A`, `T = A/F`:
`|T[p]| · |A/pA| = |F/pF| · |T/pT|`. -/
theorem arnold_0_2 (htf : ∀ (m : ℕ) (a : A), 0 < m → m • a = 0 → a = 0) (F : AddSubgroup A)
    {p : ℕ} (hp : 0 < p) :
    Nat.card (ptors (A ⧸ F) p) * (mulP A p).range.index =
      (F.map (mulP A p)).relIndex F * Nat.card (modP (A ⧸ F) p) := by
  set P := (mulP A p).range
  set pF := F.map (mulP A p)
  -- `T/pT = A/(pA + F)`
  have hmap : (P ⊔ F).map (QuotientAddGroup.mk' F) = (mulP (A ⧸ F) p).range := by
    rw [AddSubgroup.map_sup, QuotientAddGroup.map_mk'_self, sup_bot_eq]
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact ⟨(a : A ⧸ F), rfl⟩
    · rintro ⟨y, rfl⟩
      induction y using QuotientAddGroup.induction_on with | H a => ?_
      exact ⟨p • a, ⟨a, rfl⟩, by simp [mulP, QuotientAddGroup.mk_nsmul]⟩
  have hT : Nat.card (modP (A ⧸ F) p) = (P ⊔ F).index := by
    unfold AddSubgroup.index
    exact Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hmap).symm.trans
      (QuotientAddGroup.quotientQuotientEquivQuotient F (P ⊔ F) le_sup_right)).toEquiv
  -- `T[p] ≅ (pA ∩ F)/pF`
  have hpF : pF ≤ P ⊓ F := by
    rintro _ ⟨f, hf, rfl⟩; exact ⟨⟨f, rfl⟩, F.nsmul_mem hf p⟩
  have htors : Nat.card (ptors (A ⧸ F) p) = pF.relIndex (P ⊓ F) := by
    unfold AddSubgroup.relIndex AddSubgroup.index
    let g : ptors (A ⧸ F) p → ↥(P ⊓ F) ⧸ pF.addSubgroupOf (P ⊓ F) := fun t =>
      ((⟨p • (t : A ⧸ F).out, ⟨⟨(t : A ⧸ F).out, rfl⟩, by
        show p • (t : A ⧸ F).out ∈ F
        rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul,
          QuotientAddGroup.out_eq']; exact t.2⟩⟩ : ↥(P ⊓ F)) : ↥(P ⊓ F) ⧸ pF.addSubgroupOf (P ⊓ F))
    refine Nat.card_congr (Equiv.ofBijective g ⟨?_, ?_⟩)
    · intro t t' h
      rw [QuotientAddGroup.eq] at h
      obtain ⟨f, hf, hfe⟩ := h
      apply Subtype.ext
      rw [← QuotientAddGroup.out_eq' (t : A ⧸ F), ← QuotientAddGroup.out_eq' (t' : A ⧸ F)]
      apply QuotientAddGroup.eq.mpr
      have h1 : p • (-(t : A ⧸ F).out + (t' : A ⧸ F).out - f) = 0 := by
        have := hfe
        simp only [map_add, map_neg, AddSubgroup.coe_subtype] at this
        rw [smul_sub, smul_add, smul_neg]
        change p • f = -(p • (t : A ⧸ F).out) + p • (t' : A ⧸ F).out at this
        rw [← this]; abel
      have h2 := htf p _ hp h1
      rw [sub_eq_zero] at h2
      rw [h2]; exact hf
    · intro y
      induction y using QuotientAddGroup.induction_on with | H x => ?_
      obtain ⟨⟨a, ha⟩, hxF⟩ := x.2
      have hat : (a : A ⧸ F) ∈ ptors (A ⧸ F) p := by
        show p • (a : A ⧸ F) = 0
        rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
        rw [show p • a = (x : A) from ha]; exact hxF
      refine ⟨⟨_, hat⟩, ?_⟩
      apply QuotientAddGroup.eq.mpr
      -- `out (a + F) = a + f`
      obtain ⟨f, hf, hfa⟩ : ∃ f ∈ F, ((a : A ⧸ F)).out = a + f := by
        refine ⟨-a + ((a : A ⧸ F)).out, ?_, by abel⟩
        exact QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (a : A ⧸ F)).symm
      refine ⟨-f, F.neg_mem hf, ?_⟩
      simp only [map_add, map_neg, AddSubgroup.coe_subtype]
      change -(p • f) = -(p • ((a : A ⧸ F)).out) + (x : A)
      rw [hfa, ← show p • a = (x : A) from ha, smul_add]; abel
  have h1 : P.index = P.relIndex (P ⊔ F) * (P ⊔ F).index :=
    (AddSubgroup.relIndex_mul_index le_sup_left).symm
  have h2 : P.relIndex (P ⊔ F) = (P ⊓ F).relIndex F := by
    rw [AddSubgroup.relIndex_sup_left, AddSubgroup.inf_relIndex_right]
  have h3 : pF.relIndex F = pF.relIndex (P ⊓ F) * (P ⊓ F).relIndex F :=
    (AddSubgroup.relIndex_mul_relIndex pF (P ⊓ F) F hpF inf_le_right).symm
  rw [htors, hT, h1, h2, h3]
  ring

variable {n : ℕ} {ι : A →+ (Fin n → ℚ)} {d : Fin n → A} (hd : ∀ j, ι (d j) = Pi.single j 1)

include hd in
theorem d_mem_Flat (j : Fin n) : d j ∈ Flat ι := fun i =>
  ⟨if i = j then 1 else 0, by rw [hd, Pi.single_apply]; split_ifs <;> simp⟩

include hd in
theorem iota_sum (k : Fin n → ℤ) : ι (∑ j, k j • d j) = fun i => (k i : ℚ) := by
  funext i
  simp only [map_sum, map_zsmul, hd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  simp

/-- `ℤⁿ ≅ F`, `k ↦ ∑ k_j d_j`. -/
def flatEquiv (hd : ∀ j, ι (d j) = Pi.single j 1) (hι : Function.Injective ι) :
    (Fin n → ℤ) ≃+ Flat ι :=
  AddEquiv.ofBijective
    ({ toFun := fun k => ⟨(∑ j, k j • d j), (Flat ι).sum_mem fun j _ =>
        (Flat ι).zsmul_mem (d_mem_Flat hd j) _⟩
       map_zero' := Subtype.ext (by simp)
       map_add' := fun k k' => Subtype.ext (by simp [add_smul, Finset.sum_add_distrib]) } :
      (Fin n → ℤ) →+ Flat ι)
    ⟨fun k k' h => by
      have h' : (∑ j, k j • d j : A) = ∑ j, k' j • d j := congrArg Subtype.val h
      have := congrArg ι h'
      rw [iota_sum hd, iota_sum hd] at this
      funext j; exact_mod_cast congrFun this j,
     fun y => by
      choose k hk using y.2
      exact ⟨k, Subtype.ext (eq_sum_of_int hd hι hk).symm⟩⟩

theorem flatEquiv_apply (hι : Function.Injective ι) (k : Fin n → ℤ) :
    ((flatEquiv hd hι k : Flat ι) : A) = ∑ j, k j • d j := rfl

include hd in
/-- **`|F/pF| = pⁿ`** for `F = ι⁻¹(ℤⁿ)`. -/
theorem relIndex_pF (hι : Function.Injective ι) (p : ℕ) :
    ((Flat ι).map (mulP A p)).relIndex (Flat ι) = p ^ n := by
  set e := flatEquiv hd hι
  set K : AddSubgroup (Fin n → ℤ) :=
    AddSubgroup.pi Set.univ fun _ => AddSubgroup.zmultiples (p : ℤ)
  have hH : ((Flat ι).map (mulP A p)).addSubgroupOf (Flat ι) =
      K.comap (e.symm : Flat ι →+ (Fin n → ℤ)) := by
    ext y
    obtain ⟨k, rfl⟩ := e.surjective y
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap]
    change _ ↔ e.symm (e k) ∈ K
    rw [e.symm_apply_apply]
    simp only [K, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨f, hf, hfe⟩ j
      obtain ⟨k', hk'⟩ := e.surjective ⟨f, hf⟩
      have h1 : e (p • k') = e k := by
        apply Subtype.ext
        rw [map_nsmul, AddSubgroup.coe_nsmul, hk']
        exact hfe
      have h2 := e.injective h1
      refine ⟨k' j, ?_⟩
      rw [← h2, Pi.smul_apply, nsmul_eq_mul, mul_comm]
    · intro h
      choose c hc using h
      refine ⟨(e c : A), (e c).2, ?_⟩
      show p • ((e c : Flat ι) : A) = ((e k : Flat ι) : A)
      rw [← AddSubgroup.coe_nsmul, ← map_nsmul]
      congr 2
      funext j
      rw [Pi.smul_apply, nsmul_eq_mul, ← hc j]
  unfold AddSubgroup.relIndex
  rw [hH, AddSubgroup.index_comap_of_surjective _ e.symm.surjective, AddSubgroup.index_pi]
  simp [Int.index_zmultiples]

include hd in
/-- **Arnold, Theorem 0.2, for `F ≅ ℤⁿ`**: `|T[p]| · |A/pA| = pⁿ · |T/pT|`, i.e.
`(number of ℤ(p^∞) summands of T_p) + p-rank(A) = n`. -/
theorem arnold_Zn (hι : Function.Injective ι) {p : ℕ} (hp : 0 < p) :
    Nat.card (ptors (A ⧸ Flat ι) p) * (mulP A p).range.index =
      p ^ n * Nat.card (modP (A ⧸ Flat ι) p) := by
  have htf : ∀ (m : ℕ) (a : A), 0 < m → m • a = 0 → a = 0 := fun m a hm h => by
    apply hι
    have := congrArg ι h
    rw [map_nsmul, map_zero] at this
    rw [map_zero]
    funext j
    have hj := congrFun this j
    simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at hj
    exact hj.resolve_left hm.ne'
  rw [arnold_0_2 htf (Flat ι) hp, relIndex_pF hd hι p]

end AdelicToriLean
