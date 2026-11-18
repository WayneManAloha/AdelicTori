import Mathlib

/-!
# Nonarchimedean dimension: the discrete side

Lewis (2019), Proposition 1 and p. 6: a finitely generated profinite abelian group `D` has a
standard representation `D ≅ ∏_{j=1}^m Δ_j`, `Δ_j = ∏_p ℤ̂(p^{n_p(j)})` procyclic with `Δ_{j+1}` a
quotient of `Δ_j`, and `dim_n D = #{j : Δ_j infinite}`. For `D = T^∨`, `T` a discrete torsion
group, open subgroups `U ⊆ D` are the annihilators of finite `E ⊆ T`, `U ≅ (T/E)^∨`, and `U` needs
`max_p rk_p(T/E)` topological generators, `rk_p X = dim_{𝔽_p} X[p]`. Dropping the finitely many
finite `Δ_j` gives an open subgroup with `dim_n D` generators, and no open subgroup needs fewer
(its `ℤ_p`-ranks and its `p`-ranks at almost all `p` are those of `D`). Hence

  `dim_n (T^∨) = min { max_p rk_p (T/E) : E ⊆ T finite }`,

which is the definition used here (`dimN`), with `rk_p X = log_p |X[p]|` (`prank`).

* `card_ptors_quot_le`: `|(T/E)[p]| ≤ |T[p]|` for finite `E`;
* `dimSet_quot`: `dim_n` is unchanged by quotients by finite subgroups (`dimN_quot`);
* `dimN_eq_of_finiteIndex`: for subgroups `F₁, F₂ ⊆ A` of finite index in `F₁ + F₂`,
  `dim_n(A/F₁) = dim_n(A/F₂)`: the paper's independence of the delta-subgroup
  (Lewis 2019, Lemma 6, Corollary 4).
-/

noncomputable section

namespace AdelicToriLean

variable (T : Type*) [AddCommGroup T]

/-- Multiplication by `p`. -/
def mulP (p : ℕ) : T →+ T where
  toFun x := p • x
  map_zero' := smul_zero p
  map_add' x y := smul_add p x y

/-- The `p`-torsion `T[p]`. -/
def ptors (p : ℕ) : AddSubgroup T := (mulP T p).ker

theorem mem_ptors {p : ℕ} {x : T} : x ∈ ptors T p ↔ p • x = 0 := Iff.rfl

/-- The `p`-rank `log_p |T[p]|`. -/
def prank (p : ℕ) : ℕ := Nat.log p (Nat.card (ptors T p))

/-- Bounds `k` achieved by some finite quotient: `max_p rk_p (T/E) ≤ k`. -/
def dimSet : Set ℕ := {k | ∃ E : AddSubgroup T, Finite E ∧ ∀ p, p.Prime → prank (T ⧸ E) p ≤ k}

/-- **Nonarchimedean dimension** `dim_n (T^∨)` of the dual of a torsion group `T`. -/
def dimN : ℕ := sInf (dimSet T)

variable {T}

/-- `p`-ranks are invariant under isomorphism. -/
theorem prank_congr {T' : Type*} [AddCommGroup T'] (e : T ≃+ T') (p : ℕ) :
    prank T p = prank T' p := by
  unfold prank
  congr 1
  refine Nat.card_congr
    { toFun := fun x => ⟨e x, by
        show p • e x = 0; rw [← map_nsmul, show p • (x : T) = 0 from x.2, map_zero]⟩
      invFun := fun y => ⟨e.symm y, by
        show p • e.symm y = 0; rw [← map_nsmul, show p • (y : T') = 0 from y.2, map_zero]⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }

/-- **`|(T/E)[p]| ≤ |T[p]|`** for finite `E`. -/
theorem card_ptors_quot_le (E : AddSubgroup T) [Finite E] (p : ℕ) :
    Nat.card (ptors (T ⧸ E) p) ≤ Nat.card (ptors T p) := by
  set S : AddSubgroup T := E.comap (mulP T p)
  have hES : E ≤ S := fun e he => show p • e ∈ E from E.nsmul_mem he p
  have hTS : ptors T p ≤ S := fun x hx => show p • x ∈ E by rw [show p • x = 0 from hx]; exact E.zero_mem
  -- `g : S → T/E` has range `(T/E)[p]` and kernel `E`
  let g : S →+ T ⧸ E := (QuotientAddGroup.mk' E).comp S.subtype
  have hrange : g.range = ptors (T ⧸ E) p := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      show p • ((x : T) : T ⧸ E) = 0
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]; exact hx
    · intro hy
      induction y using QuotientAddGroup.induction_on with | H x => ?_
      refine ⟨⟨x, ?_⟩, rfl⟩
      have : ((p • x : T) : T ⧸ E) = 0 := by rw [QuotientAddGroup.mk_nsmul]; exact hy
      exact (QuotientAddGroup.eq_zero_iff (p • x)).mp this
  have hker : Nat.card g.ker = Nat.card E := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x : S), (QuotientAddGroup.eq_zero_iff _).mp x.2⟩
        invFun := fun e => ⟨⟨e, hES e.2⟩, (QuotientAddGroup.eq_zero_iff _).mpr e.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h1 : Nat.card S = Nat.card (ptors (T ⧸ E) p) * Nat.card E := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, hrange, hker]
  -- `h : S → E`, `x ↦ p x`, has kernel `T[p]`
  let h : S →+ E :=
    { toFun := fun x => ⟨p • (x : T), x.2⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have hkerh : Nat.card h.ker = Nat.card (ptors T p) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x : S), by
          have := x.2
          rw [AddMonoidHom.mem_ker] at this
          exact congrArg Subtype.val this⟩
        invFun := fun y => ⟨⟨y, hTS y.2⟩, by
          rw [AddMonoidHom.mem_ker]; ext; exact y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : Nat.card S ≤ Nat.card E * Nat.card (ptors T p) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup h.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange h).toEquiv, hkerh]
    exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective _ Subtype.coe_injective)
  have hE : 0 < Nat.card E := Nat.card_pos
  rw [h1, mul_comm (Nat.card E)] at h2
  exact Nat.le_of_mul_le_mul_right h2 hE

theorem prank_quot_le (E : AddSubgroup T) [Finite E] (p : ℕ) :
    prank (T ⧸ E) p ≤ prank T p :=
  Nat.log_mono_right (card_ptors_quot_le E p)

/-- The preimage of a finite subgroup of `T/E` is finite when `E` is. -/
theorem finite_comap (E : AddSubgroup T) [Finite E] (E' : AddSubgroup (T ⧸ E)) [Finite E'] :
    Finite (E'.comap (QuotientAddGroup.mk' E)) := by
  have hfin : ((E'.comap (QuotientAddGroup.mk' E) : AddSubgroup T) : Set T).Finite := by
    show ((QuotientAddGroup.mk' E) ⁻¹' (E' : Set (T ⧸ E))).Finite
    refine (Set.toFinite (E' : Set (T ⧸ E))).preimage' fun b _ => ?_
    induction b using QuotientAddGroup.induction_on with | H x => ?_
    have : (QuotientAddGroup.mk' E) ⁻¹' {(x : T ⧸ E)} = (fun e => x + e) '' (E : Set T) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, QuotientAddGroup.mk'_apply,
        Set.mem_image, SetLike.mem_coe]
      constructor
      · intro hy
        exact ⟨-x + y, QuotientAddGroup.eq.mp hy.symm, by abel⟩
      · rintro ⟨e, he, rfl⟩
        exact (QuotientAddGroup.eq.mpr (by simpa using he)).symm
    rw [this]
    exact (Set.toFinite (E : Set T)).image _
  exact hfin.to_subtype

/-- **`dim_n` is unchanged by quotients by finite subgroups.** -/
theorem dimSet_quot (E : AddSubgroup T) [Finite E] : dimSet (T ⧸ E) = dimSet T := by
  ext k
  constructor
  · rintro ⟨E', hE', hk⟩
    have := hE'
    set E'' := E'.comap (QuotientAddGroup.mk' E)
    have : Finite E'' := finite_comap E E'
    have hle : E ≤ E'' := fun e he => show ((e : T) : T ⧸ E) ∈ E' by
      rw [(QuotientAddGroup.eq_zero_iff _).mpr he]; exact E'.zero_mem
    have hmap : E''.map (QuotientAddGroup.mk' E) = E' :=
      AddSubgroup.map_comap_eq_self_of_surjective (QuotientAddGroup.mk'_surjective E) E'
    refine ⟨E'', inferInstance, fun p hp => ?_⟩
    have e := (QuotientAddGroup.quotientAddEquivOfEq hmap).symm.trans
      (QuotientAddGroup.quotientQuotientEquivQuotient E E'' hle)
    rw [← prank_congr e]
    exact hk p hp
  · rintro ⟨E'', hE'', hk⟩
    have : Finite E'' := hE''
    set E' := E''.map (QuotientAddGroup.mk' E)
    have : Finite E' :=
      ((Set.toFinite (E'' : Set T)).image (QuotientAddGroup.mk' E)).to_subtype
    refine ⟨E', inferInstance, fun p hp => ?_⟩
    have hle : E ≤ E ⊔ E'' := le_sup_left
    have hmap : (E ⊔ E'').map (QuotientAddGroup.mk' E) = E' := by
      simp only [AddSubgroup.map_sup, QuotientAddGroup.map_mk'_self, bot_sup_eq, E']
    have e1 := (QuotientAddGroup.quotientAddEquivOfEq hmap).symm.trans
      (QuotientAddGroup.quotientQuotientEquivQuotient E (E ⊔ E'') hle)
    rw [prank_congr e1]
    -- `T/(E ⊔ E'')` is a finite quotient of `T/E''`
    have hle' : E'' ≤ E ⊔ E'' := le_sup_right
    set F := (E ⊔ E'').map (QuotientAddGroup.mk' E'')
    have hF : F = E.map (QuotientAddGroup.mk' E'') := by
      simp only [F, AddSubgroup.map_sup, QuotientAddGroup.map_mk'_self, sup_bot_eq]
    have : Finite F := by
      rw [hF]; exact ((Set.toFinite (E : Set T)).image (QuotientAddGroup.mk' E'')).to_subtype
    have e2 := QuotientAddGroup.quotientQuotientEquivQuotient E'' (E ⊔ E'') hle'
    rw [← prank_congr e2]
    exact (prank_quot_le F p).trans (hk p hp)

theorem log_self' {p : ℕ} (hp : p.Prime) : Nat.log p p = 1 := by
  simpa using Nat.log_pow hp.one_lt 1

/-- `(T/E)[p]` is finite when `T[p]` and `E` are. -/
theorem finite_ptors_quot (E : AddSubgroup T) [Finite E] (p : ℕ) [Finite (ptors T p)] :
    Finite (ptors (T ⧸ E) p) := by
  set S : AddSubgroup T := E.comap (mulP T p)
  have hS : (S : Set T).Finite := by
    show ((mulP T p) ⁻¹' (E : Set T)).Finite
    refine (Set.toFinite (E : Set T)).preimage' fun b _ => ?_
    by_cases hb : ∃ x0, mulP T p x0 = b
    · obtain ⟨x0, rfl⟩ := hb
      have : (mulP T p) ⁻¹' {mulP T p x0} ⊆ (fun t => x0 + t) '' (ptors T p : Set T) := by
        intro y hy
        refine ⟨-x0 + y, ?_, by abel_nf⟩
        show p • (-x0 + y) = 0
        have hy' : p • y = p • x0 := hy
        rw [smul_add, smul_neg, hy', neg_add_cancel]
      exact ((Set.toFinite (ptors T p : Set T)).image _).subset this
    · have : (mulP T p) ⁻¹' {b} = ∅ := by
        ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]; exact fun h => hb ⟨y, h⟩
      rw [this]; exact Set.finite_empty
  have hsub : (ptors (T ⧸ E) p : Set (T ⧸ E)) ⊆ (QuotientAddGroup.mk' E) '' (S : Set T) := by
    intro y hy
    induction y using QuotientAddGroup.induction_on with | H x => ?_
    refine ⟨x, ?_, rfl⟩
    have : ((p • x : T) : T ⧸ E) = 0 := by rw [QuotientAddGroup.mk_nsmul]; exact hy
    exact (QuotientAddGroup.eq_zero_iff (p • x)).mp this
  exact ((hS.image _).subset hsub).to_subtype

/-- A nonzero element of `X[p]`, `X[p]` finite, gives `rk_p X ≥ 1`. -/
theorem one_le_prank {X : Type*} [AddCommGroup X] {p : ℕ} (hp : p.Prime) [Finite (ptors X p)]
    {x : X} (hx : p • x = 0) (hx0 : x ≠ 0) : 1 ≤ prank X p := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : addOrderOf x = p := addOrderOf_eq_prime hx hx0
  have hz : Nat.card (AddSubgroup.zmultiples x) = p := by rw [Nat.card_zmultiples, hord]
  have hinj : Nat.card (AddSubgroup.zmultiples x) ≤ Nat.card (ptors X p) := by
    refine Nat.card_le_card_of_injective
      (fun y : AddSubgroup.zmultiples x => (⟨y, ?_⟩ : ptors X p)) ?_
    · obtain ⟨m, hm⟩ := y.2
      show p • (y : X) = 0
      rw [← hm, smul_comm, hx, smul_zero]
    · intro a b h
      have := congrArg Subtype.val h
      exact Subtype.ext this
  have hcard : p ≤ Nat.card (ptors X p) := hz ▸ hinj
  unfold prank
  calc 1 = Nat.log p p := (log_self' hp).symm
    _ ≤ _ := Nat.log_mono_right hcard

/-- If `T[p]` has at most `p` elements for every prime `p`, then `1 ∈ dimSet T`. -/
theorem one_mem_dimSet (h : ∀ p, p.Prime → Nat.card (ptors T p) ≤ p) : 1 ∈ dimSet T := by
  refine ⟨⊥, inferInstance, fun p hp => ?_⟩
  rw [← prank_congr (QuotientAddGroup.quotientBot (G := T)).symm]
  unfold prank
  calc Nat.log p (Nat.card (ptors T p)) ≤ Nat.log p p := Nat.log_mono_right (h p hp)
    _ = 1 := log_self' hp

/-- **`dim_n = 1`** when `|T[p]| ≤ p` for every prime `p` and no finite quotient kills all
`p`-torsion. -/
theorem dimN_eq_one (h1 : ∀ p, p.Prime → Nat.card (ptors T p) ≤ p)
    (h0 : ∀ E : AddSubgroup T, Finite E → ∃ p, p.Prime ∧ 1 ≤ prank (T ⧸ E) p) : dimN T = 1 := by
  have hmem := one_mem_dimSet h1
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hlt
  push Not at hlt
  have h00 : dimN T = 0 := by omega
  have := Nat.sInf_mem ⟨1, hmem⟩
  rw [show sInf (dimSet T) = 0 from h00] at this
  obtain ⟨E, hE, hk⟩ := this
  obtain ⟨p, hp, hp1⟩ := h0 E hE
  have := hk p hp
  omega

/-- **`dim_n (T/E) = dim_n T`** for finite `E`. -/
theorem dimN_quot (E : AddSubgroup T) [Finite E] : dimN (T ⧸ E) = dimN T := by
  unfold dimN; rw [dimSet_quot]

/-- `dim_n` is invariant under isomorphism. -/
theorem dimSet_congr {T' : Type*} [AddCommGroup T'] (e : T ≃+ T') : dimSet T = dimSet T' := by
  ext k
  constructor
  · rintro ⟨E, hE, hk⟩
    have : Finite E := hE
    refine ⟨E.map (e : T →+ T'), ((Set.toFinite (E : Set T)).image e).to_subtype, fun p hp => ?_⟩
    rw [← prank_congr (QuotientAddGroup.congr E _ e rfl)]
    exact hk p hp
  · rintro ⟨E, hE, hk⟩
    have : Finite E := hE
    refine ⟨E.map (e.symm : T' →+ T), ((Set.toFinite (E : Set T')).image e.symm).to_subtype,
      fun p hp => ?_⟩
    rw [← prank_congr (QuotientAddGroup.congr E _ e.symm rfl)]
    exact hk p hp

theorem dimN_congr {T' : Type*} [AddCommGroup T'] (e : T ≃+ T') : dimN T = dimN T' := by
  unfold dimN; rw [dimSet_congr e]

/-- **Independence of the delta-subgroup.** If `F₁, F₂ ⊆ A` both have finite index in `F₁ + F₂`,
then `dim_n (A/F₁) = dim_n (A/F₂)`. -/
theorem dimN_eq_of_finiteIndex {A : Type*} [AddCommGroup A] (F₁ F₂ : AddSubgroup A)
    [Finite ((F₁ ⊔ F₂).map (QuotientAddGroup.mk' F₁))]
    [Finite ((F₁ ⊔ F₂).map (QuotientAddGroup.mk' F₂))] :
    dimN (A ⧸ F₁) = dimN (A ⧸ F₂) := by
  rw [← dimN_quot ((F₁ ⊔ F₂).map (QuotientAddGroup.mk' F₁)),
    ← dimN_quot ((F₁ ⊔ F₂).map (QuotientAddGroup.mk' F₂)),
    dimN_congr (QuotientAddGroup.quotientQuotientEquivQuotient F₁ (F₁ ⊔ F₂) le_sup_left),
    dimN_congr (QuotientAddGroup.quotientQuotientEquivQuotient F₂ (F₁ ⊔ F₂) le_sup_right)]

end AdelicToriLean
