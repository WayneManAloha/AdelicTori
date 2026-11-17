import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Theorem `spectrum-resolutions`: the pushout resolution

The paper's proof, in the generality in which it runs. Data:

* `C` a topological additive group, `α : Z →+ C` (the first coordinate of the diagonal
  `ℤⁿ ↪ C' × ℝⁿ`), `ε : Z →+ V` (the second coordinate, `ℤⁿ ↪ ℝⁿ`);
* `B` a discrete group with `j : Z →+ B` (`ℤⁿ ⊆ B`) and `r : B →+ V` (`B ⊆ ℚⁿ ⊆ ℝⁿ`),
  `r ∘ j = ε`.

Objects:

* `G0 = (C × V) / {(α z, ε z)}` (the given resolution);
* `L = (C ⊕ B) / {(α z, -j z)}` (the pushout `L_B = C' ⊕_{ℤⁿ} B`);
* `Dq = (L × V) / {(ι b, r b)}`, `ι b = [0, b]`.

Main result: `spectrumEquiv : Dq ≃ₜ+ G0`, built from the paper's `Φ_B([c, b], x) = [(c, x - b)]`
and `Ψ_B([c, x]) = [([c, 0], x)]`.
-/

open Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace AdelicToriLean

namespace Spectrum

variable {C Z B V : Type*} [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
  [AddCommGroup Z] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  (α : Z →+ C) (ε : Z →+ V) (j : Z →+ B) (r : B →+ V)

/-- `{(α z, ε z)}` in `C × V`. -/
def R : AddSubgroup (C × V) := (α.prod ε).range

/-- The given resolution `G0 = (C × V) / ℤⁿ`. -/
abbrev G0 := (C × V) ⧸ R α ε

/-- `{(α z, -j z)}` in `C × B`. -/
def S : AddSubgroup (C × B) := (α.prod (-j)).range

/-- **The pushout** `L = (C ⊕ B) / {(α z, -z)}`. -/
abbrev L := (C × B) ⧸ S α j

/-- `ι : B → L`, `b ↦ [0, b]`. -/
def ιL : B →+ L α j := (QuotientAddGroup.mk' (S α j)).comp (AddMonoidHom.inr C B)

/-- `{(ι b, r b)}` in `L × V`. -/
def T : AddSubgroup (L α j × V) := ((ιL α j).prod r).range

/-- `(L × V) / B`. -/
abbrev Dq := (L α j × V) ⧸ T α j r

/-- `L → G0`, `[c, b] ↦ [(c, -r b)]`. -/
def Phi1 (h : r.comp j = ε) : L α j →+ G0 α ε :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' (R α ε)).comp ((AddMonoidHom.fst C B).prod (-(r.comp (AddMonoidHom.snd C B)))))
    (by
      intro x hx
      obtain ⟨z, rfl⟩ := hx
      rw [AddMonoidHom.mem_ker]
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.prod_apply,
        AddMonoidHom.coe_fst, AddMonoidHom.neg_apply, AddMonoidHom.coe_snd, map_neg, neg_neg,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      refine ⟨z, ?_⟩
      simp only [AddMonoidHom.prod_apply]
      rw [← h]; rfl)

/-- **`Φ_B : L × V → G0`**, `([c, b], x) ↦ [(c, x - r b)]`. -/
def PhiB (h : r.comp j = ε) : L α j × V →+ G0 α ε :=
  (Phi1 α ε j r h).coprod ((QuotientAddGroup.mk' (R α ε)).comp (AddMonoidHom.inr C V))

theorem PhiB_mk (h : r.comp j = ε) (c : C) (b : B) (x : V) :
    PhiB α ε j r h (QuotientAddGroup.mk (c, b), x) = QuotientAddGroup.mk (c, x - r b) := by
  simp only [PhiB, AddMonoidHom.coprod_apply, Phi1, QuotientAddGroup.lift_mk,
    AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coe_fst,
    AddMonoidHom.neg_apply, AddMonoidHom.coe_snd, QuotientAddGroup.mk'_apply,
    AddMonoidHom.inr_apply]
  rw [← QuotientAddGroup.mk_add]
  congr 1
  ext <;> simp [sub_eq_neg_add]

theorem T_le_ker (h : r.comp j = ε) : T α j r ≤ (PhiB α ε j r h).ker := by
  rintro _ ⟨b, rfl⟩
  rw [AddMonoidHom.mem_ker]
  show PhiB α ε j r h (QuotientAddGroup.mk (0, b), r b) = 0
  rw [PhiB_mk, sub_self]
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨0, by simp⟩

/-- `Φ̄_B : (L × V) / B → G0`. -/
def PhiBar (h : r.comp j = ε) : Dq α j r →+ G0 α ε :=
  QuotientAddGroup.lift _ (PhiB α ε j r h) (T_le_ker α ε j r h)

/-- `C × V → (L × V) / B`, `(c, x) ↦ [([c, 0], x)]`. -/
def Psi0 : C × V →+ Dq α j r :=
  (QuotientAddGroup.mk' (T α j r)).comp
    (((QuotientAddGroup.mk' (S α j)).comp (AddMonoidHom.inl C B)).prodMap (AddMonoidHom.id V))

theorem R_le_ker (h : r.comp j = ε) : R α ε ≤ (Psi0 α j r).ker := by
  rintro _ ⟨z, rfl⟩
  rw [AddMonoidHom.mem_ker]
  simp only [Psi0, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.prod_apply,
    AddMonoidHom.coe_prodMap, Prod.map, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  refine ⟨j z, ?_⟩
  simp only [AddMonoidHom.prod_apply, ιL, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.inr_apply, QuotientAddGroup.mk'_apply]
  refine Prod.ext ?_ ?_
  · show (QuotientAddGroup.mk (0, j z) : L α j) = QuotientAddGroup.mk (α z, 0)
    rw [QuotientAddGroup.eq]
    exact ⟨z, by ext <;> simp⟩
  · show r (j z) = ε z
    rw [← h]; rfl

/-- **`Ψ_B : G0 → (L × V) / B`**. -/
def PsiB (h : r.comp j = ε) : G0 α ε →+ Dq α j r :=
  QuotientAddGroup.lift _ (Psi0 α j r) (R_le_ker α ε j r h)

theorem PsiB_PhiBar (h : r.comp j = ε) (y : Dq α j r) :
    PsiB α ε j r h (PhiBar α ε j r h y) = y := by
  obtain ⟨⟨l, x⟩, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨⟨c, b⟩, rfl⟩ := QuotientAddGroup.mk_surjective l
  show PsiB α ε j r h (PhiB α ε j r h (QuotientAddGroup.mk (c, b), x)) = _
  rw [PhiB_mk]
  show QuotientAddGroup.mk ((QuotientAddGroup.mk (c, 0) : L α j), x - r b) = _
  rw [QuotientAddGroup.eq]
  refine ⟨b, ?_⟩
  refine Prod.ext ?_ ?_
  · show (QuotientAddGroup.mk (0, b) : L α j) =
      -(QuotientAddGroup.mk (c, 0)) + QuotientAddGroup.mk (c, b)
    rw [← QuotientAddGroup.mk_neg, ← QuotientAddGroup.mk_add]
    congr 1; ext <;> simp
  · show r b = -(x - r b) + x
    abel

theorem PhiBar_PsiB (h : r.comp j = ε) (y : G0 α ε) :
    PhiBar α ε j r h (PsiB α ε j r h y) = y := by
  obtain ⟨⟨c, x⟩, rfl⟩ := QuotientAddGroup.mk_surjective y
  show PhiB α ε j r h (QuotientAddGroup.mk (c, 0), x) = _
  rw [PhiB_mk, map_zero, sub_zero]

theorem continuous_PhiBar (h : r.comp j = ε) : Continuous (PhiBar α ε j r h) := by
  have hq1 : IsOpenQuotientMap (QuotientAddGroup.mk : C × B → L α j) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have hq : IsQuotientMap fun p : (C × B) × V => ((QuotientAddGroup.mk p.1 : L α j), p.2) :=
    (hq1.prodMap IsOpenQuotientMap.id).isQuotientMap
  have hcontPhi : Continuous (PhiB α ε j r h) := by
    rw [hq.continuous_iff]
    have : (PhiB α ε j r h ∘ fun p : (C × B) × V => ((QuotientAddGroup.mk p.1 : L α j), p.2)) =
        fun p => QuotientAddGroup.mk (p.1.1, p.2 - r p.1.2) := by
      funext p; exact PhiB_mk α ε j r h p.1.1 p.1.2 p.2
    rw [this]
    refine continuous_quot_mk.comp (continuous_fst.fst.prodMk ?_)
    exact continuous_snd.sub ((continuous_of_discreteTopology (f := r)).comp continuous_fst.snd)
  rw [(QuotientAddGroup.isOpenQuotientMap_mk (N := T α j r)).isQuotientMap.continuous_iff]
  exact hcontPhi

theorem continuous_PsiB (h : r.comp j = ε) : Continuous (PsiB α ε j r h) := by
  rw [(QuotientAddGroup.isOpenQuotientMap_mk (N := R α ε)).isQuotientMap.continuous_iff]
  show Continuous fun p : C × V =>
    (QuotientAddGroup.mk ((QuotientAddGroup.mk (p.1, 0) : L α j), p.2) : Dq α j r)
  exact continuous_quot_mk.comp
    ((continuous_quot_mk.comp (continuous_fst.prodMk continuous_const)).prodMk continuous_snd)

/-- **Spectrum of resolutions**: `(L_B × V) / B ≅ (C × V) / ℤⁿ` as topological groups. -/
def spectrumEquiv (h : r.comp j = ε) : Dq α j r ≃ₜ+ G0 α ε where
  toFun := PhiBar α ε j r h
  invFun := PsiB α ε j r h
  left_inv := PsiB_PhiBar α ε j r h
  right_inv := PhiBar_PsiB α ε j r h
  map_add' := map_add _
  continuous_toFun := continuous_PhiBar α ε j r h
  continuous_invFun := continuous_PsiB α ε j r h

end Spectrum

end AdelicToriLean
