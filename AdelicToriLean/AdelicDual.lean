import AdelicToriLean.PerpQuot
import AdelicToriLean.QHatSelfDual
import AdelicToriLean.RealDual
import AdelicToriLean.AdelicPairing

/-!
# The adeles are self-dual, and `(𝔸/ℤ)^∨ ≅ ℤ̂ × ℚ`

`𝔸 = ℚ̂ × ℝ` (`Adele`). Every continuous character of `𝔸` is
`(x, y) ↦ e(ψ(u x)) · exp(i t y)` for a unique `(u, t) ∈ 𝔸`, and this identifies `𝔸` with
its Pontryagin dual as topological groups (`adeleSelfDual`).

The closing Example of the paper: with `ℤ` embedded diagonally (`Zd = ℤ · 1`), `ℤ` is closed
in `𝔸`, `𝔸/ℤ` is a locally compact Hausdorff group, and
`(𝔸/ℤ)^∨ ≅ ℤ̂ × ℚ` with `ℚ` discrete (`adeleModZDual`): `(z, q)` goes to the character of
`𝔸/ℤ` induced by `(z + q, -2πq) ∈ 𝔸`.
-/

open Topology Real

noncomputable section

namespace AdelicToriLean

instance : T2Space (Multiplicative Adele) := inferInstanceAs (T2Space Adele)
instance : LocallyCompactSpace (Multiplicative Adele) := inferInstanceAs (LocallyCompactSpace Adele)
instance : SigmaCompactSpace (Multiplicative Adele) := inferInstanceAs (SigmaCompactSpace Adele)

/-! ### Self-duality of `𝔸` -/

/-- The character `(x, y) ↦ e(ψ(u x)) · exp(i t y)` of `𝔸`. -/
def adeleChar (a : Adele) : PontryaginDual (Multiplicative Adele) :=
  ⟨{ toFun := fun x => AddCircle.toCircle (psi (a.1 * (Multiplicative.toAdd x).1)) *
        Circle.exp (a.2 * (Multiplicative.toAdd x).2)
     map_one' := by simp
     map_mul' := fun x y => by
       simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, mul_add, map_add,
         AddCircle.toCircle_add, Circle.exp_add]
       exact mul_mul_mul_comm _ _ _ _ },
    (AddCircle.continuous_toCircle.comp (continuous_psi.comp (continuous_const.mul
      (continuous_fst.comp continuous_toAdd)))).mul
      (Circle.exp.continuous.comp (continuous_const.mul (continuous_snd.comp continuous_toAdd)))⟩

theorem adeleChar_apply (a : Adele) (x : Multiplicative Adele) :
    adeleChar a x = AddCircle.toCircle (psi (a.1 * (Multiplicative.toAdd x).1)) *
      Circle.exp (a.2 * (Multiplicative.toAdd x).2) := rfl

theorem adeleChar_add (a b : Adele) : adeleChar (a + b) = adeleChar a * adeleChar b := by
  ext x
  simp only [adeleChar_apply, Prod.fst_add, Prod.snd_add, add_mul, map_add,
    AddCircle.toCircle_add, Circle.exp_add]
  exact mul_mul_mul_comm _ _ _ _

/-- `adeleChar` as a homomorphism. -/
def adeleHom : Multiplicative Adele →* PontryaginDual (Multiplicative Adele) where
  toFun a := adeleChar (Multiplicative.toAdd a)
  map_one' := by ext x; simp [adeleChar_apply]
  map_mul' a b := adeleChar_add _ _

theorem continuous_adeleHom : Continuous adeleHom := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : Multiplicative Adele × Multiplicative Adele =>
    AddCircle.toCircle (psi ((Multiplicative.toAdd p.1).1 * (Multiplicative.toAdd p.2).1)) *
      Circle.exp ((Multiplicative.toAdd p.1).2 * (Multiplicative.toAdd p.2).2))
  exact (AddCircle.continuous_toCircle.comp (continuous_psi.comp
      ((continuous_fst.comp (continuous_toAdd.comp continuous_fst)).mul
        (continuous_fst.comp (continuous_toAdd.comp continuous_snd))))).mul
    (Circle.exp.continuous.comp ((continuous_snd.comp (continuous_toAdd.comp continuous_fst)).mul
        (continuous_snd.comp (continuous_toAdd.comp continuous_snd))))

theorem exp_mul_eq_one {c : ℝ} (h : ∀ s : ℝ, Circle.exp (c * s) = 1) : c = 0 := by
  by_contra hc
  have := h (π / c)
  rw [mul_div_cancel₀ _ hc, Circle.exp_eq_one] at this
  obtain ⟨m, hm⟩ := this
  have hm' : (1 : ℝ) = 2 * m := by
    have := pi_pos
    field_simp at hm
    nlinarith
  have : (2 * m : ℤ) = 1 := by exact_mod_cast hm'.symm
  omega

theorem adeleChar_injective : Function.Injective adeleChar := by
  intro a b h
  have h1 : adeleChar (a - b) = 1 := by
    rw [show a = (a - b) + b by abel, adeleChar_add] at h
    exact mul_eq_right.mp h
  have hval : ∀ x : Adele, AddCircle.toCircle (psi ((a - b).1 * x.1)) *
      Circle.exp ((a - b).2 * x.2) = 1 := fun x => by
    have := DFunLike.congr_fun h1 (Multiplicative.ofAdd x)
    rwa [adeleChar_apply, PontryaginDual.one_apply] at this
  have h2 : (a - b).2 = 0 := exp_mul_eq_one fun s => by
    simpa using hval (0, s)
  have h1' : (a - b).1 = 0 := by
    by_contra hne
    obtain ⟨w, hw⟩ := exists_psi_ne_zero hne
    have := hval (w, 0)
    simp only [mul_zero, Circle.exp_zero, mul_one] at this
    exact hw ((toCircle_eq_one_iff _).mp this)
  rw [← sub_eq_zero]
  exact Prod.ext h1' h2

theorem adeleHom_injective : Function.Injective adeleHom := fun _ _ h =>
  adeleChar_injective h

/-- **Every continuous character of `𝔸` is some `adeleChar a`.** -/
theorem adeleChar_surjective : Function.Surjective adeleChar := by
  intro χ
  let χ1 : PontryaginDual (Multiplicative QHat) :=
    ⟨{ toFun := fun x => χ (Multiplicative.ofAdd (Multiplicative.toAdd x, 0))
       map_one' := map_one (χ : Multiplicative Adele →ₜ* Circle)
       map_mul' := fun x y => by
         rw [← map_mul (χ : Multiplicative Adele →ₜ* Circle)]; congr 1; apply Multiplicative.toAdd.injective; simp },
      χ.continuous.comp (continuous_ofAdd.comp
        ((continuous_toAdd).prodMk continuous_const))⟩
  let χ2 : PontryaginDual (Multiplicative ℝ) :=
    ⟨{ toFun := fun y => χ (Multiplicative.ofAdd (0, Multiplicative.toAdd y))
       map_one' := map_one (χ : Multiplicative Adele →ₜ* Circle)
       map_mul' := fun x y => by
         rw [← map_mul (χ : Multiplicative Adele →ₜ* Circle)]; congr 1; apply Multiplicative.toAdd.injective; simp },
      χ.continuous.comp (continuous_ofAdd.comp
        (continuous_const.prodMk continuous_toAdd))⟩
  obtain ⟨u, hu⟩ := chi_surjective χ1
  obtain ⟨t, ht⟩ := chiR_surjective χ2
  refine ⟨(u, t), PontryaginDual.ext fun x => ?_⟩
  have hsplit : x = Multiplicative.ofAdd ((Multiplicative.toAdd x).1, 0) *
      Multiplicative.ofAdd (0, (Multiplicative.toAdd x).2) := by
    apply Multiplicative.toAdd.injective
    simp
  conv_rhs => rw [hsplit, map_mul]
  change _ = χ1 (Multiplicative.ofAdd (Multiplicative.toAdd x).1) *
    χ2 (Multiplicative.ofAdd (Multiplicative.toAdd x).2)
  rw [← hu, ← ht, chi_apply, chiR_apply, adeleChar_apply, toAdd_ofAdd, toAdd_ofAdd]

theorem adeleHom_surjective : Function.Surjective adeleHom := fun χ => by
  obtain ⟨a, ha⟩ := adeleChar_surjective χ
  exact ⟨Multiplicative.ofAdd a, ha⟩

/-- **`𝔸` is a self-dual locally compact abelian group.** -/
def adeleSelfDual : Multiplicative Adele ≃ₜ* PontryaginDual (Multiplicative Adele) := by
  haveI : BaireSpace (PontryaginDual (Multiplicative Adele)) :=
    BaireSpace.of_t2Space_locallyCompactSpace
  have hbij : Function.Bijective adeleHom := ⟨adeleHom_injective, adeleHom_surjective⟩
  have hom : IsOpenMap adeleHom :=
    MonoidHom.isOpenMap_of_sigmaCompact _ hbij.2 continuous_adeleHom
  let h := (Equiv.ofBijective _ hbij).toHomeomorphOfContinuousOpen continuous_adeleHom hom
  exact { MulEquiv.ofBijective adeleHom hbij with
    continuous_toFun := continuous_adeleHom
    continuous_invFun := h.symm.continuous }

theorem adeleSelfDual_apply (a x : Adele) :
    adeleSelfDual (Multiplicative.ofAdd a) (Multiplicative.ofAdd x) =
      AddCircle.toCircle (psi (a.1 * x.1)) * Circle.exp (a.2 * x.2) := rfl

/-- **`𝔸` is self-dual**, as an LCA group statement. -/
theorem adele_self_dual :
    LocallyCompactSpace Adele ∧ T2Space Adele ∧
      Nonempty (Multiplicative Adele ≃ₜ* PontryaginDual (Multiplicative Adele)) :=
  ⟨inferInstance, inferInstance, ⟨adeleSelfDual⟩⟩

/-! ### The closing Example: `(𝔸/ℤ)^∨ ≅ ℤ̂ × ℚ` -/

/-- `ℤ`, embedded diagonally in `𝔸 = ℚ̂ × ℝ`. -/
def Zd : AddSubgroup Adele := AddSubgroup.zmultiples 1

theorem mem_Zd {a : Adele} : a ∈ Zd ↔ ∃ n : ℤ, ((n : QHat), (n : ℝ)) = a := by
  simp only [Zd, AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul, mul_one]
  rfl

theorem one_mem_ZHat : (1 : QHat) ∈ ZHat := mem_ZHat.mpr fun v => by
  show (1 : v.adicCompletion ℚ) ∈ _
  exact (v.adicCompletionIntegers ℚ).one_mem

theorem intCast_mem_ZHat (m : ℤ) : (m : QHat) ∈ ZHat := by
  rw [← zsmul_one]; exact ZHat.zsmul_mem one_mem_ZHat m

theorem mul_intCast_mem_ZHat {z : QHat} (hz : z ∈ ZHat) (m : ℤ) : z * m ∈ ZHat := by
  rw [mul_comm, ← zsmul_eq_mul]; exact ZHat.zsmul_mem hz m

theorem toCircle_real (x : ℝ) :
    AddCircle.toCircle ((x : ℝ) : AddCircle (1 : ℝ)) = Circle.exp (2 * π * x) := by
  rw [AddCircle.toCircle_apply_mk]; ring_nf

/-- The diagonal `ℤ` is discrete, hence closed, in `𝔸`. -/
theorem isClosed_Zd : IsClosed (Zd : Set Adele) := by
  have hU : IsOpen ((ZHat : Set QHat) ×ˢ Set.Ioo (-1 / 2 : ℝ) (1 / 2)) :=
    isOpen_ZHat.prod isOpen_Ioo
  have : DiscreteTopology Zd := by
    rw [discreteTopology_iff_isOpen_singleton_zero]
    convert hU.preimage continuous_subtype_val
    ext ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := mem_Zd.mp ha
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_prod, Set.mem_Ioo]
    constructor
    · intro h
      have h0 : ((n : QHat), (n : ℝ)) = 0 := congrArg Subtype.val h
      have : (n : ℝ) = 0 := congrArg Prod.snd h0
      rw [this]
      exact ⟨intCast_mem_ZHat n, by norm_num, by norm_num⟩
    · rintro ⟨-, h1, h2⟩
      have : n = 0 := by
        have h1' : (-1 : ℝ) < 2 * n := by linarith
        have h2' : (2 * n : ℝ) < 1 := by linarith
        have : (-1 : ℤ) < 2 * n := by exact_mod_cast h1'
        have : (2 * n : ℤ) < 1 := by exact_mod_cast h2'
        omega
      subst this
      ext <;> simp
  exact AddSubgroup.isClosed_of_discrete

instance : T2Space (Adele ⧸ Zd) := by
  have : IsClosed (Zd : Set Adele) := isClosed_Zd
  infer_instance

instance : LocallyCompactSpace (Multiplicative (Adele ⧸ Zd)) :=
  inferInstanceAs (LocallyCompactSpace (Adele ⧸ Zd))

/-- `ℚ` with the discrete topology. -/
def QD : Type := ℚ

instance : AddCommGroup QD := inferInstanceAs (AddCommGroup ℚ)
instance : TopologicalSpace QD := ⊥
instance : DiscreteTopology QD := ⟨rfl⟩
instance : Countable QD := inferInstanceAs (Countable ℚ)
instance : IsTopologicalAddGroup QD where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- The identity `QD → ℚ`. -/
def QD.val (q : QD) : ℚ := q

@[simp] theorem QD.val_zero : QD.val 0 = 0 := rfl
@[simp] theorem QD.val_add (q q' : QD) : QD.val (q + q') = QD.val q + QD.val q' := rfl

/-- `(z, q) ↦ (z + q, -2πq) ∈ 𝔸`. -/
def embZQ : ZHat × QD →+ Adele where
  toFun p := ((p.1 : QHat) + algebraMap ℚ QHat (QD.val p.2), -(2 * π * (QD.val p.2 : ℝ)))
  map_zero' := by ext <;> simp
  map_add' p p' := by
    ext
    · simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, QD.val_add, map_add]; abel_nf
    · simp only [Prod.snd_add, QD.val_add, Rat.cast_add]; ring

theorem continuous_embZQ : Continuous embZQ := by
  have h2 : Continuous fun q : QD => QD.val q := continuous_of_discreteTopology
  exact ((continuous_subtype_val.comp continuous_fst).add
      ((continuous_of_discreteTopology (f := fun q : QD => algebraMap ℚ QHat (QD.val q))).comp
        continuous_snd)).prodMk
    ((continuous_of_discreteTopology (f := fun q : QD => -(2 * π * (QD.val q : ℝ)))).comp
      continuous_snd)

theorem embZQ_kills (p : ZHat × QD) (a : Adele) (ha : a ∈ Zd) :
    adeleChar (embZQ p) (Multiplicative.ofAdd a) = 1 := by
  obtain ⟨n, rfl⟩ := mem_Zd.mp ha
  rw [adeleChar_apply]
  simp only [embZQ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toAdd_ofAdd, add_mul, map_add,
    AddCircle.toCircle_add]
  rw [psi_ZHat (mul_intCast_mem_ZHat p.1.2 n), AddCircle.toCircle_zero, one_mul,
    show algebraMap ℚ QHat (QD.val p.2) * (n : QHat) = algebraMap ℚ QHat (QD.val p.2 * n) by
      simp, psi_algebraMap, toCircle_real, ← Circle.exp_add]
  rw [Circle.exp_eq_one]
  exact ⟨0, by push_cast; ring⟩

/-- The homomorphism underlying `descend`. -/
def descendHom (χ : PontryaginDual (Multiplicative Adele))
    (hχ : ∀ a ∈ Zd, χ (Multiplicative.ofAdd a) = 1) :
    Multiplicative (Adele ⧸ Zd) →* Circle :=
  AddMonoidHom.toMultiplicativeLeft (QuotientAddGroup.lift Zd
    (MonoidHom.toAdditiveRight (χ : Multiplicative Adele →* Circle))
    (fun a ha => AddMonoidHom.mem_ker.mpr (by
      show Additive.ofMul (χ (Multiplicative.ofAdd a)) = 0
      rw [hχ a ha]; rfl)))

theorem descendHom_apply (χ : PontryaginDual (Multiplicative Adele)) (hχ) (a : Adele) :
    descendHom χ hχ (Multiplicative.ofAdd (a : Adele ⧸ Zd)) = χ (Multiplicative.ofAdd a) := rfl

/-- A character of `𝔸` trivial on `ℤ` descends to `𝔸/ℤ`. -/
def descend (χ : PontryaginDual (Multiplicative Adele))
    (hχ : ∀ a ∈ Zd, χ (Multiplicative.ofAdd a) = 1) :
    PontryaginDual (Multiplicative (Adele ⧸ Zd)) :=
  ⟨descendHom χ hχ, by
    have hc : Continuous fun y : Adele ⧸ Zd => descendHom χ hχ (Multiplicative.ofAdd y) :=
      QuotientAddGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
        (χ.continuous.comp continuous_ofAdd)
    exact hc.comp continuous_toAdd⟩

theorem descend_apply (χ : PontryaginDual (Multiplicative Adele)) (hχ) (a : Adele) :
    descend χ hχ (Multiplicative.ofAdd (a : Adele ⧸ Zd)) = χ (Multiplicative.ofAdd a) := rfl

/-- The map `ℤ̂ × ℚ → (𝔸/ℤ)^∨`. -/
def PhiZQ : Multiplicative (ZHat × QD) →* PontryaginDual (Multiplicative (Adele ⧸ Zd)) where
  toFun p := descend (adeleChar (embZQ (Multiplicative.toAdd p))) (embZQ_kills _)
  map_one' := PontryaginDual.ext fun x => by
    induction x using Multiplicative.rec with | ofAdd x => ?_
    induction x using QuotientAddGroup.induction_on with | H a => ?_
    rw [descend_apply, toAdd_one, map_zero, PontryaginDual.one_apply]
    simp [adeleChar_apply]
  map_mul' p p' := PontryaginDual.ext fun x => by
    induction x using Multiplicative.rec with | ofAdd x => ?_
    induction x using QuotientAddGroup.induction_on with | H a => ?_
    show adeleChar _ (Multiplicative.ofAdd a) =
      adeleChar _ (Multiplicative.ofAdd a) * adeleChar _ (Multiplicative.ofAdd a)
    rw [toAdd_mul, map_add, adeleChar_add]; rfl

theorem PhiZQ_apply (p : Multiplicative (ZHat × QD)) (a : Adele) :
    PhiZQ p (Multiplicative.ofAdd (a : Adele ⧸ Zd)) =
      adeleChar (embZQ (Multiplicative.toAdd p)) (Multiplicative.ofAdd a) := rfl

theorem continuous_PhiZQ : Continuous PhiZQ := by
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  change Continuous (fun p : Multiplicative (ZHat × QD) × (Adele ⧸ Zd) =>
    PhiZQ p.1 (Multiplicative.ofAdd p.2))
  rw [← (IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff]
  change Continuous (fun r : Multiplicative (ZHat × QD) × Adele =>
    AddCircle.toCircle (psi ((embZQ (Multiplicative.toAdd r.1)).1 * r.2.1)) *
      Circle.exp ((embZQ (Multiplicative.toAdd r.1)).2 * r.2.2))
  have e := continuous_embZQ.comp (continuous_toAdd.comp
    (continuous_fst : Continuous (Prod.fst : Multiplicative (ZHat × QD) × Adele → _)))
  exact (AddCircle.continuous_toCircle.comp (continuous_psi.comp
      ((continuous_fst.comp e).mul (continuous_fst.comp continuous_snd)))).mul
    (Circle.exp.continuous.comp ((continuous_snd.comp e).mul
      (continuous_snd.comp continuous_snd)))

theorem PhiZQ_injective : Function.Injective PhiZQ := by
  rw [injective_iff_map_eq_one]
  intro p hp
  have h1 : adeleChar (embZQ (Multiplicative.toAdd p)) = 1 := PontryaginDual.ext fun x => by
    have := DFunLike.congr_fun hp (Multiplicative.ofAdd (((Multiplicative.toAdd x : Adele)) : Adele ⧸ Zd))
    rwa [PhiZQ_apply, PontryaginDual.one_apply] at this
  have h0 : embZQ (Multiplicative.toAdd p) = 0 :=
    adeleChar_injective (h1.trans (by ext x; simp [adeleChar_apply]))
  have hq : QD.val (Multiplicative.toAdd p).2 = 0 := by
    have := congrArg Prod.snd h0
    simp only [embZQ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_zero, neg_eq_zero,
      mul_eq_zero, OfNat.ofNat_ne_zero, pi_ne_zero, false_or, Rat.cast_eq_zero] at this
    exact this
  have hz : ((Multiplicative.toAdd p).1 : QHat) = 0 := by
    have := congrArg Prod.fst h0
    simp only [embZQ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_zero, hq, map_zero,
      add_zero] at this
    exact this
  apply Multiplicative.toAdd.injective
  exact Prod.ext (Subtype.ext hz) hq

/-- **Every character of `𝔸/ℤ` is some `PhiZQ (z, q)`.** -/
theorem PhiZQ_surjective : Function.Surjective PhiZQ := by
  intro ψ
  let χ : PontryaginDual (Multiplicative Adele) :=
    ⟨(ψ : Multiplicative (Adele ⧸ Zd) →* Circle).comp
        (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Zd)),
      ψ.continuous.comp (continuous_ofAdd.comp (continuous_quot_mk.comp continuous_toAdd))⟩
  obtain ⟨⟨u, t⟩, hut⟩ := adeleChar_surjective χ
  have h1 : adeleChar (u, t) (Multiplicative.ofAdd 1) = 1 := by
    rw [hut]
    show ψ (Multiplicative.ofAdd ((1 : Adele) : Adele ⧸ Zd)) = 1
    have h0 : ((1 : Adele) : Adele ⧸ Zd) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_zmultiples 1)
    erw [h0]
    exact map_one (ψ : Multiplicative (Adele ⧸ Zd) →* Circle)
  obtain ⟨r, z, hz, rfl⟩ := exists_rat_add_ZHat u
  rw [adeleChar_apply, toAdd_ofAdd] at h1
  simp only [Prod.fst_one, Prod.snd_one, mul_one, map_add, psi_ZHat hz, add_zero,
    psi_algebraMap, toCircle_real, ← Circle.exp_add, Circle.exp_eq_one] at h1
  obtain ⟨m, hm⟩ := h1
  refine ⟨Multiplicative.ofAdd (⟨z + m, ZHat.add_mem hz (intCast_mem_ZHat m)⟩,
    (r - m : ℚ)), ?_⟩
  have he : embZQ (⟨z + m, ZHat.add_mem hz (intCast_mem_ZHat m)⟩, (r - m : ℚ)) =
      (algebraMap ℚ QHat r + z, t) := by
    ext
    · simp only [embZQ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, QD.val, map_sub, map_intCast]
      abel_nf
    · simp only [embZQ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, QD.val, Rat.cast_sub,
        Rat.cast_intCast]
      linarith
  refine PontryaginDual.ext fun x => ?_
  induction x using Multiplicative.rec with | ofAdd x => ?_
  induction x using QuotientAddGroup.induction_on with | H a => ?_
  rw [PhiZQ_apply, toAdd_ofAdd, he, hut]
  rfl

instance : CompactSpace ZHat := isCompact_iff_compactSpace.mp isCompact_ZHat

instance : SigmaCompactSpace (Multiplicative (ZHat × QD)) :=
  inferInstanceAs (SigmaCompactSpace (ZHat × QD))

/-- **The closing Example: `(𝔸/ℤ)^∨ ≅ ℤ̂ × ℚ`**, `ℤ̂` compact, `ℚ` discrete. -/
def adeleModZDual :
    Multiplicative (ZHat × QD) ≃ₜ* PontryaginDual (Multiplicative (Adele ⧸ Zd)) := by
  haveI : BaireSpace (PontryaginDual (Multiplicative (Adele ⧸ Zd))) :=
    BaireSpace.of_t2Space_locallyCompactSpace
  have hbij : Function.Bijective PhiZQ := ⟨PhiZQ_injective, PhiZQ_surjective⟩
  have hom : IsOpenMap PhiZQ :=
    MonoidHom.isOpenMap_of_sigmaCompact _ hbij.2 continuous_PhiZQ
  let h := (Equiv.ofBijective _ hbij).toHomeomorphOfContinuousOpen continuous_PhiZQ hom
  exact { MulEquiv.ofBijective PhiZQ hbij with
    continuous_toFun := continuous_PhiZQ
    continuous_invFun := h.symm.continuous }

/-- **Example.** `𝔸/ℤ` is a locally compact Hausdorff group whose dual is `ℤ̂ × ℚ`, the
product of a compact group and a discrete torsion-free group. -/
theorem closing_example :
    IsClosed (Zd : Set Adele) ∧ LocallyCompactSpace (Adele ⧸ Zd) ∧ T2Space (Adele ⧸ Zd) ∧
      CompactSpace ZHat ∧ DiscreteTopology QD ∧
      Nonempty (Multiplicative (ZHat × QD) ≃ₜ* PontryaginDual (Multiplicative (Adele ⧸ Zd))) :=
  ⟨isClosed_Zd, inferInstance, inferInstance, inferInstance, inferInstance, ⟨adeleModZDual⟩⟩

end AdelicToriLean
