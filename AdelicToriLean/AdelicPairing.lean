import AdelicToriLean.StrongApprox

/-!
# The adeles `𝔸 = ℚ̂ × ℝ` and the pairing with `ℚⁿ`

The paper's self-duality pairing on `𝔸ⁿ`, evaluated against the diagonal copy of `ℚⁿ`:
for `a = (u, x) ∈ 𝔸ⁿ` and `b ∈ ℚⁿ`,
`⟪a, b⟫ = ∑_i (ψ(b_i u_i) - b_i x_i) ∈ ℝ/ℤ`.

* `pairing b : 𝔸ⁿ →+ ℝ/ℤ`, continuous (`continuous_pairing`), additive in `b` (`pairing_add`);
* `pairing_diag`: the diagonal `ℚⁿ ⊆ 𝔸ⁿ` pairs to `0` with every `b ∈ ℚⁿ`.
-/

open IsDedekindDomain

noncomputable section

namespace AdelicToriLean

/-- The adeles of `ℚ`: `𝔸 = ℚ̂ × ℝ`. -/
abbrev Adele := QHat × ℝ

/-- `𝔸ⁿ`. -/
abbrev An (n : ℕ) := Fin n → Adele

/-- `x ↦ b x (mod 1)` on `ℝ`. -/
def realChar (b : ℚ) : ℝ →+ AddCircle (1 : ℝ) :=
  (QuotientAddGroup.mk' _).comp (AddMonoidHom.mulLeft (b : ℝ))

theorem continuous_realChar (b : ℚ) : Continuous (realChar b) :=
  (AddCircle.continuous_mk' 1).comp (continuous_const.mul continuous_id)

/-- `u ↦ ψ(b u)` on `ℚ̂`. -/
def finChar (b : ℚ) : QHat →+ AddCircle (1 : ℝ) :=
  psi.comp (AddMonoidHom.mk' (fun u : QHat => b • u) (smul_add b))

theorem continuous_finChar (b : ℚ) : Continuous (finChar b) := by
  refine continuous_psi.comp ?_
  show Continuous fun u : QHat => b • u
  simp_rw [Algebra.smul_def]
  exact continuous_const.mul continuous_id

/-- One coordinate of the pairing: `(u, x) ↦ ψ(b u) - b x`. -/
def pair1 (b : ℚ) : Adele →+ AddCircle (1 : ℝ) :=
  (finChar b).comp (AddMonoidHom.fst _ _) - (realChar b).comp (AddMonoidHom.snd _ _)

theorem pair1_apply (b : ℚ) (a : Adele) : pair1 b a = finChar b a.1 - realChar b a.2 := rfl

theorem continuous_pair1 (b : ℚ) : Continuous (pair1 b) :=
  ((continuous_finChar b).comp continuous_fst).sub ((continuous_realChar b).comp continuous_snd)

/-- **The pairing** `⟪a, b⟫ = ∑_i (ψ(b_i u_i) - b_i x_i)` of `a ∈ 𝔸ⁿ` with `b ∈ ℚⁿ`. -/
def pairing {n : ℕ} (b : Fin n → ℚ) : An n →+ AddCircle (1 : ℝ) :=
  ∑ i, (pair1 (b i)).comp (Pi.evalAddMonoidHom (fun _ => Adele) i)

theorem pairing_apply {n : ℕ} (b : Fin n → ℚ) (a : An n) :
    pairing b a = ∑ i, pair1 (b i) (a i) := by
  simp [pairing, AddMonoidHom.finsetSum_apply]

theorem continuous_pairing {n : ℕ} (b : Fin n → ℚ) : Continuous (pairing b) := by
  have : (pairing b : An n → AddCircle (1 : ℝ)) = fun a => ∑ i, pair1 (b i) (a i) :=
    funext (pairing_apply b)
  rw [this]
  exact continuous_finsetSum _ fun i _ => (continuous_pair1 (b i)).comp (continuous_apply i)

theorem finChar_add (b b' : ℚ) (u : QHat) : finChar (b + b') u = finChar b u + finChar b' u := by
  simp [finChar, add_smul]

theorem realChar_add (b b' : ℚ) (x : ℝ) : realChar (b + b') x = realChar b x + realChar b' x := by
  simp [realChar, add_mul]

theorem pair1_add (b b' : ℚ) (a : Adele) : pair1 (b + b') a = pair1 b a + pair1 b' a := by
  rw [pair1_apply, pair1_apply, pair1_apply, finChar_add, realChar_add]; abel

/-- The pairing is additive in `b`. -/
theorem pairing_add {n : ℕ} (b b' : Fin n → ℚ) (a : An n) :
    pairing (b + b') a = pairing b a + pairing b' a := by
  simp only [pairing_apply, Pi.add_apply, pair1_add, Finset.sum_add_distrib]

/-- The diagonal embedding `ℚⁿ → 𝔸ⁿ`. -/
def diag {n : ℕ} : (Fin n → ℚ) →+ An n where
  toFun r i := (algebraMap ℚ QHat (r i), (r i : ℝ))
  map_zero' := by ext i <;> simp
  map_add' r s := by ext i <;> simp

theorem diag_apply {n : ℕ} (r : Fin n → ℚ) (i : Fin n) :
    diag r i = (algebraMap ℚ QHat (r i), (r i : ℝ)) := rfl

theorem pair1_diag (b r : ℚ) : pair1 b (algebraMap ℚ QHat r, (r : ℝ)) = 0 := by
  rw [pair1_apply]
  simp only [finChar, realChar, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.mk'_apply, AddMonoidHom.coe_mulLeft, QuotientAddGroup.mk'_apply]
  rw [Algebra.smul_def, ← map_mul, psi_algebraMap]
  push_cast
  exact sub_self _

/-- **The diagonal `ℚⁿ` is isotropic**: `⟪r, b⟫ = 0` for `r, b ∈ ℚⁿ`. -/
theorem pairing_diag {n : ℕ} (b r : Fin n → ℚ) : pairing b (diag r) = 0 := by
  rw [pairing_apply]
  exact Finset.sum_eq_zero fun i _ => pair1_diag (b i) (r i)

end AdelicToriLean
