import AdelicToriLean.EndRing

/-!
# Additive endomorphisms of `B_K`

* `endo_eq_mul`: every additive endomorphism `f` of the group `B_K` is multiplication by a unique
  `o ∈ 𝓞 K`.
* `endEquiv`: the ring `Module.End ℤ B_K` is isomorphic to `𝓞 K`.
* `quasiIdempotent`: every idempotent quasi-endomorphism of `B_K` is `0` or the identity
  (so `B_K` is strongly indecomposable).
-/

open NumberField nonZeroDivisors

noncomputable section

namespace AdelicToriLean.DegreeOnePrimes

variable {K : Type*} [Field K] [NumberField K] (D : DegreeOnePrimes K)

theorem one_mem_BK : (1 : K) ∈ D.BK := D.OK_le_BK ((D.mem_OK_iff).mpr ⟨1, by simp⟩)

theorem intMul_mem_BK {x : K} (hx : x ∈ D.BK) (n : ℤ) : (n : K) * x ∈ D.BK := by
  have : (n : K) * x = (n : 𝓞 K) • x := by simp [Algebra.smul_def]
  rw [this]; exact Submodule.smul_mem _ _ hx

/-- A chosen nonzero integer `n` with `n x ∈ 𝓞 K`. -/
def den (x : K) : ℤ := Classical.choose (exists_int_mul_mem x)

theorem den_ne_zero (x : K) : den x ≠ 0 := (Classical.choose_spec (exists_int_mul_mem x)).1

theorem den_mul_mem (x : K) : ((den x : K) * x) ∈ D.BK := by
  obtain ⟨o, ho⟩ := (Classical.choose_spec (exists_int_mul_mem x)).2
  rw [den, ← ho]; exact D.OK_le_BK (D.coe_mem_OK o)

variable (f : D.BK →+ D.BK)

/-- The extension of `f` to `K`: `F x = f(n x) / n` for any `n ≠ 0` with `n x ∈ B_K`. -/
def ext (x : K) : K := ((den x : K))⁻¹ * (f ⟨(den x : K) * x, D.den_mul_mem x⟩ : K)

theorem f_intMul (n : ℤ) {y : K} (hy : y ∈ D.BK) :
    (f ⟨(n : K) * y, D.intMul_mem_BK hy n⟩ : K) = (n : K) * (f ⟨y, hy⟩ : K) := by
  have : (⟨(n : K) * y, D.intMul_mem_BK hy n⟩ : D.BK) = n • ⟨y, hy⟩ := by
    ext; simp [zsmul_eq_mul]
  rw [this, map_zsmul]; simp [zsmul_eq_mul]

theorem ext_eq (x : K) (n : ℤ) (hn : n ≠ 0) (hx : (n : K) * x ∈ D.BK) :
    D.ext f x = ((n : K))⁻¹ * (f ⟨(n : K) * x, hx⟩ : K) := by
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
  have hdK : (den x : K) ≠ 0 := by exact_mod_cast den_ne_zero x
  have h1 := D.f_intMul f n (D.den_mul_mem x)
  have h2 := D.f_intMul f (den x) hx
  have e : (⟨(n : K) * ((den x : K) * x), D.intMul_mem_BK (D.den_mul_mem x) n⟩ : D.BK) =
      ⟨(den x : K) * ((n : K) * x), D.intMul_mem_BK hx (den x)⟩ := by ext; simp only; ring
  have key : (n : K) * (f ⟨(den x : K) * x, D.den_mul_mem x⟩ : K) =
      (den x : K) * (f ⟨(n : K) * x, hx⟩ : K) := by
    rw [← h1, ← h2, e]
  rw [ext]
  calc (den x : K)⁻¹ * (f ⟨(den x : K) * x, D.den_mul_mem x⟩ : K)
      = (den x : K)⁻¹ * ((n : K)⁻¹ * ((n : K) * (f ⟨(den x : K) * x, D.den_mul_mem x⟩ : K))) := by
        rw [inv_mul_cancel_left₀ hnK]
    _ = (n : K)⁻¹ * ((den x : K)⁻¹ * ((den x : K) * (f ⟨(n : K) * x, hx⟩ : K))) := by
        rw [key, mul_left_comm]
    _ = _ := by rw [inv_mul_cancel_left₀ hdK]

theorem ext_add (x y : K) : D.ext f (x + y) = D.ext f x + D.ext f y := by
  set n := den x * den y
  have hn : n ≠ 0 := mul_ne_zero (den_ne_zero x) (den_ne_zero y)
  have hx : (n : K) * x ∈ D.BK := by
    have : (n : K) * x = (den y : K) * ((den x : K) * x) := by simp [n]; ring
    rw [this]; exact D.intMul_mem_BK (D.den_mul_mem x) _
  have hy : (n : K) * y ∈ D.BK := by
    have : (n : K) * y = (den x : K) * ((den y : K) * y) := by simp [n]; ring
    rw [this]; exact D.intMul_mem_BK (D.den_mul_mem y) _
  have hxy : (n : K) * (x + y) ∈ D.BK := by rw [mul_add]; exact Submodule.add_mem _ hx hy
  rw [D.ext_eq f _ n hn hxy, D.ext_eq f _ n hn hx, D.ext_eq f _ n hn hy, ← mul_add]
  congr 1
  have : (⟨(n : K) * (x + y), hxy⟩ : D.BK) = ⟨(n : K) * x, hx⟩ + ⟨(n : K) * y, hy⟩ := by
    ext; simp [mul_add]
  rw [this, map_add]; rfl

/-- The extension as a `ℚ`-linear map. -/
def extLin : K →ₗ[ℚ] K :=
  (AddMonoidHom.mk' (D.ext f) (D.ext_add f)).toRatLinearMap

theorem extLin_apply_BK {x : K} (hx : x ∈ D.BK) : D.extLin f x = (f ⟨x, hx⟩ : K) := by
  show D.ext f x = _
  have h1 : ((1 : ℤ) : K) * x ∈ D.BK := by simpa using hx
  rw [D.ext_eq f x 1 one_ne_zero h1]
  simp

/-- **`End_ℤ(B_K) = 𝓞 K`**: every additive endomorphism of `B_K` is multiplication by a unique
element of `𝓞 K`. -/
theorem endo_eq_mul : ∃! o : 𝓞 K, ∀ x : D.BK, (f x : K) = (o : K) * x := by
  have hB : ∀ x ∈ D.BK, D.extLin f x ∈ D.BK := fun x hx => by
    rw [D.extLin_apply_BK f hx]; exact (f ⟨x, hx⟩).2
  obtain ⟨o, ho⟩ := D.linearEnd_eq_mul (D.extLin f) hB
  refine ⟨o, fun x => by rw [← D.extLin_apply_BK f x.2, ho], fun o' ho' => ?_⟩
  have h1 := ho' ⟨1, D.one_mem_BK⟩
  have h2 := ho 1
  rw [D.extLin_apply_BK f D.one_mem_BK] at h2
  simp only [mul_one] at h1 h2
  exact (IsFractionRing.injective (𝓞 K) K) (by
    rw [← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ← h1, h2])

/-- The coefficient of an additive endomorphism. -/
def endCoeff (g : D.BK →+ D.BK) : 𝓞 K := Classical.choose (D.endo_eq_mul g).exists

theorem endCoeff_spec (g : D.BK →+ D.BK) (x : D.BK) : (g x : K) = (D.endCoeff g : K) * x :=
  Classical.choose_spec (D.endo_eq_mul g).exists x

theorem eq_endCoeff (g : D.BK →+ D.BK) {o : 𝓞 K} (ho : ∀ x : D.BK, (g x : K) = (o : K) * x) :
    o = D.endCoeff g :=
  (D.endo_eq_mul g).unique ho (D.endCoeff_spec g)

/-- Multiplication by `o ∈ 𝓞 K` as an endomorphism of `B_K`. -/
def mulEnd (o : 𝓞 K) : Module.End ℤ D.BK :=
  { toFun := fun x => ⟨(o : K) * x, by
      have : (o : K) * x = o • (x : K) := by simp [Algebra.smul_def]
      rw [this]; exact Submodule.smul_mem _ _ x.2⟩
    map_add' := fun x y => by ext; simp [mul_add]
    map_smul' := fun n x => by ext; simp [zsmul_eq_mul]; ring }

theorem spec' (g : Module.End ℤ D.BK) (x : D.BK) : (g x : K) = (D.endCoeff g.toAddMonoidHom : K) * x :=
  D.endCoeff_spec g.toAddMonoidHom x

/-- **`End_ℤ(B_K) ≃+* 𝓞 K`.** -/
def endEquiv : Module.End ℤ D.BK ≃+* 𝓞 K where
  toFun g := D.endCoeff g.toAddMonoidHom
  invFun := D.mulEnd
  left_inv g := by
    ext x
    exact (D.spec' g x).symm
  right_inv o := (D.eq_endCoeff (D.mulEnd o).toAddMonoidHom (fun x => rfl)).symm
  map_mul' f g := by
    refine (D.eq_endCoeff (f * g).toAddMonoidHom (fun x => ?_)).symm
    show ((f (g x)) : K) = _
    rw [D.spec' f (g x), D.spec' g x]; push_cast; ring
  map_add' f g := by
    refine (D.eq_endCoeff (f + g).toAddMonoidHom (fun x => ?_)).symm
    show ((f x + g x : D.BK) : K) = _
    rw [Submodule.coe_add, D.spec' f x, D.spec' g x]; push_cast; ring

/-- **Strong indecomposability**: an idempotent quasi-endomorphism of `B_K` is `0` or the
identity. (`ℚ End(B_K) = K` is a field.) -/
theorem quasiIdempotent (e : K →ₗ[ℚ] K) (n : ℕ) (hn : n ≠ 0)
    (he : ∀ x ∈ D.BK, (n : K) * e x ∈ D.BK) (hidem : e ∘ₗ e = e) : e = 0 ∨ e = LinearMap.id := by
  obtain ⟨α, hα⟩ := D.quasiEnd_eq_mul e n hn he
  have h1 := congrArg (fun F : K →ₗ[ℚ] K => F 1) hidem
  simp only [LinearMap.comp_apply, hα, mul_one] at h1
  have hα2 : α * α = α := h1
  have h0 : α * (α - 1) = 0 := by rw [mul_sub, hα2, mul_one, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · left; ext x; rw [hα, h, zero_mul]; rfl
  · right; ext x; rw [hα, sub_eq_zero.mp h, one_mul]; rfl

end AdelicToriLean.DegreeOnePrimes
