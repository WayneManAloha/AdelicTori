import AdelicToriLean.NalaPeriodic

/-!
# Divisibility of `nala(G)` and the adelic exponential

* `pow_surjective`: a compact connected abelian group is divisible (its dual is torsion-free);
* `tdSet_divisible`: `td(G)` is divisible;
* `nala_divisible`: `nala(G)` is divisible (transport through `exp_n`);
* `expa : arla(G) → G`, `g ↦ g(1)`; `expAd : adla(G) → G`, `f ↦ f(1, 1)` (the adelic exponential),
  continuous, with `expAd f = exp_n(f|ℤ̂) · exp_a(f|ℝ)` (`expAd_eq`).
-/

open Topology TensorProduct

noncomputable section

namespace AdelicToriLean

section Divisible

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [ConnectedSpace G]

/-- **A compact connected abelian group is divisible.** -/
theorem pow_surjective {n : ℕ} (hn : 0 < n) : Function.Surjective (fun x : G => x ^ n) := by
  intro x
  set H : Subgroup G := (powMonoidHom n : G →* G).range
  have hHset : (H : Set G) = Set.range (fun y : G => y ^ n) := by ext; simp [H]
  have hHc : IsClosed (H : Set G) := by
    rw [hHset]; exact (_root_.isCompact_range (continuous_pow n)).isClosed
  by_contra hx
  have hxH : x ∉ H := by
    intro h
    rw [← SetLike.mem_coe, hHset] at h
    exact hx h
  have : IsClosed (H : Set G) := hHc
  have hne : (x : G ⧸ H) ≠ 1 := by rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : PontryaginDual (G ⧸ H), ψ x ≠ 1 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hne
    apply PontryaginDual.eval_injective (G ⧸ H)
    ext ψ
    simp [PontryaginDual.eval_apply, h ψ]
  set χ : PontryaginDual G := ψ.comp ⟨QuotientGroup.mk' H, continuous_quot_mk⟩
  have hχ : χ ^ n = 1 := by
    refine ContinuousMonoidHom.ext fun y => ?_
    erw [ContinuousMonoidHom.pow_apply, ← map_pow, PontryaginDual.one_apply]
    show ψ ((y ^ n : G) : G ⧸ H) = 1
    have hy : y ^ n ∈ H := ⟨y, rfl⟩
    rw [(QuotientGroup.eq_one_iff _).mpr hy, map_one]
  exact hψ (by
    have := DFunLike.congr_fun (dual_torsionFree χ hn hχ) x
    rw [PontryaginDual.one_apply] at this
    exact this)

/-- Roots of elements of `td(G)` stay in `td(G)`: **`td(G)` is divisible.** -/
theorem tdSet_divisible {Δ : Subgroup G} {k : ℕ} (hΔ : IsDelta Δ k) {x : G} (hx : x ∈ tdSet G)
    {n : ℕ} (hn : 0 < n) : ∃ y ∈ tdSet G, y ^ n = x := by
  obtain ⟨q, hqc, -, -, hq⟩ := hΔ.exists_map
  obtain ⟨y, hy⟩ := pow_surjective hn x
  obtain ⟨m, hm, hxm⟩ := torsion_of_mem_tdSet q hqc hx
  refine ⟨y, mem_tdSet_of_torsion hΔ q hqc hq (Nat.mul_pos hn hm) ?_, hy⟩
  rw [pow_mul, ← map_pow, show y ^ n = x from hy, hxm]

/-- **`nala(G)` is divisible.** -/
theorem nala_divisible {Δ : Subgroup G} {k : ℕ} (hΔ : IsDelta Δ k) (f : nala G) {n : ℕ}
    (hn : 0 < n) : ∃ g : nala G, g ^ n = f := by
  have hx : f genZ ∈ tdSet G := by rw [← range_expn]; exact ⟨f, rfl⟩
  obtain ⟨y, hyt, hy⟩ := tdSet_divisible hΔ hx hn
  set g := (expnEquiv G).symm ⟨y, (mem_td_iff G).mpr hyt⟩
  refine ⟨g, (expnEquiv G).injective (Subtype.ext ?_)⟩
  rw [map_pow, Subgroup.coe_pow, MulEquiv.apply_symm_apply, expnEquiv_apply]
  exact hy

end Divisible

section Exponential

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The generator `(1, 1)` of `𝔸_ℤ = ℤ̂ × ℝ`. -/
abbrev genAZ : Multiplicative AZ := Multiplicative.ofAdd (oneZ, 1)

/-- **The archimedean exponential** `exp_a(g) = g(1)`. -/
def expa : arla G →* G where
  toFun g := g (Multiplicative.ofAdd 1)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The adelic exponential** `exp(f) = f(1, 1)`. -/
def expAd : adla G →* G where
  toFun f := f (genAZ)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_expa : Continuous (expa G) :=
  continuous_eval_const (F := arla G) (Multiplicative.ofAdd 1)

theorem continuous_expAd : Continuous (expAd G) :=
  continuous_eval_const (F := adla G) genAZ

/-- Under `adla(G) ≅ nala(G) × arla(G)`, `exp(f) = exp_n(f|ℤ̂) · exp_a(f|ℝ)`. -/
theorem expAd_eq (f : adla G) :
    expAd G f = expn G (adlaEquiv G f).1 * expa G (adlaEquiv G f).2 := by
  rw [adlaEquiv_apply]
  show f genAZ = f (Multiplicative.ofAdd (oneZ, 0)) * f (Multiplicative.ofAdd (0, 1))
  rw [← map_mul, ← ofAdd_add]
  congr 2
  simp

end Exponential

end AdelicToriLean
