import AdelicToriLean.TopCharacterisation
import AdelicToriLean.Fdccg

/-!
# Every finite-dimensional protorus has a delta-subgroup

Let `G` be a protorus with `n = dim_a G = rk G^∨ < ∞`. Choose `ι : G^∨ → ℚⁿ` injective with
`ℤⁿ ⊆ ι(G^∨)` (`exists_rank_embedding`), and characters `d_j` with `ι(d_j) = e_j`. Then
`q : G → (ℝ/ℤ)ⁿ`, `q(g) = (d_j(g))_j`, is a continuous surjective homomorphism
(`q_surjective`, via the adelic characters `Φ_ι(a)` and double duality), and `Δ = ker q`:

* is totally disconnected: for every character `ψ`, some `ψ^m` lies in `⟨d_j⟩`, so `ψ` maps `Δ`
  into the finite set of `m`-th roots of unity;
* satisfies `G/Δ ≅ (ℝ/ℤ)ⁿ` (compact to Hausdorff).

`exists_delta`: `G` has a delta-subgroup, `IsDelta Δ (dim_a G)`.
-/

open Topology TensorProduct Real

noncomputable section

namespace AdelicToriLean

/-- Clearing denominators in `ℚⁿ`. -/
theorem exists_int_multiple {n : ℕ} (v : Fin n → ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ k : Fin n → ℤ, ∀ j, (m : ℚ) * v j = k j := by
  refine ⟨∏ j, (v j).den, Finset.prod_pos fun j _ => (v j).den_pos,
    fun j => (v j).num * (((∏ i, (v i).den) / (v j).den : ℕ) : ℤ), fun j => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun i => (v i).den) (Finset.mem_univ j)
  show ((∏ i, (v i).den : ℕ) : ℚ) * v j = (((v j).num * ((∏ i, (v i).den) / (v j).den : ℕ) : ℤ) : ℚ)
  rw [hc, Nat.mul_div_cancel_left _ (v j).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

/-- The `m`-th roots of unity in the circle form a finite set. -/
theorem finite_roots_circle {m : ℕ} (hm : 0 < m) : {z : Circle | z ^ m = 1}.Finite := by
  refine (((Polynomial.nthRoots m (1 : ℂ)).toFinset.finite_toSet).preimage
    (Set.injOn_of_injective Subtype.val_injective)).subset ?_
  intro z hz
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset,
    Polynomial.mem_nthRoots hm]
  have := congrArg (fun w : Circle => (w : ℂ)) (show z ^ m = 1 from hz)
  simpa using this

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [ConnectedSpace G] [T2Space G]

/-- **Existence of delta-subgroups.** A finite-dimensional protorus `G` has a delta-subgroup
`Δ`, `G/Δ ≅ (ℝ/ℤ)ⁿ` with `n = dim_a G`. -/
theorem exists_delta [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    ∃ Δ : Subgroup G, IsDelta Δ (dimA G) := by
  have : DiscreteTopology (PontryaginDual G) := discreteTopology_dual
  obtain ⟨ι, hι, hZ⟩ := exists_rank_embedding (dual_additive_torsionFree G)
  choose d hd using hZ
  set χ : Fin (dimA G) → PontryaginDual G := fun j => Additive.toMul (d j)
  set q : G →* Torus (dimA G) :=
    { toFun := fun x j => χ j x
      map_one' := by funext j; exact map_one (χ j)
      map_mul' := fun x y => by funext j; exact map_mul (χ j) x y }
  have hqc : Continuous q := continuous_pi fun j => (χ j).continuous
  -- `q` is surjective
  have hqs : Function.Surjective q := by
    intro t
    have hx : ∀ j, ∃ x : ℝ, AddCircle.toCircle (x : AddCircle (1 : ℝ)) = t j := fun j => by
      obtain ⟨θ, hθ⟩ := Circle.exp_surjective (t j)
      refine ⟨θ / (2 * π), ?_⟩
      rw [AddCircle.toCircle_apply_mk, ← hθ]
      congr 1
      field_simp
    choose x hx using hx
    set a : An (dimA G) := ∑ j, Pi.single j ((0 : QHat), -x j)
    obtain ⟨g, hg⟩ := (PontryaginDual.toDoubleDual G).surjective (Phi ι a)
    refine ⟨g, funext fun j => ?_⟩
    show χ j g = t j
    have h1 : (PontryaginDual.toDoubleDual G g) (χ j) = χ j g := rfl
    have hp : pairing (Pi.single j (1 : ℚ)) a = (x j : AddCircle (1 : ℝ)) := by
      simp only [a, map_sum, pairing_realSingle]
      rw [Finset.sum_eq_single j]
      · simp [realChar]
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij, realChar]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [← h1, hg, Phi_apply]
    show AddCircle.toCircle (pairing (ι (d j)) a) = t j
    rw [hd j, hp, hx j]
  set Δ : Subgroup G := q.ker
  have hΔc : IsClosed (Δ : Set G) := isClosed_singleton.preimage hqc
  -- `Δ` is totally disconnected
  have hTD : IsTotallyDisconnected (Δ : Set G) := by
    suffices TotallySeparatedSpace Δ from totallyDisconnectedSpace_subtype_iff.mp inferInstance
    rw [totallySeparatedSpace_iff_exists_isClopen]
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    obtain ⟨ψ, hψ⟩ : ∃ ψ : PontryaginDual G, ψ a ≠ ψ b := by
      by_contra h
      simp only [not_exists, not_not] at h
      apply hab
      apply Subtype.ext
      apply (PontryaginDual.toDoubleDual G).injective
      ext ψ
      exact congrArg Subtype.val (h ψ)
    obtain ⟨m, hm, k, hk⟩ := exists_int_multiple (ι (Additive.ofMul ψ))
    have hrel : m • Additive.ofMul ψ = ∑ j, k j • d j := hι (by
      rw [map_nsmul, map_sum]
      funext i
      simp [Finset.sum_apply, hd, Pi.single_apply, nsmul_eq_mul, hk])
    have hroot : ∀ y ∈ Δ, ψ y ^ m = 1 := by
      intro y hy
      let ev : Additive (PontryaginDual G) →+ Additive Circle :=
        { toFun := fun c => Additive.ofMul (Additive.toMul c y)
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have h := congrArg ev hrel
      rw [map_nsmul, map_sum] at h
      have h0 : ∀ j, ev (d j) = 0 := fun j => by
        show Additive.ofMul (χ j y) = 0
        rw [show χ j y = q y j from rfl, (MonoidHom.mem_ker).mp hy]; rfl
      simp only [map_zsmul, h0, smul_zero, Finset.sum_const_zero] at h
      have := congrArg Additive.toMul h
      rw [toMul_nsmul, toMul_zero] at this
      exact this
    set f : Δ → Circle := fun y => ψ y
    have hfc : Continuous f := ψ.continuous.comp continuous_subtype_val
    have hS := finite_roots_circle hm
    set U : Set Δ := f ⁻¹' {ψ a}
    have hUc : IsClosed U := isClosed_singleton.preimage hfc
    have hUcompl : Uᶜ = f ⁻¹' ({z : Circle | z ^ m = 1} \ {ψ a}) := by
      ext y
      simp only [U, Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]
      exact ⟨fun h => ⟨hroot y y.2, h⟩, fun h => h.2⟩
    refine ⟨U, ⟨hUc, ?_⟩, rfl, ?_⟩
    · rw [← isClosed_compl_iff, hUcompl]
      exact (hS.sdiff).isClosed.preimage hfc
    · show f ⟨b, hb⟩ ∉ ({ψ a} : Set Circle)
      exact fun h => hψ (h.symm)
  -- `G/Δ ≅ (ℝ/ℤ)ⁿ`
  set e0 : G ⧸ Δ ≃* Torus (dimA G) := QuotientGroup.quotientKerEquivOfSurjective q hqs
  have hcont : Continuous e0 :=
    (QuotientGroup.isQuotientMap_mk Δ).continuous_iff.mpr hqc
  set hom := hcont.homeoOfEquivCompactToT2 (f := e0.toEquiv)
  exact ⟨Δ, ⟨hΔc, hTD, ⟨{ e0 with
    continuous_toFun := hcont
    continuous_invFun := hom.symm.continuous }⟩⟩⟩

/-- **Topological characterisation, unconditional form.** For a nontrivial finite-dimensional
protorus `G`, `td(G)` is not locally compact and `exp_n : nala(G) → td(G)` is not open. -/
theorem topological_characterisation_of_fd [Nontrivial G]
    [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    ¬ LocallyCompactSpace (td G) ∧ ¬ IsOpenMap (expnEquiv G) := by
  obtain ⟨Δ, hΔ⟩ := exists_delta G
  exact ⟨not_locallyCompact_td hΔ, not_isOpenMap_expn hΔ⟩

end AdelicToriLean
