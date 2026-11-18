import AdelicToriLean.DeltaExistence

/-!
# Lemma `nala-periodic-lca`

For a finite-dimensional protorus `G`, `nala(G) = Hom(ℤ̂, G)` (compact-open topology) is a periodic
LCA group: Hausdorff, locally compact, and every element lies in a compact open subgroup; and
evaluation at `1` is an algebraic isomorphism `nala(G) ≅ td(G)`.

* `isCompact_Kdelta`: `K_Δ` is compact for every closed totally disconnected `Δ`;
* `mem_Kdelta_of_genZ`: `f ∈ K_P` as soon as `f(1) ∈ P`, `P` a closed subgroup;
* `periodic_nala`: every `f ∈ nala(G)` lies in a compact open subgroup `K_P`, with
  `P = q⁻¹⟨q(f 1)⟩` and `q : G → G/Δ`;
* `nala_periodic_lca`: the lemma.
-/

open Topology TensorProduct

noncomputable section

namespace AdelicToriLean

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous homomorphism `ℤ̂ → G` takes values in every closed subgroup containing `f(1)`. -/
theorem mem_Kdelta_of_genZ {P : Subgroup G} (hP : IsClosed (P : Set G)) {f : nala G}
    (hf : f genZ ∈ P) : f ∈ Kdelta P := by
  intro z
  have hc : IsClosed {a : ZHat | f (Multiplicative.ofAdd a) ∈ P} :=
    hP.preimage (f.continuous.comp continuous_ofAdd)
  have hsub : Set.range iZ ⊆ {a : ZHat | f (Multiplicative.ofAdd a) ∈ P} := by
    rintro _ ⟨m, rfl⟩
    show f (Multiplicative.ofAdd (iZ m)) ∈ P
    rw [show Multiplicative.ofAdd (iZ m) = genZ ^ m by simp [genZ, iZ, ← ofAdd_zsmul], map_zpow]
    exact P.zpow_mem hf m
  have : Multiplicative.toAdd z ∈ closure (Set.range iZ) := by
    rw [denseRange_iZ.closure_range]; trivial
  exact hc.closure_subset_iff.mpr hsub this

variable [CompactSpace G] [T2Space G]

/-- `K_P ≅ P` is compact. -/
theorem isCompact_Kdelta {P : Subgroup G} (hc : IsClosed (P : Set G))
    (htd : IsTotallyDisconnected (P : Set G)) : IsCompact (Kdelta P : Set (nala G)) := by
  have : CompactSpace P := isCompact_iff_compactSpace.mp hc.isCompact
  have : CompactSpace (Kdelta P) := (kdeltaEquiv P hc htd).toHomeomorph.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr this

/-- **Periodicity.** Every element of `nala(G)` lies in a compact open subgroup. -/
theorem periodic_nala {Δ : Subgroup G} {n : ℕ} (hΔ : IsDelta Δ n) (f : nala G) :
    ∃ K : Subgroup (nala G), IsOpen (K : Set (nala G)) ∧ IsCompact (K : Set (nala G)) ∧ f ∈ K := by
  obtain ⟨q, hqc, -, -, hq⟩ := hΔ.exists_map
  have hx : f genZ ∈ tdSet G := by rw [← range_expn]; exact ⟨f, rfl⟩
  obtain ⟨k, hk, hxk⟩ := torsion_of_mem_tdSet q hqc hx
  obtain ⟨hPc, hTD⟩ := torsion_preimage hΔ q hqc hq hk hxk
  set P : Subgroup G := (Subgroup.zpowers (q (f genZ))).comap q
  have hΔP : Kdelta Δ ≤ Kdelta P := fun g hg z => by
    show q (g z) ∈ Subgroup.zpowers (q (f genZ))
    rw [(hq _).mpr (hg z)]; exact Subgroup.one_mem _
  exact ⟨Kdelta P, Subgroup.isOpen_mono hΔP (isOpen_Kdelta hΔ), isCompact_Kdelta hPc hTD,
    mem_Kdelta_of_genZ hPc (Subgroup.mem_zpowers _)⟩

theorem locallyCompact_nala {Δ : Subgroup G} {n : ℕ} (hΔ : IsDelta Δ n) :
    LocallyCompactSpace (nala G) :=
  (isCompact_Kdelta hΔ.closed hΔ.td).locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_Kdelta hΔ).mem_nhds (Kdelta Δ).one_mem)

variable (G) [ConnectedSpace G]

/-- **Lemma `nala-periodic-lca`.** For a finite-dimensional protorus `G`, `nala(G) = Hom(ℤ̂, G)`
with the compact-open topology is a periodic LCA group (Hausdorff, locally compact, every element
in a compact open subgroup), and evaluation at `1` is an algebraic isomorphism
`ev_1 : nala(G) ≅ td(G)`. -/
theorem nala_periodic_lca [FiniteDimensional ℚ (ℚ ⊗[ℤ] Additive (PontryaginDual G))] :
    T2Space (nala G) ∧ LocallyCompactSpace (nala G) ∧
      (∀ f : nala G, ∃ K : Subgroup (nala G), IsOpen (K : Set (nala G)) ∧
        IsCompact (K : Set (nala G)) ∧ f ∈ K) ∧
      (∃ e : nala G ≃* td G, ∀ f, (e f : G) = f genZ) := by
  obtain ⟨Δ, hΔ⟩ := exists_delta G
  exact ⟨inferInstance, locallyCompact_nala hΔ, periodic_nala hΔ,
    ⟨expnEquiv G, expnEquiv_apply G⟩⟩

end AdelicToriLean
