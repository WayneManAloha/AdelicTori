import AdelicToriLean.AdelicModel

/-!
# The adelic torus `(𝔸ⁿ / C) / Λ` realises the dual of a lattice

For a discrete abelian group `D` with an injective `ι : D → ℚⁿ` whose image contains `ℤⁿ`:

* `Cadd ι = {(u, 0) | u ∈ C}` with `C = annC (range ι) ⊆ ℤ̂ⁿ`;
* `Lam ι`: the image of the diagonal `Λ̃ = {(q, q) | q ∈ ℚⁿ}` in `𝔸ⁿ / C`;
* `adelicModelEquiv`: **`(𝔸ⁿ / C) / Λ ≅ D^∨`** as topological groups (the quotient is written
  multiplicatively);
* `compactSpace_adelicTorus`: `(𝔸ⁿ / C) / Λ` is compact.
-/

open IsDedekindDomain Topology

noncomputable section

namespace AdelicToriLean

variable {n : ℕ} {D : Type*} [CommGroup D] [TopologicalSpace D] [DiscreteTopology D]
  (ι : Additive D →+ (Fin n → ℚ))

/-- `C ⊆ 𝔸ⁿ`, embedded as `(u, 0)`. -/
def Cadd : AddSubgroup (An n) := (annC (Set.range ι)).map finPart

/-- `Λ ⊆ 𝔸ⁿ / C`: the image of the diagonal `ℚⁿ`. -/
def Lam : AddSubgroup (An n ⧸ Cadd ι) := (diag (n := n)).range.map (QuotientAddGroup.mk' (Cadd ι))

/-- The adelic torus `(𝔸ⁿ / C) / Λ`. -/
abbrev AdelicTorus := (An n ⧸ Cadd ι) ⧸ Lam ι

/-- `Φ` as an additive map into `Additive (D^∨)`. -/
def PhiAdd : An n →+ Additive (PontryaginDual D) where
  toFun a := Additive.ofMul (Phi ι a)
  map_zero' := by rw [Phi_zero]; rfl
  map_add' a b := by rw [Phi_add]; rfl

theorem Phi_finPart {u : Fin n → QHat} (hu : u ∈ annC (Set.range ι)) : Phi ι (finPart u) = 1 := by
  rw [Phi_eq_one_iff]
  intro d
  rw [pairing_finPart]
  exact (mem_annC.mp hu).2 _ ⟨_, rfl⟩

theorem Cadd_le_ker : Cadd ι ≤ (PhiAdd ι).ker := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hx
  rw [AddMonoidHom.mem_ker]
  show Additive.ofMul (Phi ι (finPart u)) = 0
  rw [Phi_finPart ι hu]; rfl

/-- `Φ` on `𝔸ⁿ / C`. -/
def PhiQ1 : (An n ⧸ Cadd ι) →+ Additive (PontryaginDual D) :=
  QuotientAddGroup.lift _ (PhiAdd ι) (Cadd_le_ker ι)

theorem Lam_le_ker : Lam ι ≤ (PhiQ1 ι).ker := by
  intro x hx
  obtain ⟨_, ⟨r, rfl⟩, rfl⟩ := AddSubgroup.mem_map.mp hx
  rw [AddMonoidHom.mem_ker]
  show Additive.ofMul (Phi ι (diag r)) = 0
  rw [Phi_diag]; rfl

/-- `Φ` on `(𝔸ⁿ / C) / Λ`. -/
def PhiQ : AdelicTorus ι →+ Additive (PontryaginDual D) :=
  QuotientAddGroup.lift _ (PhiQ1 ι) (Lam_le_ker ι)

theorem PhiQ_mk (a : An n) :
    PhiQ ι (QuotientAddGroup.mk (QuotientAddGroup.mk a)) = Additive.ofMul (Phi ι a) := rfl

omit [TopologicalSpace D] [DiscreteTopology D] in
theorem mk_mk_surjective :
    Function.Surjective fun a : An n => (QuotientAddGroup.mk (QuotientAddGroup.mk a :
      An n ⧸ Cadd ι) : AdelicTorus ι) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact ⟨a, rfl⟩

omit [TopologicalSpace D] [DiscreteTopology D] in
theorem continuous_mk_mk :
    Continuous fun a : An n => (QuotientAddGroup.mk (QuotientAddGroup.mk a :
      An n ⧸ Cadd ι) : AdelicTorus ι) :=
  continuous_quot_mk.comp continuous_quot_mk

omit [TopologicalSpace D] [DiscreteTopology D] in
/-- **`(𝔸ⁿ / C) / Λ` is compact**: it is the image of `K = (ℤ̂ × [0, 1])ⁿ`. -/
theorem compactSpace_adelicTorus : CompactSpace (AdelicTorus ι) := by
  refine ⟨?_⟩
  have : (Set.univ : Set (AdelicTorus ι)) =
      (fun a : An n => (QuotientAddGroup.mk (QuotientAddGroup.mk a :
        An n ⧸ Cadd ι) : AdelicTorus ι)) '' Kset n := by
    refine (Set.eq_univ_of_forall fun y => ?_).symm
    obtain ⟨a, rfl⟩ := mk_mk_surjective ι y
    obtain ⟨k, hk, r, rfl⟩ := exists_mem_K_add_diag a
    refine ⟨k, hk, ?_⟩
    have hd : (QuotientAddGroup.mk (QuotientAddGroup.mk (diag r) : An n ⧸ Cadd ι) :
        AdelicTorus ι) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_map.mpr ⟨diag r, ⟨r, rfl⟩, rfl⟩)
    show _ = (QuotientAddGroup.mk (QuotientAddGroup.mk (k + diag r) : An n ⧸ Cadd ι) :
        AdelicTorus ι)
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_add, hd]
    exact (add_zero (QuotientAddGroup.mk (QuotientAddGroup.mk k : An n ⧸ Cadd ι) : AdelicTorus ι)).symm
  rw [this]
  exact (isCompact_Kset n).image (continuous_mk_mk ι)

theorem continuous_PhiQ : Continuous (PhiQ ι) := by
  have h1 : Continuous (PhiQ1 ι) := by
    rw [(QuotientAddGroup.isOpenQuotientMap_mk (N := Cadd ι)).isQuotientMap.continuous_iff]
    exact (continuous_Phi ι).comp continuous_id
  rw [(QuotientAddGroup.isOpenQuotientMap_mk (N := Lam ι)).isQuotientMap.continuous_iff]
  exact h1

theorem PhiQ_injective (hZ : ∀ j : Fin n, Pi.single j 1 ∈ Set.range ι) :
    Function.Injective (PhiQ ι) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨a, rfl⟩ := mk_mk_surjective ι y
  have h1 : Phi ι a = 1 := Additive.ofMul.injective hy
  obtain ⟨u, hu, r, rfl⟩ := (ker_Phi ι hZ a).mp h1
  rw [QuotientAddGroup.eq_zero_iff]
  refine AddSubgroup.mem_map.mpr ⟨diag r, ⟨r, rfl⟩, ?_⟩
  show QuotientAddGroup.mk (diag r) = QuotientAddGroup.mk (finPart u + diag r)
  have hc : (QuotientAddGroup.mk (finPart u) : An n ⧸ Cadd ι) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_map.mpr ⟨u, hu, rfl⟩)
  rw [QuotientAddGroup.mk_add, hc, zero_add]

theorem PhiQ_surjective (hι : Function.Injective ι) : Function.Surjective (PhiQ ι) := by
  intro x
  obtain ⟨a, ha⟩ := Phi_surjective ι hι (Additive.toMul x)
  exact ⟨QuotientAddGroup.mk (QuotientAddGroup.mk a), by rw [PhiQ_mk, ha]; rfl⟩

/-- The multiplicative form of `PhiQ`. -/
def PhiQMul : Multiplicative (AdelicTorus ι) →* PontryaginDual D :=
  AddMonoidHom.toMultiplicativeLeft (PhiQ ι)

/-- **The adelic realisation of the dual of a lattice.** For a discrete group `D` and an injective
`ι : D → ℚⁿ` whose image contains `ℤⁿ`, the adelic torus `(𝔸ⁿ / C) / Λ` is topologically
isomorphic to `D^∨`. -/
def adelicModelEquiv (hι : Function.Injective ι) (hZ : ∀ j : Fin n, Pi.single j 1 ∈ Set.range ι) :
    Multiplicative (AdelicTorus ι) ≃ₜ* PontryaginDual D :=
  haveI := compactSpace_adelicTorus ι
  let e : Multiplicative (AdelicTorus ι) ≃* PontryaginDual D :=
    MulEquiv.ofBijective (PhiQMul ι) ⟨fun x y h => Multiplicative.toAdd.injective
      (PhiQ_injective ι hZ (by
        have h' : Additive.toMul (PhiQ ι (Multiplicative.toAdd x)) =
            Additive.toMul (PhiQ ι (Multiplicative.toAdd y)) := h
        exact Additive.toMul.injective h')),
      fun x => by
        obtain ⟨y, hy⟩ := PhiQ_surjective ι hι (Additive.ofMul x)
        exact ⟨Multiplicative.ofAdd y, by simp [PhiQMul, hy]⟩⟩
  have hc : Continuous e := (continuous_PhiQ ι)
  let h := hc.homeoOfEquivCompactToT2 (f := e.toEquiv)
  { e with
    continuous_toFun := hc
    continuous_invFun := h.symm.continuous }

theorem adelicModelEquiv_apply (hι : Function.Injective ι)
    (hZ : ∀ j : Fin n, Pi.single j 1 ∈ Set.range ι) (a : An n) :
    adelicModelEquiv ι hι hZ (Multiplicative.ofAdd (QuotientAddGroup.mk (QuotientAddGroup.mk a))) =
      Phi ι a := rfl

end AdelicToriLean
