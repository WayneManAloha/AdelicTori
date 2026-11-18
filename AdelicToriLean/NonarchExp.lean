import AdelicToriLean.ZHatAction

/-!
# The nonarchimedean exponential `exp_n : nala(G) → td(G)`

For a commutative Hausdorff topological group `G`:

* `tdSet G`: the union of the compact totally disconnected subgroups of `G`;
* `expn G : nala G →* G`, `f ↦ f 1`: continuous (`continuous_expn`) and injective (`expn_injective`);
* `range_expn`: the image of `expn` is `tdSet G`; so `td G := (expn G).range` is a subgroup with
  `td G = tdSet G` (`mem_td_iff`);
* `map_td_le`: `td` is functorial for continuous homomorphisms, in particular fully invariant;
* `expnEquiv : nala G ≃* td G`, a continuous algebraic isomorphism.
-/

open Topology

noncomputable section

namespace AdelicToriLean

instance : CompactSpace (Multiplicative ZHat) := inferInstanceAs (CompactSpace ZHat)

instance : TotallyDisconnectedSpace (Multiplicative ZHat) :=
  inferInstanceAs (TotallyDisconnectedSpace ZHat)

instance : T2Space (Multiplicative ZHat) := inferInstanceAs (T2Space ZHat)

/-- The generator `1 ∈ ℤ̂`, written multiplicatively. -/
abbrev genZ : Multiplicative ZHat := Multiplicative.ofAdd oneZ

section Image

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

omit [IsTopologicalGroup G] in
/-- **The image of `ℤ̂` is profinite.** The range of a continuous homomorphism `ℤ̂ → G` is a
compact totally disconnected subgroup. -/
theorem range_totallyDisconnected (f : ContinuousMonoidHom (Multiplicative ZHat) G) :
    TotallyDisconnectedSpace ((f : Multiplicative ZHat →* G).range) := by
  set M := Multiplicative ZHat
  set C := (f : M →* G).range
  set K : Subgroup M := (f : M →* G).ker
  have hKc : IsClosed (K : Set M) := by
    have : (K : Set M) = f ⁻¹' {1} := by ext m; simp [K]
    rw [this]; exact isClosed_singleton.preimage f.continuous
  -- separating open subgroups
  have hsep : ∀ z : M, z ∉ K → ∃ U : Subgroup M, IsOpen (U : Set M) ∧ K ≤ U ∧ z ∉ U := by
    intro z hz
    have h := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := M) ⟨K, hKc⟩
    have hz' : z ∉ sInf {N : Subgroup M | IsOpen (N : Set M) ∧ K ≤ N} := by
      rw [← h]; exact hz
    rw [Subgroup.mem_sInf] at hz'
    obtain ⟨N, ⟨hNo, hKN⟩, hzN⟩ := not_forall₂.mp hz'
    exact ⟨N, hNo, hKN, hzN⟩
  have : TotallySeparatedSpace C := by
    rw [totallySeparatedSpace_iff_exists_isClopen]
    rintro ⟨_, za, rfl⟩ ⟨_, zb, rfl⟩ hab
    have hz : za⁻¹ * zb ∉ K := by
      intro hk
      apply hab
      apply Subtype.ext
      have : f (za⁻¹ * zb) = 1 := hk
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this
    obtain ⟨U, hUo, hKU, hzU⟩ := hsep _ hz
    have hUc : IsClosed (U : Set M) := Subgroup.isClosed_of_isOpen U hUo
    set V : Set M := {m | za⁻¹ * m ∈ U}
    have hVc : IsClosed V := hUc.preimage (continuous_const_mul za⁻¹)
    have hVo : IsOpen V := hUo.preimage (continuous_const_mul za⁻¹)
    have hfV : IsClosed (f '' V) := (hVc.isCompact.image f.continuous).isClosed
    have hfVc : IsClosed (f '' Vᶜ) := (hVo.isClosed_compl.isCompact.image f.continuous).isClosed
    -- inside `C`, the complement of `f '' V` is `f '' Vᶜ`
    have hcompl : ((Subtype.val : C → G) ⁻¹' (f '' V))ᶜ = (Subtype.val : C → G) ⁻¹' (f '' Vᶜ) := by
      ext ⟨_, m, rfl⟩
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_image]
      constructor
      · intro h
        exact ⟨m, fun hm => h ⟨m, hm, rfl⟩, rfl⟩
      · rintro ⟨m', hm', he⟩ ⟨m'', hm'', he'⟩
        apply hm'
        have hk : m''⁻¹ * m' ∈ K := by
          show f (m''⁻¹ * m') = 1
          rw [map_mul, map_inv, inv_mul_eq_one]
          exact he'.trans he.symm
        have := U.mul_mem hm'' (hKU hk)
        show za⁻¹ * m' ∈ U
        convert this using 1
        group
    refine ⟨(Subtype.val : C → G) ⁻¹' (f '' V), ⟨hfV.preimage continuous_subtype_val, ?_⟩,
      ⟨za, show za⁻¹ * za ∈ U by rw [inv_mul_cancel]; exact U.one_mem, rfl⟩, ?_⟩
    · rw [← isClosed_compl_iff, hcompl]
      exact hfVc.preimage continuous_subtype_val
    · rw [hcompl]
      exact ⟨zb, fun h => hzU h, rfl⟩
  infer_instance

omit [IsTopologicalGroup G] [T2Space G] in
theorem isCompact_range (f : ContinuousMonoidHom (Multiplicative ZHat) G) :
    IsCompact (((f : Multiplicative ZHat →* G).range : Subgroup G) : Set G) := by
  have : (((f : Multiplicative ZHat →* G).range : Subgroup G) : Set G) = Set.range f := by
    ext; simp
  rw [this]; exact _root_.isCompact_range f.continuous

end Image

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The union of the compact totally disconnected subgroups of `G`. -/
def tdSet : Set G :=
  {x | ∃ C : Subgroup G, IsCompact (C : Set G) ∧ TotallyDisconnectedSpace C ∧ x ∈ C}

/-- **The nonarchimedean exponential** `exp_n(f) = f(1)`. -/
def expn : nala G →* G where
  toFun f := f genZ
  map_one' := rfl
  map_mul' _ _ := rfl

theorem expn_apply (f : nala G) : expn G f = f genZ := rfl

theorem continuous_expn : Continuous (expn G) :=
  continuous_eval_const (F := nala G) genZ

theorem expn_injective [T2Space G] : Function.Injective (expn G) :=
  fun _ _ h => zhatHom_ext h

/-- **The image of `exp_n` is the union of the compact totally disconnected subgroups.** -/
theorem range_expn [T2Space G] : Set.range (expn G) = tdSet G := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨(f : Multiplicative ZHat →* G).range, isCompact_range f,
      range_totallyDisconnected f, genZ, rfl⟩
  · rintro ⟨C, hC, hTD, hx⟩
    have : CompactSpace C := isCompact_iff_compactSpace.mp hC
    obtain ⟨f, hf⟩ := exists_zhatHom (P := C) ⟨x, hx⟩
    refine ⟨(⟨C.subtype, continuous_subtype_val⟩ : ContinuousMonoidHom C G).comp f, ?_⟩
    show ((f genZ : C) : G) = x
    rw [hf]

/-- `td(G)`: the image of `exp_n`, a subgroup. -/
def td : Subgroup G := (expn G).range

theorem mem_td_iff [T2Space G] {x : G} : x ∈ td G ↔ x ∈ tdSet G := by
  rw [← range_expn]; rfl

/-- **`td` is functorial**: continuous homomorphisms map `td` into `td`. In particular `td(G)` is a
fully invariant subgroup. -/
theorem map_td_le {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : ContinuousMonoidHom G H) : (td G).map (φ : G →* H) ≤ td H := by
  rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
  exact ⟨φ.comp f, rfl⟩

theorem td_fullyInvariant (φ : ContinuousMonoidHom G G) :
    (td G).map (φ : G →* G) ≤ td G :=
  map_td_le G φ

/-- `exp_n` as an algebraic isomorphism `nala(G) ≃* td(G)`. -/
def expnEquiv [T2Space G] : nala G ≃* td G := MonoidHom.ofInjective (expn_injective G)

theorem expnEquiv_apply [T2Space G] (f : nala G) : (expnEquiv G f : G) = f genZ := rfl

theorem continuous_expnEquiv [T2Space G] : Continuous (expnEquiv G) :=
  (continuous_expn G).subtype_mk _

/-- **`exp_n` is a continuous algebraic isomorphism onto `td(G)`**, and `td(G)` is the union of the
compact totally disconnected subgroups of `G`. -/
theorem nonarchimedean_exponential [T2Space G] :
    Continuous (expn G) ∧ Function.Injective (expn G) ∧ Set.range (expn G) = tdSet G :=
  ⟨continuous_expn G, expn_injective G, range_expn G⟩

end AdelicToriLean
