import AdelicToriLean.AdelicTorus
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Properties of `C` and `Λ` in the adelic torus `(𝔸ⁿ / C) / Λ`

The statement of Theorem `fdccg-adelic-tori` asserts that `C` is a torsion-free profinite subgroup
of `𝔸ⁿ` and that `Λ ≅ ℚⁿ` is discrete and cocompact in `𝔸ⁿ / C`. Each is a separate declaration:

* `Cadd_le`: `C ⊆ ℤ̂ⁿ × {0}`;
* `isCompact_Cadd`: `C` is compact;
* `totallyDisconnected_Cadd`: `C` is totally disconnected (so, with compactness, profinite);
* `An_torsionFree`: `𝔸ⁿ` is torsion-free (so `C` is);
* `diag_mem_Cadd_iff`: `Λ̃ ∩ C = 0`;
* `lamEquiv`: `Λ ≅ ℚⁿ`;
* `discreteTopology_Lam`: `Λ` is discrete in `𝔸ⁿ / C`;
* `compactSpace_adelicTorus` (in `AdelicTorus.lean`): `Λ` is cocompact.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum Topology

noncomputable section

namespace AdelicToriLean

variable {n : ℕ} {D : Type*} [CommGroup D] [TopologicalSpace D] [DiscreteTopology D]
  (ι : Additive D →+ (Fin n → ℚ))

omit [TopologicalSpace D] [DiscreteTopology D] in
/-- `C ⊆ ℤ̂ⁿ × {0}`. -/
theorem Cadd_le {a : An n} (ha : a ∈ Cadd ι) : ∀ i, (a i).1 ∈ ZHat ∧ (a i).2 = 0 := by
  obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp ha
  exact fun i => ⟨(mem_annC.mp hu).1 i, rfl⟩

theorem isClosed_ZHat : IsClosed (ZHat : Set QHat) :=
  AddSubgroup.isClosed_of_isOpen _ isOpen_ZHat

omit [TopologicalSpace D] [DiscreteTopology D] in
theorem isClosed_annC : IsClosed (annC (Set.range ι) : Set (Fin n → QHat)) := by
  have h1 : IsClosed {u : Fin n → QHat | ∀ i, u i ∈ ZHat} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_ZHat.preimage (continuous_apply i)
  have h2 : IsClosed {u : Fin n → QHat |
      ∀ b ∈ Set.range ι, ∑ i, finChar (b i) (u i) = 0} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun b => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact continuous_finsetSum _ fun i _ => (continuous_finChar (b i)).comp (continuous_apply i)
  have : (annC (Set.range ι) : Set (Fin n → QHat)) =
      {u | ∀ i, u i ∈ ZHat} ∩ {u | ∀ b ∈ Set.range ι, ∑ i, finChar (b i) (u i) = 0} := by
    ext u; exact mem_annC
  rw [this]; exact h1.inter h2

omit [TopologicalSpace D] [DiscreteTopology D] in
/-- **`C` is compact.** -/
theorem isCompact_Cadd : IsCompact (Cadd ι : Set (An n)) := by
  have hcpt : IsCompact (annC (Set.range ι) : Set (Fin n → QHat)) := by
    refine (isCompact_univ_pi fun _ => isCompact_ZHat).of_isClosed_subset (isClosed_annC ι) ?_
    intro u hu i _
    exact (mem_annC.mp hu).1 i
  have hcont : Continuous (finPart (n := n)) :=
    continuous_pi fun i => (continuous_apply i).prodMk continuous_const
  have : (Cadd ι : Set (An n)) = finPart '' (annC (Set.range ι) : Set (Fin n → QHat)) := by
    ext a; exact AddSubgroup.mem_map
  rw [this]
  exact hcpt.image hcont

/-- A space with a continuous injection into a totally disconnected space is totally
disconnected. -/
theorem totallyDisconnected_of_injective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f) (hinj : Function.Injective f) :
    TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs => ?_⟩
  have h := isTotallyDisconnected_of_totallyDisconnectedSpace (f '' s) (f '' s) subset_rfl
    (hs.image f hf.continuousOn)
  intro x hx y hy
  exact hinj (h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

instance (v : HeightOneSpectrum ℤ) : TotallyDisconnectedSpace (v.adicCompletion ℚ) :=
  totallyDisconnected_of_injective (adicCompletion.padicEquiv v).continuous
    (adicCompletion.padicEquiv v).injective

/-- `ℚ̂` is totally disconnected. -/
instance : TotallyDisconnectedSpace QHat :=
  totallyDisconnected_of_injective
    (RestrictedProduct.continuous_coe (R := fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
      (A := fun v => (v.adicCompletionIntegers ℚ)) (𝓕 := Filter.cofinite))
    (fun _ _ h => Subtype.ext h)

omit [TopologicalSpace D] [DiscreteTopology D] in
/-- **`C` is totally disconnected** (with `isCompact_Cadd`: `C` is profinite). -/
theorem totallyDisconnected_Cadd : TotallyDisconnectedSpace (Cadd ι) := by
  refine totallyDisconnected_of_injective (f := fun c : Cadd ι => fun i => ((c : An n) i).1)
    (continuous_pi fun i => continuous_fst.comp ((continuous_apply i).comp continuous_subtype_val))
    ?_
  intro c c' h
  apply Subtype.ext
  funext i
  refine Prod.ext (congrFun h i) ?_
  rw [(Cadd_le ι c.2 i).2, (Cadd_le ι c'.2 i).2]

/-- **`𝔸ⁿ` is torsion-free** (hence so is `C`): `ℚ̂` and `ℝ` are `ℚ`-vector spaces. -/
theorem An_torsionFree {m : ℕ} (hm : 0 < m) {a : An n} (h : m • a = 0) : a = 0 := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, Pi.zero_apply] at hi
  refine Prod.ext ?_ ?_
  · have h1 : (m : ℚ) • (a i).1 = 0 := by
      rw [show (m : ℚ) • (a i).1 = m • (a i).1 by norm_cast]; exact congrArg Prod.fst hi
    simpa [hm'] using h1
  · have h2 : (m : ℝ) * (a i).2 = 0 := by
      rw [← nsmul_eq_mul]; exact congrArg Prod.snd hi
    simpa [show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne'] using h2

omit [TopologicalSpace D] [DiscreteTopology D] in
/-- `Λ̃ ∩ C = 0`. -/
theorem diag_mem_Cadd_iff (r : Fin n → ℚ) : diag r ∈ Cadd ι ↔ r = 0 := by
  constructor
  · intro h
    funext i
    have := (Cadd_le ι h i).2
    simp only [diag_apply] at this
    rw [Pi.zero_apply]
    exact_mod_cast this
  · rintro rfl; rw [map_zero]; exact (Cadd ι).zero_mem

/-- The map `ℚⁿ → Λ`, `r ↦ (r, r) + C`. -/
def toLam : (Fin n → ℚ) →+ Lam ι :=
  AddMonoidHom.codRestrict ((QuotientAddGroup.mk' (Cadd ι)).comp diag) (Lam ι)
    fun r => AddSubgroup.mem_map.mpr ⟨diag r, ⟨r, rfl⟩, rfl⟩

omit [TopologicalSpace D] [DiscreteTopology D] in
theorem toLam_bijective : Function.Bijective (toLam ι) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have h : (QuotientAddGroup.mk (diag r) : An n ⧸ Cadd ι) = 0 := congrArg Subtype.val hr
    exact (diag_mem_Cadd_iff ι r).mp ((QuotientAddGroup.eq_zero_iff _).mp h)
  · rintro ⟨x, hx⟩
    obtain ⟨_, ⟨r, rfl⟩, rfl⟩ := AddSubgroup.mem_map.mp hx
    exact ⟨r, rfl⟩

/-- **`Λ ≅ ℚⁿ`.** -/
def lamEquiv : (Fin n → ℚ) ≃+ Lam ι := AddEquiv.ofBijective (toLam ι) (toLam_bijective ι)

/-- A rational in `ℤ̂` is an integer. -/
theorem rat_mem_ZHat {r : ℚ} (h : algebraMap ℚ QHat r ∈ ZHat) : r.den = 1 := by
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact q.Prime := ⟨hq⟩
  set v := (primesEquiv (R := ℤ)).symm ⟨q, hq⟩
  have hv := (mem_ZHat.mp h) v
  rw [show (algebraMap ℚ QHat r) v = algebraMap ℚ (v.adicCompletion ℚ) r from rfl,
    rat_mem_integers_iff] at hv
  have hpv : (primesEquiv v : ℕ) = q :=
    congrArg Subtype.val ((primesEquiv (R := ℤ)).apply_symm_apply ⟨q, hq⟩)
  exact not_dvd_den_of_norm_le (primesEquiv v) hv (hpv ▸ hqd)

omit [TopologicalSpace D] [DiscreteTopology D] in
/-- **`Λ` is discrete in `𝔸ⁿ / C`.** -/
theorem discreteTopology_Lam : DiscreteTopology (Lam ι) := by
  -- the open set `V = (ℤ̂ × (-1/2, 1/2))ⁿ`
  set V : Set (An n) := Set.univ.pi fun _ => (ZHat : Set QHat) ×ˢ Set.Ioo (-(1 / 2) : ℝ) (1 / 2)
  have hV : IsOpen V :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_ZHat.prod isOpen_Ioo
  have hU : IsOpen ((QuotientAddGroup.mk : An n → An n ⧸ Cadd ι) '' V) :=
    QuotientAddGroup.isOpenMap_coe (N := Cadd ι) V hV
  apply discreteTopology_of_isOpen_singleton_zero
  have hpre : IsOpen ((Subtype.val : Lam ι → An n ⧸ Cadd ι) ⁻¹'
      ((QuotientAddGroup.mk : An n → An n ⧸ Cadd ι) '' V)) :=
    hU.preimage continuous_subtype_val
  convert hpre using 1
  ext ⟨x, hx⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_image]
  obtain ⟨_, ⟨r, rfl⟩, rfl⟩ := AddSubgroup.mem_map.mp hx
  constructor
  · intro h0
    refine ⟨0, fun i _ => ⟨ZHat.zero_mem, by norm_num, by norm_num⟩, ?_⟩
    have := congrArg Subtype.val h0
    simpa using this.symm
  · rintro ⟨v, hv, hvr⟩
    have hc : diag r - v ∈ Cadd ι := by
      rw [← QuotientAddGroup.eq_iff_sub_mem]
      exact hvr.symm
    have hr : r = 0 := by
      funext i
      have h1 := Cadd_le ι hc i
      have hvi := hv i (Set.mem_univ i)
      simp only [Pi.sub_apply, Prod.fst_sub, Prod.snd_sub, diag_apply] at h1
      -- the real part: `r_i = (v i).2 ∈ (-1/2, 1/2)`
      have hreal : (r i : ℝ) = (v i).2 := sub_eq_zero.mp h1.2
      -- the finite part: `r_i ∈ ℤ̂`, hence an integer
      have hfin : algebraMap ℚ QHat (r i) ∈ ZHat := by
        have := ZHat.add_mem h1.1 hvi.1
        simpa using this
      have hden := rat_mem_ZHat hfin
      have hint : (r i : ℝ) = ((r i).num : ℝ) := by
        exact_mod_cast (Rat.coe_int_num_of_den_eq_one hden).symm
      have hlt : |((r i).num : ℝ)| < 1 / 2 := by
        rw [← hint, hreal, abs_lt]; exact ⟨hvi.2.1, hvi.2.2⟩
      have hnum : (r i).num = 0 := by
        have : |(r i).num| < 1 := by
          have : (|(r i).num| : ℝ) < 1 := by
            linarith
          exact_mod_cast this
        exact Int.abs_lt_one_iff.mp this
      rw [Pi.zero_apply, ← Rat.coe_int_num_of_den_eq_one hden, hnum, Int.cast_zero]
    subst hr
    apply Subtype.ext
    simp

end AdelicToriLean
