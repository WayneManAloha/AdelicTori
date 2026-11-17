import AdelicToriLean.PerpQuot
import AdelicToriLean.AdelicTorusProps

/-!
# The periodic group `L = C^⊥ / C` of the adelic model

For `ι : D → ℚⁿ` injective with `ℤⁿ ⊆ ι(D)` and `C = annC (range ι)`:

* `psi_eq_zero_iff`: `ker ψ = ℤ̂`;
* `perp_emb_eq`: `C = ι(D)^⊥` inside `ℚ̂ⁿ`;
* `ZHatn_le_perp`: `ℤ̂ⁿ ⊆ C^⊥`, so `C ⊆ C^⊥` and `C^⊥` is open;
* `rat_mem_perp_iff`: **`C^⊥ ∩ ℚⁿ = ι(D)`**;
* `modelL_selfDual`: `L = C^⊥ / C` is Pontryagin self-dual.
-/

open IsDedekindDomain Topology

noncomputable section

namespace AdelicToriLean

variable {n : ℕ}

/-- `ℚⁿ → ℚ̂ⁿ`. -/
def emb : (Fin n → ℚ) →+ (Fin n → QHat) where
  toFun r i := algebraMap ℚ QHat (r i)
  map_zero' := by ext1 i; simp
  map_add' r s := by ext1 i; simp

theorem emb_apply (r : Fin n → ℚ) (i : Fin n) : emb r i = algebraMap ℚ QHat (r i) := rfl

theorem prA_emb (b : Fin n → ℚ) (u : Fin n → QHat) :
    prA (emb b) u = ∑ i, finChar (b i) (u i) := by
  rw [prA, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show psi (algebraMap ℚ QHat (b i) * u i) = psi ((b i) • u i)
  rw [Algebra.smul_def]

/-- **`ker ψ = ℤ̂`.** -/
theorem psi_eq_zero_iff (u : QHat) : psi u = 0 ↔ u ∈ ZHat := by
  refine ⟨fun h => ?_, psi_ZHat⟩
  obtain ⟨r, z, hz, rfl⟩ := exists_rat_add_ZHat u
  rw [map_add, psi_ZHat hz, add_zero, psi_algebraMap] at h
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  have hr : r = (m : ℚ) := by
    rw [zsmul_one] at hm
    exact_mod_cast hm.symm
  rw [hr]
  exact ZHat.add_mem (algebraMap_int_mem_ZHat m) hz

/-- `ℤ̂ⁿ`. -/
def ZHatn : AddSubgroup (Fin n → QHat) := AddSubgroup.pi Set.univ fun _ => ZHat

theorem mem_ZHatn {u : Fin n → QHat} : u ∈ ZHatn ↔ ∀ i, u i ∈ ZHat := by
  simp [ZHatn, AddSubgroup.mem_pi]

theorem isOpen_ZHatn : IsOpen (↑(ZHatn (n := n)) : Set (Fin n → QHat)) := by
  have : (↑(ZHatn (n := n)) : Set (Fin n → QHat)) = Set.univ.pi fun _ => (ZHat : Set QHat) := by
    ext u; simp [mem_ZHatn]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_ZHat

theorem prA_ZHatn {u v : Fin n → QHat} (hu : u ∈ ZHatn) (hv : v ∈ ZHatn) : prA u v = 0 := by
  rw [mem_ZHatn] at hu hv
  apply psi_ZHat
  exact AddSubgroup.sum_mem _ fun i _ => ZHat_mul_mem (hu i) (hv i)

variable {D : Type*} [CommGroup D]
  (ι : Additive D →+ (Fin n → ℚ))

/-- `C = annC (range ι)`. -/
abbrev Cm : AddSubgroup (Fin n → QHat) := annC (Set.range ι)

theorem Cm_le_ZHatn : Cm ι ≤ ZHatn := fun _ hu => mem_ZHatn.mpr (mem_annC.mp hu).1

/-- **`C = ι(D)^⊥`.** -/
theorem perp_emb_eq (hZ : ∀ j : Fin n, Pi.single j 1 ∈ Set.range ι) :
    (↑(perp (emb '' Set.range ι)) : Set (Fin n → QHat)) = Cm ι := by
  ext u
  simp only [SetLike.mem_coe, mem_perp, Set.forall_mem_image, Set.forall_mem_range, mem_annC]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun d => ?_⟩
    · obtain ⟨d, hd⟩ := hZ i
      have := h d
      rw [hd, prA_emb] at this
      rw [← psi_eq_zero_iff]
      rwa [Finset.sum_eq_single i (fun j _ hj => by
        rw [Pi.single_eq_of_ne hj, finChar_zero]) (by simp), Pi.single_eq_same, finChar_one]
        at this
    · rw [← prA_emb]; exact h d
  · rintro ⟨_, h⟩ d
    rw [prA_emb]; exact h d

theorem ZHatn_le_perp : ZHatn ≤ Hp (Cm ι) := fun _ hz _ hc =>
  prA_ZHatn (Cm_le_ZHatn ι hc) hz

theorem Cm_le_perp : Cm ι ≤ Hp (Cm ι) := (Cm_le_ZHatn ι).trans (ZHatn_le_perp ι)

theorem isOpen_perp : IsOpen (Hp (Cm ι) : Set (Fin n → QHat)) :=
  AddSubgroup.isOpen_mono (ZHatn_le_perp ι) isOpen_ZHatn

theorem isClosed_Cm : IsClosed (Cm ι : Set (Fin n → QHat)) := isClosed_annC ι

/-- The image of `ι(D)` in `ℚ̂ⁿ`. -/
abbrev Bm : AddSubgroup (Fin n → QHat) := ι.range.map emb

theorem perp_closure (S : AddSubgroup (Fin n → QHat)) :
    (↑(perp (S.topologicalClosure : Set (Fin n → QHat))) : Set (Fin n → QHat)) =
      ↑(perp (S : Set (Fin n → QHat))) := by
  ext v
  simp only [SetLike.mem_coe, mem_perp]
  refine ⟨fun h u hu => h u (S.le_topologicalClosure hu), fun h u hu => ?_⟩
  have hcl : IsClosed {u : Fin n → QHat | prA u v = 0} :=
    isClosed_eq (by
      have := (continuous_prA v)
      have hc : Continuous fun u : Fin n → QHat => prA u v := by
        simpa [prA_comm] using this
      exact hc) continuous_const
  exact closure_minimal (fun u hu => h u hu) hcl hu

/-- **`C^⊥ ∩ ℚⁿ = ι(D)`.** -/
theorem rat_mem_perp_iff (hZ : ∀ j : Fin n, Pi.single j 1 ∈ Set.range ι) (q : Fin n → ℚ) :
    emb q ∈ Hp (Cm ι) ↔ q ∈ Set.range ι := by
  constructor
  · intro hq
    have hBset : (emb '' Set.range ι) = (Bm ι : Set (Fin n → QHat)) := by
      ext x; simp [Bm]
    have hC : (Cm ι : Set (Fin n → QHat)) = ↑(perp ((Bm ι).topologicalClosure : Set (Fin n → QHat))) := by
      rw [perp_closure, ← hBset, perp_emb_eq ι hZ]
    have hperp : (Hp (Cm ι) : Set (Fin n → QHat)) = (Bm ι).topologicalClosure := by
      show (↑(perp (Cm ι : Set (Fin n → QHat))) : Set (Fin n → QHat)) = _
      rw [hC]
      exact perp_perp_eq _ (AddSubgroup.isClosed_topologicalClosure _)
    have hq' : emb q ∈ (Bm ι).topologicalClosure := by
      rw [← SetLike.mem_coe, ← hperp]; exact hq
    -- the closure lies in the open (hence closed) subgroup `ι(D) + ℤ̂ⁿ`
    have hU : (Bm ι).topologicalClosure ≤ Bm ι ⊔ ZHatn := by
      apply AddSubgroup.topologicalClosure_minimal _ le_sup_left
      exact AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_right isOpen_ZHatn)
    obtain ⟨y, hy, z, hz, hyz⟩ := AddSubgroup.mem_sup.mp (hU hq')
    obtain ⟨b, ⟨d, rfl⟩, rfl⟩ := AddSubgroup.mem_map.mp hy
    have hzq : z = emb (q - ι d) := by rw [map_sub, ← hyz]; abel
    have hint : ∀ i, ((q - ι d) i).den = 1 := by
      intro i
      apply rat_mem_ZHat
      have := mem_ZHatn.mp hz i
      rwa [hzq, emb_apply] at this
    have hmem : q - ι d ∈ ι.range := by
      have hsum : q - ι d = ∑ j, ((q - ι d) j).num • (Pi.single j 1 : Fin n → ℚ) := by
        ext i
        rw [Finset.sum_apply, Finset.sum_eq_single i (fun j _ hj => by
          rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]) (by simp),
          Pi.smul_apply, Pi.single_eq_same, zsmul_eq_mul, mul_one]
        exact (Rat.coe_int_num_of_den_eq_one (hint i)).symm
      rw [hsum]
      exact AddSubgroup.sum_mem _ fun j _ => AddSubgroup.zsmul_mem _ (by
        obtain ⟨e, he⟩ := hZ j; exact ⟨e, he⟩) _
    obtain ⟨e, he⟩ := hmem
    exact ⟨d + e, by rw [map_add, he]; abel⟩
  · rintro ⟨d, rfl⟩ c hc
    rw [prA_comm, prA_emb]
    exact (mem_annC.mp hc).2 _ ⟨d, rfl⟩

variable [TopologicalSpace D] [DiscreteTopology D]

/-- `L = C^⊥ / C`, the periodic group of the model. -/
abbrev ModelL := PQ (Cm ι)

/-- **`L ≅ L^∨`.** -/
def modelL_selfDual : Multiplicative (ModelL ι) ≃ₜ* PontryaginDual (Multiplicative (ModelL ι)) :=
  perpQuotEquiv (Cm ι) (isClosed_Cm ι) (Cm_le_perp ι) (isOpen_perp ι)

end AdelicToriLean
