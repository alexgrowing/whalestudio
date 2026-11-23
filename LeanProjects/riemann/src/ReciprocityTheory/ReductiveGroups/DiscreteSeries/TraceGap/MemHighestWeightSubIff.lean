import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.GsBasisPhys
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.BlockAnti

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

theorem gc_coord_num (x : Fin n × Fin n) (s : Finset (Fin (n * n))) :
    (fockBasis n).coord s ∘ₗ (cpFock x.1 x.2 ∘ₗ cmFock x.1 x.2) =
      (if finProdFinEquiv x ∈ s then (1 : ℂ) else 0) • (fockBasis n).coord s := by
  refine (fockBasis n).ext fun t => ?_
  simp only [LinearMap.comp_apply, lf_num_basis, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  by_cases h : t = s
  · subst h
    split_ifs <;> simp
  · split_ifs <;> simp [Module.Basis.repr_self, h]

theorem gc_support_phys {ε : Fin n → Bool} {f : Fock n} (hf : f ∈ physFock ε) {s : Finset (Fin (n * n))}
    (hs : (fockBasis n).coord s f ≠ 0) : s ⊆ lfPhysModes ε := by
  intro m hm
  by_contra hnot
  obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
  have hx : ¬ (ε x.1 = true ∧ ε x.2 = false) := fun h => hnot ((lf_mem_phys ε x.1 x.2).2 h)
  have h0 : cmFock x.1 x.2 f = 0 := by
    simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hf
    exact hf x.1 x.2 hx
  have h := LinearMap.congr_fun (gc_coord_num x s) f
  simp only [LinearMap.comp_apply, h0, map_zero, if_pos hm, one_smul] at h
  exact hs h.symm

def gcPh (ε : Fin n → Bool) (s : Finset (Fin (n * n))) : Finset (Fin n × Fin n) :=
  (s \ (lowerWedgeAlt ε).1).image finProdFinEquiv.symm ∪
    ((lowerWedgeAlt ε).1 \ s).image fun k => ((finProdFinEquiv.symm k).2, (finProdFinEquiv.symm k).1)

theorem gc_disj (ε : Fin n → Bool) {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    Disjoint ((s \ (lowerWedgeAlt ε).1).image finProdFinEquiv.symm)
      (((lowerWedgeAlt ε).1 \ s).image fun k => ((finProdFinEquiv.symm k).2, (finProdFinEquiv.symm k).1)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx1
  obtain ⟨k', hk', he⟩ := Finset.mem_image.1 hx2
  have hp := hs (Finset.mem_sdiff.1 hk).1
  have hp' := (lowerWedgeAlt ε).2 (Finset.mem_sdiff.1 hk').1
  simp only [lfPhysModes, mem_filter, mem_univ, true_and] at hp hp'
  have e : (finProdFinEquiv.symm k').2 = (finProdFinEquiv.symm k).1 := congrArg Prod.fst he
  rw [e, hp.1] at hp'
  exact Bool.noConfusion hp'.2

theorem gc_isPosNC (ε : Fin n → Bool) {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    IsPosNC ε (gcPh ε s) := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨hks, hk0⟩ := Finset.mem_sdiff.1 hk
    have hp := hs hks
    obtain ⟨y, rfl⟩ := finProdFinEquiv.surjective k
    rw [mem_lowerWedge_iff] at hk0
    simp only [lfPhysModes, mem_filter, mem_univ, true_and, Equiv.symm_apply_apply] at hp ⊢
    have hne : y.1 ≠ y.2 := fun he => by
      have h1 := hp.1
      rw [he, hp.2] at h1
      exact Bool.noConfusion h1
    refine ⟨lt_of_le_of_ne (not_lt.1 fun h' => hk0 ⟨hp.1, hp.2, h'⟩) hne, ?_⟩
    rw [hp.1, hp.2]
    simp
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨y, rfl⟩ := finProdFinEquiv.surjective k
    have hk0 := (Finset.mem_sdiff.1 hk).1
    rw [mem_lowerWedge_iff] at hk0
    simp only [Equiv.symm_apply_apply]
    refine ⟨hk0.2.2, ?_⟩
    rw [hk0.1, hk0.2.1]
    simp

theorem gc_phSum (ε : Fin n → Bool) {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    phSum (gcPh ε s) = ∑ k ∈ s \ (lowerWedgeAlt ε).1, modeWt ε (finProdFinEquiv.symm k) -
      ∑ k ∈ (lowerWedgeAlt ε).1 \ s, modeWt ε (finProdFinEquiv.symm k) := by
  unfold phSum gcPh
  rw [Finset.sum_union (gc_disj ε hs), Finset.sum_image (fun a _ b _ h => finProdFinEquiv.symm.injective h),
    Finset.sum_image (fun a _ b _ h => finProdFinEquiv.symm.injective
      (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))),
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hp := hs (Finset.mem_sdiff.1 hk).1
    simp only [lfPhysModes, mem_filter, mem_univ, true_and] at hp
    simp only [modeWt, if_pos hp]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hp := (lowerWedgeAlt ε).2 (Finset.mem_sdiff.1 hk).1
    simp only [lfPhysModes, mem_filter, mem_univ, true_and] at hp
    simp only [modeWt, if_pos hp, root, neg_sub]

theorem fockWeight_wedge_lowerModes (ε : Fin n → Bool) : fockWt ε (lowerWedgeAlt ε).1 = rhoHol ε - rhoN ε :=
  (coord_wt_eq ε (lowerWedge_weight ε) (by simp)).symm

theorem gc_wt_eq (ε : Fin n → Bool) {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    fockWt ε s = rhoHol ε - rhoN ε + phSum (gcPh ε s) := by
  rw [gc_phSum ε hs, ← fockWeight_wedge_lowerModes]
  unfold fockWt
  have e1 := Finset.sum_sdiff (f := fun k => modeWt ε (finProdFinEquiv.symm k))
    (Finset.inter_subset_left : s ∩ (lowerWedgeAlt ε).1 ⊆ s)
  have e2 := Finset.sum_sdiff (f := fun k => modeWt ε (finProdFinEquiv.symm k))
    (Finset.inter_subset_right : s ∩ (lowerWedgeAlt ε).1 ⊆ (lowerWedgeAlt ε).1)
  have d1 : s \ (s ∩ (lowerWedgeAlt ε).1) = s \ (lowerWedgeAlt ε).1 := by
    ext; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have d2 : (lowerWedgeAlt ε).1 \ (s ∩ (lowerWedgeAlt ε).1) = (lowerWedgeAlt ε).1 \ s := by
    ext; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [d1] at e1
  rw [d2] at e2
  rw [← e1, ← e2]
  abel

theorem gc_Ph_empty {ε : Fin n → Bool} {s : Finset (Fin (n * n))} (h : gcPh ε s = ∅) : s = (lowerWedgeAlt ε).1 := by
  unfold gcPh at h
  rw [Finset.union_eq_empty, Finset.image_eq_empty, Finset.image_eq_empty, Finset.sdiff_eq_empty_iff_subset,
    Finset.sdiff_eq_empty_iff_subset] at h
  exact Finset.Subset.antisymm h.1 h.2

theorem gc_plus_sum {ε : Fin n → Bool} {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    ∑ a ∈ plusIdx ε, fockWt ε s a = (s.card : ℝ) := by
  unfold fockWt
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hp := hs hk
  obtain ⟨y, rfl⟩ := finProdFinEquiv.surjective k
  have hp' := (lf_mem_phys ε y.1 y.2).1 hp
  simp only [Equiv.symm_apply_apply, modeWt, if_pos hp', root, Pi.sub_apply, Finset.sum_sub_distrib]
  simp [plusIdx, Pi.single_apply, hp'.1, hp'.2]

end ReciprocityTheory.ChartRestriction.DS.TRGap
