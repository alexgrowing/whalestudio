import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lowerWedgeAlt (ε : Fin n → Bool) : LfIdx ε :=
  ⟨(lfPhysModes ε).filter fun m => (finProdFinEquiv.symm m).2 < (finProdFinEquiv.symm m).1, filter_subset _ _⟩

theorem mem_lowerWedge_iff (ε : Fin n → Bool) (x : Fin n × Fin n) :
    finProdFinEquiv x ∈ (lowerWedgeAlt ε).1 ↔ ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 := by
  simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply,
    and_assoc]

theorem lf_rhoHol_sub_rhoN (ε : Fin n → Bool) (c : Fin n) :
    (rhoHol ε - rhoN ε) c = if ε c = true then ((univ.filter fun a => ε a = false ∧ a < c).card : ℝ)
      else -((univ.filter fun i => ε i = true ∧ c < i).card : ℝ) := by
  rw [cfa_rho_coord]
  cases hc : ε c <;> simp [hc, Finset.sum_boole]

theorem lowerWedge_weight (ε : Fin n → Bool) (c : Fin n) :
    sgE ε cpFock cmFock c c (fockBasis n (lowerWedgeAlt ε).1) =
      (((rhoHol ε - rhoN ε) c : ℝ) : ℂ) • fockBasis n (lowerWedgeAlt ε).1 := by
  have hw : fockWt ε (lowerWedgeAlt ε).1 c = (rhoHol ε - rhoN ε) c := by
    rw [cfa_rho_coord, fockWt, Finset.sum_apply]
    have hS : (lowerWedgeAlt ε).1 = univ.filter fun k => ε (finProdFinEquiv.symm k).1 = true ∧
        ε (finProdFinEquiv.symm k).2 = false ∧ (finProdFinEquiv.symm k).2 < (finProdFinEquiv.symm k).1 := by
      ext k
      simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    rw [hS, Finset.sum_filter, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
    have key : ∀ i b : Fin n, (if ε i = true ∧ ε b = false ∧ b < i then modeWt ε (i, b) c else 0) =
        (if c = i then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) -
        (if c = b then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) := by
      intro i b
      by_cases h : ε i = true ∧ ε b = false ∧ b < i
      · simp only [if_pos h]
        simp only [modeWt, if_pos (And.intro h.1 h.2.1), root, Pi.sub_apply, Pi.single_apply]
      · simp only [if_neg h]
        simp
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => key i b]
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      simp
    · simp
  rw [fockBasis_wt, hw]

theorem lowerWedge_killed_by_lowering (ε : Fin n → Bool) {a b : Fin n} (hba : b < a) (he : ε a = ε b) :
    sgE ε cpFock cmFock a b (fockBasis n (lowerWedgeAlt ε).1) = 0 := by
  have hab : a ≠ b := (ne_of_lt hba).symm
  unfold sgE
  split_ifs with h1 h2
  · rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxm : ε x = false := (Finset.mem_filter.1 hx).2
    rw [Module.End.mul_apply]
    by_cases hbx : finProdFinEquiv (b, x) ∈ (lowerWedgeAlt ε).1
    · obtain ⟨σ, -, hσ, -⟩ := lf_cm_basis_of_mem (x := (b, x)) hbx
      dsimp only at hσ
      rw [hσ, map_smul]
      have hxb : x < b := ((mem_lowerWedge_iff ε (b, x)).1 hbx).2.2
      have hmem : finProdFinEquiv (a, x) ∈ (lowerWedgeAlt ε).1.erase (finProdFinEquiv (b, x)) := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hab (congrArg Prod.fst (finProdFinEquiv.injective h)),
          (mem_lowerWedge_iff ε (a, x)).2 ⟨h1.1, hxm, hxb.trans hba⟩⟩
      have h0 := lf_cp_basis_of_mem (x := (a, x)) hmem
      dsimp only at h0
      rw [h0, smul_zero]
    · have h0 := lf_cm_basis_of_not_mem (x := (b, x)) hbx
      dsimp only at h0
      rw [h0, map_zero]
  · rw [LinearMap.neg_apply, LinearMap.sum_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hip : ε i = true := (Finset.mem_filter.1 hi).2
    rw [Module.End.mul_apply]
    by_cases hia : finProdFinEquiv (i, a) ∈ (lowerWedgeAlt ε).1
    · obtain ⟨σ, -, hσ, -⟩ := lf_cm_basis_of_mem (x := (i, a)) hia
      dsimp only at hσ
      rw [hσ, map_smul]
      have hai : a < i := ((mem_lowerWedge_iff ε (i, a)).1 hia).2.2
      have hmem : finProdFinEquiv (i, b) ∈ (lowerWedgeAlt ε).1.erase (finProdFinEquiv (i, a)) := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hab (congrArg Prod.snd (finProdFinEquiv.injective h)).symm,
          (mem_lowerWedge_iff ε (i, b)).2 ⟨hip, h2.2, hba.trans hai⟩⟩
      have h0 := lf_cp_basis_of_mem (x := (i, b)) hmem
      dsimp only at h0
      rw [h0, smul_zero]
    · have h0 := lf_cm_basis_of_not_mem (x := (i, a)) hia
      dsimp only at h0
      rw [h0, map_zero]
  · exfalso
    cases hb : ε b <;> simp_all

end ReciprocityTheory.ChartRestriction.DS
