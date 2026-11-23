import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree

noncomputable section

open Classical

namespace PI.OrbJet.AU

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbJet.OrbW PI.OrbShared

variable (D : D7) (p : ℕ) [Fact p.Prime]

theorem subst_rename {β : Type} [Finite β] (ep : ℂ_[p]) (r : Pl D) (F : MvPowerSeries (ZMod (nP D p) × β) ℂ_[p]) :
    subst (fun v : Pl D × β => C ep * logPl D p v) (rename (pE D p r β) F) =
      rename (pE D p r β) (subst (fun w : ZMod (nP D p) × β => C ep * jetLogG p (nP D p) w) F) := by
  haveI : Finite (Pl D × β) := inferInstance
  have hcc1 : ∀ v : Pl D × β, constantCoeff (C ep * logPl D p v) = 0 := by
    intro v
    rw [map_mul]
    have h0 : constantCoeff (logPl D p v) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show logPl D p v 0 = 0
      simp [logPl, JetTdeg, eq_comm (a := (0 : Pl D × β →₀ ℕ))]
    rw [h0, mul_zero]
  have hb : HasSubst (fun v : Pl D × β => C ep * logPl D p v) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcc1
  have hcc2 : ∀ w : ZMod (nP D p) × β, constantCoeff (C ep * jetLogG p (nP D p) w) = 0 := by
    intro w
    rw [map_mul]
    have h0 : constantCoeff (jetLogG p (nP D p) w) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show jetLogG p (nP D p) w 0 = 0
      simp [jetLogG, JetTdeg, eq_comm (a := (0 : ZMod (nP D p) × β →₀ ℕ))]
    rw [h0, mul_zero]
  have ha : HasSubst (fun w : ZMod (nP D p) × β => C ep * jetLogG p (nP D p) w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcc2
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) hb,
    MvPowerSeries.subst_comp_subst_apply ha (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext w
  rw [Function.comp_apply, MvPowerSeries.subst_X hb, ← MvPowerSeries.rename_eq_subst, map_mul,
    MvPowerSeries.rename_C, rename_jet]

def bsum {N0 N1 : ℕ} (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) :
    MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ a : Fin N0, ∑ b : Fin N1,
    subst (fun s : ZMod (nP D p) => (X (s, a, b) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p])) be

theorem hasSubst_Xs {N0 N1 : ℕ} (a : Fin N0) (b : Fin N1) :
    HasSubst (fun s : ZMod (nP D p) => (X (s, a, b) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p])) := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => MvPowerSeries.constantCoeff_X _)
  | exact MvPowerSeries.HasSubst.X
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [MvPowerSeries.constantCoeff_X]; exact IsNilpotent.zero)

theorem cc_bsum {N0 N1 : ℕ} (sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0) :
    constantCoeff (sg • bsum D p (N0 := N0) (N1 := N1) be) = 0 := by
  unfold bsum
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum]
  rw [Finset.sum_eq_zero (fun a _ => ?_), mul_zero]
  rw [map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_Xs D p a b)
    (fun s => MvPowerSeries.constantCoeff_X _) hbe

theorem beAll_eq {N0 N1 : ℕ} (R : Finset (Pl D)) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) :
    beAll D p (N0 := N0) (N1 := N1) R sg be =
      ∑ r ∈ R, rename (pE D p r (Fin N0 × Fin N1)) (sg r • bsum D p (be r)) := by
  unfold beAll bsum
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_Xs D p a b) (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext s
  rw [MvPowerSeries.subst_X (MvPowerSeries.HasSubst.X_comp _)]
  rfl

def Eorb {N0 N1 : ℕ} (sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) :
    MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p] :=
  subst (jetLogG p (nP D p) (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (sg • bsum D p be))

theorem E_eq {N0 N1 : ℕ} (R : Finset (Pl D)) (sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hcc : ∀ r ∈ R, constantCoeff (be r) = 0) :
    subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (beAll D p R sg be)) =
      ∏ r ∈ R, rename (pE D p r (Fin N0 × Fin N1)) (Eorb D p (N0 := N0) (N1 := N1) (sg r) (be r)) := by
  haveI : Finite (Pl D × Fin N0 × Fin N1) := inferInstance
  have hL : HasSubst (logPl D p (β := Fin N0 × Fin N1)) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => ?_
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show logPl D p v 0 = 0
    simp [logPl, JetTdeg, eq_comm (a := (0 : Pl D × Fin N0 × Fin N1 →₀ ℕ))]
  have hG : ∀ r ∈ R, constantCoeff (sg r • bsum D p (N0 := N0) (N1 := N1) (be r)) = 0 :=
    fun r hr => cc_bsum D p (sg r) (be r) (hcc r hr)
  have hRG : ∀ r ∈ R, constantCoeff (rename (pE D p r (Fin N0 × Fin N1)) (sg r • bsum D p (N0 := N0) (N1 := N1) (be r))) = 0 := by
    intro r hr
    rw [MvPowerSeries.rename_eq_subst]
    exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.HasSubst.X_comp _)
      (fun i => MvPowerSeries.constantCoeff_X _) (hG r hr)
  rw [beAll_eq]
  change subst (logPl D p (β := Fin N0 × Fin N1)) (PI.OrbShared.ExpSum.eS _) = _
  rw [PI.OrbShared.ExpSum.eS_sum _ _ hRG, ← MvPowerSeries.coe_substAlgHom hL, map_prod]
  refine Finset.prod_congr rfl fun r hr => ?_
  rw [MvPowerSeries.coe_substAlgHom]
  have h1 : PI.OrbShared.ExpSum.eS (rename (pE D p r (Fin N0 × Fin N1)) (sg r • bsum D p (N0 := N0) (N1 := N1) (be r))) =
      rename (pE D p r (Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (sg r • bsum D p (N0 := N0) (N1 := N1) (be r))) := by
    rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst]
    exact (PI.OrbShared.ExpSum.subst_eS (MvPowerSeries.HasSubst.X_comp _) _ (hG r hr)).symm
  rw [h1]
  have h2 := subst_rename D p 1 r (OJ.expS ℂ_[p] (sg r • bsum D p (N0 := N0) (N1 := N1) (be r)))
  simp only [map_one, one_mul] at h2
  rw [h2]
  rfl

theorem prod_monomial_one {σ ι : Type*} (s : Finset ι) (g : ι → σ →₀ ℕ) :
    (∏ i ∈ s, (monomial (g i) (1 : ℂ_[p]) : MvPowerSeries σ ℂ_[p])) = monomial (∑ i ∈ s, g i) 1 := by
  classical
  refine Finset.induction_on s (by simp [MvPowerSeries.monomial_zero_one]) ?_
  intro i s hi ih
  rw [Finset.prod_insert hi, ih, MvPowerSeries.monomial_mul_monomial, one_mul, Finset.sum_insert hi]

def resM {γ : Type} (r : Pl D) (m : Pl D × γ →₀ ℕ) : ZMod (nP D p) × γ →₀ ℕ :=
  comapDomain (pE D p r γ) m (pE D p r γ).injective.injOn

theorem mem_orbit_unique {R : Finset (Pl D)} (hR : IsReps D p R) {r r' : Pl D} (hr : r ∈ R) (hr' : r' ∈ R)
    (s s' : ZMod (nP D p)) (h : orbMap D p r s = orbMap D p r' s') : r = r' := by
  obtain ⟨r0, -, huniq⟩ := hR (orbMap D p r s)
  have h1 := huniq r ⟨hr, s.val, rfl⟩
  have h2 := huniq r' ⟨hr', s'.val, h.symm⟩
  rw [h1, h2]

theorem sum_resM {γ : Type} {R : Finset (Pl D)} (hR : IsReps D p R) (m : Pl D × γ →₀ ℕ) :
    ∑ r ∈ R, mapDomain (pE D p r γ) (resM D p r m) = m := by
  ext ⟨z, c⟩
  rw [Finsupp.finset_sum_apply]
  obtain ⟨r0, ⟨hr0, e0, he0⟩, huniq⟩ := hR z
  have hx0 : ((z, c) : Pl D × γ) = pE D p r0 γ ((e0 : ZMod (nP D p)), c) := by
    show (z, c) = (orbMap D p r0 (e0 : ZMod (nP D p)), c)
    rw [← posPl_eq_orbMap, he0]
  rw [Finset.sum_eq_single r0]
  · rw [hx0, Finsupp.mapDomain_apply (pE D p r0 γ).injective]
    rfl
  · intro r hr hne
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨s, c'⟩, hsc⟩
    apply hne
    apply huniq r
    refine ⟨hr, s.val, ?_⟩
    have hsc' : ((orbMap D p r s, c') : Pl D × γ) = (z, c) := hsc
    rw [← (Prod.mk.inj hsc').1]
    rfl
  · intro h
    exact absurd hr0 h

theorem mono_eq {γ : Type} {R : Finset (Pl D)} (hR : IsReps D p R) (m : Pl D × γ →₀ ℕ) :
    (monomial m (1 : ℂ_[p]) : MvPowerSeries (Pl D × γ) ℂ_[p]) =
      ∏ r ∈ R, rename (pE D p r γ) (monomial (resM D p r m) 1) := by
  conv_lhs => rw [← sum_resM D p hR m]
  rw [← prod_monomial_one]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [MvPowerSeries.rename_monomial]

end PI.OrbJet.AU

end
