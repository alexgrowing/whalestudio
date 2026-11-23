import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ConstantCoeffZeroOfBoundTwo

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet.OJ

variable {p : ℕ} [Fact p.Prime]

theorem norm_coeff_monomial_one {τ : Type*} (j m : τ →₀ ℕ) :
    ‖coeff m (monomial j (1 : ℂ_[p]))‖ ≤ 1 := by
  rw [MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

theorem admissible_jet_term {D : D7} (E : Ent D) (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (c : ℂ_[p])
    (hc : ‖c‖ = 1) (ep sg : ℂ_[p]) (hep : ‖ep‖ = 1) (hsg : sg = 1 ∨ sg = -1) (be : MvPowerSeries (ZMod 2) ℂ_[p])
    (hbe : OJ.B1 p 2 be ∧ OJ.B2 p 2 be ∧ OJ.B3 p 2 be ∧ OJ.B4 p 2 be)
    (j : ZMod 1 × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ) :
    (oneLoc E p h5 u i z (T1 (D.R.N i) (D.R.N (i + 1)) c ep sg be j)).AdmB := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  exact ⟨c, hc, be, ⟨ep, hep, sg, hsg, monomial j 1, fun m => norm_coeff_monomial_one j m,
    subst_log_jet_monomial _ _ c ep sg hc0 be j⟩, hbe⟩

def kz (D : D7) {N0 N1 : ℕ} (z : Pl D) (k : Pl D × Fin N0 × Fin N1 →₀ ℕ) : ZMod 1 × Fin N0 × Fin N1 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun w => k (z, w.2)

theorem sum_mapDomain_kz (D : D7) {N0 N1 : ℕ} (k : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    ∑ z, Finsupp.mapDomain (pEmb (ptE D z) (Fin N0 × Fin N1)) (kz D z k) = k := by
  ext ⟨z0, w⟩
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single z0]
  · have h : ((z0, w) : Pl D × Fin N0 × Fin N1) =
        pEmb (ptE D z0) (Fin N0 × Fin N1) ((0 : ZMod 1), w) := rfl
    rw [h, Finsupp.mapDomain_apply (pEmb (ptE D z0) _).injective]
    rfl
  · intro z _ hz
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨a, w'⟩, h⟩
    rw [pEmb_apply] at h
    exact hz (congrArg Prod.fst h)
  · intro h
    exact absurd (Finset.mem_univ z0) h

theorem hs_logPl (D : D7) (hn : nP D p = 1) (N0 N1 : ℕ) : HasSubst (logPl D p (β := Fin N0 × Fin N1)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show logPl D p v 0 = 0
  simp only [logPl]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  exact fun h => (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero))
    (Finsupp.single_eq_zero.1 h.symm)

theorem hasSubst_log_jet (N0 N1 : ℕ) : HasSubst (jetLogG p 1 (β := Fin N0 × Fin N1)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show jetLogG p 1 v 0 = 0
  simp only [jetLogG]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  exact fun h => (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero))
    (Finsupp.single_eq_zero.1 h.symm)

theorem prod_rename_exp_jet_series (D : D7) (hn : nP D p = 1) (N0 N1 : ℕ) (ep sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) (hcc : ∀ z, constantCoeff (be z) = 0) :
    ∏ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (Y1 N0 N1 (ep z) (sg z) (be z)) =
      subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (fAll D N0 N1 ep sg be)) := by
  classical
  have hE : ∀ f : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p],
      OJ.expS ℂ_[p] f = PI.OrbShared.ExpSum.eS f := fun f => rfl
  set g : Pl D → MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] := fun z =>
    (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub (ep z) (z, a, b)) (be z) with hg
  have hgc : ∀ z, constantCoeff (g z) = 0 := fun z => by
    simp only [hg]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul]
    simp only [map_sum, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_gSub _ _ _ (hcc z),
      Finset.sum_const_zero, smul_zero]
  have hz : ∀ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (Y1 N0 N1 (ep z) (sg z) (be z)) =
      subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (g z)) := by
    intro z
    have hl : (fun v => rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (jetLogG p 1 v)) =
        fun v => logPl D p (pEmb (ptE D z) (Fin N0 × Fin N1) v) := by
      funext v
      rw [jetLogG_one, rename_psubst _ (PowerSeries.HasSubst.of_constantCoeff_zero
        (MvPowerSeries.constantCoeff_X v)), MvPowerSeries.rename_X, logPl_one p D hn]
    rw [Y1, rename_subst' _ (hasSubst_log_jet N0 N1), hl, ← subst_rename' _ (hs_logPl D hn N0 N1), OJ.expS,
      OJ.expS, rename_psubst _ (PowerSeries.HasSubst.of_constantCoeff_zero
        (constantCoeff_jet_series N0 N1 (ep z) (sg z) (be z) (hcc z))), rename_jet_series]
  rw [Finset.prod_congr rfl (fun z _ => hz z), ← MvPowerSeries.coe_substAlgHom (hs_logPl D hn N0 N1),
    ← map_prod]
  congr 1
  rw [show fAll D N0 N1 ep sg be = ∑ z, g z from rfl, hE,
    PI.OrbShared.ExpSum.eS_sum _ _ (fun z _ => hgc z)]
  rfl

private theorem prod_monomial_one_eq_monomial_sum {ι σ : Type*} (s : Finset ι) (m : ι → σ →₀ ℕ) :
    ∏ i ∈ s, (monomial (m i) (1 : ℂ_[p]) : MvPowerSeries σ ℂ_[p]) = monomial (∑ i ∈ s, m i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    first | rfl | simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, MvPowerSeries.monomial_mul_monomial, one_mul]

theorem factor (D : D7) (hn : nP D p = 1) (N0 N1 : ℕ) (c : ℂ_[p]) (hc : c ≠ 0) (ep sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) (hcc : ∀ z, constantCoeff (be z) = 0)
    (k : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    subst (psiA p c) (monomial k 1 *
        subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (fAll D N0 N1 ep sg be))) =
      ∏ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (T1 N0 N1 c (ep z) (sg z) (be z) (kz D z k)) := by
  classical
  have hpsi : ∀ z (s : ZMod 1 × Fin N0 × Fin N1),
      rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (psiA p c s) =
        psiA p c (pEmb (ptE D z) (Fin N0 × Fin N1) s) := by
    intro z s
    have hh : PowerSeries.HasSubst (C c⁻¹ * X s : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    simp only [psiA]
    rw [rename_psubst _ hh, map_mul, MvPowerSeries.rename_C, MvPowerSeries.rename_X]
  have hT : ∀ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (T1 N0 N1 c (ep z) (sg z) (be z) (kz D z k)) =
      subst (psiA p c) (monomial (Finsupp.mapDomain (pEmb (ptE D z) (Fin N0 × Fin N1)) (kz D z k)) 1 *
        rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (Y1 N0 N1 (ep z) (sg z) (be z))) := by
    intro z
    rw [T1, rename_subst' _ (hs_psiA p c), funext (hpsi z), ← subst_rename' _ (hs_psiA p c), map_mul,
      MvPowerSeries.rename_monomial]
  rw [Finset.prod_congr rfl (fun z _ => hT z), ← MvPowerSeries.coe_substAlgHom (hs_psiA p c), ← map_prod,
    Finset.prod_mul_distrib, prod_rename_exp_jet_series D hn N0 N1 ep sg be hcc, prod_monomial_one_eq_monomial_sum,
    sum_mapDomain_kz]

end PI.OrbJet.AO

end
