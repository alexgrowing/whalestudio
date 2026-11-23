import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstantStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSqStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SuppliedNorm

theorem sup_norm : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup p lam q0 R l l' dg s J tau → ∃ c : ℝ, 0 < c ∧ ∀ ν, n1 ν ≤ q0 → (J ν = 0 ∧ TBB.jN2 p (J ν) = 0 ∧ ¬ (NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν))) ∨ (J ν ≠ 0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) ∧ s ν ≠ 0 ∧ TBB.jN2 p (J ν) = ENNReal.ofReal (c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)))) := by
  intro hy P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau hN hS
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨c₁, hc₁, h1⟩ := GlobalTheory.T.bessel_setting_uniform_constant hy P.k P.r Wp Wq p.T.base
  have hH : PI.BesselPeriodGGP.IsHaarOn (GG P.k P.r) p.T.base.μG := by
    haveI : IsFiniteMeasureOnCompacts p.T.base.μG := ⟨fun K hK => p.T.base.haarG.finite_compact K hK⟩
    haveI : IsLocallyFiniteMeasure p.T.base.μG := inferInstance
    exact ⟨inferInstance, p.T.base.haarG.ne_zero, p.T.base.haarG.conc, p.T.base.haarG.left⟩
  obtain ⟨c₂, hc₂, h2⟩ := GlobalTheory.BesselDegree.schur_fdeg hy P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) _ hH
  obtain ⟨⟨-, -, -, -, hgap⟩, hfam⟩ := GlobalTheory.NumFam.num_fam P.k P.r lam P.u b bv ga h q0 hN
  refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, fun ν hν => ?_⟩
  have hDS := hS.fam ν hν
  obtain ⟨hl, hdg, hfd⟩ := hS.left ν hν
  obtain ⟨hl', -, -⟩ := hS.right ν hν
  have hP := h1 _ _ (h / 2) (R ν) (l ν) (l' ν) (dg ν) hDS (hfam ν hν).2.2.1 hgap hl hl' hfd
  have h0 : TBB.jN2 p (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = 0 := by
    rw [GlobalTheory.T.jN2_eq_normSq_base, hP 0 0 ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun g _ => by simp, by simp⟩]
    simp
  by_cases hnz : NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
  · right
    obtain ⟨hc, hs⟩ := hS.coef ν hν hnz.1 hnz.2
    have hj : TBB.jN2 p (J ν) = ENNReal.ofReal (c₁ * dg ν) := by
      rw [GlobalTheory.T.jN2_eq_normSq_base, hP _ _ hc, hs]
      congr 1
      field_simp
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hy.1.2.2.1 P.k P.r _ _ (R ν) hDS).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    have hd : dg ν = c₂ * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := by
      rw [← hfd w hw0, (h2 _ (R ν) hDS).1 w hw0]
    refine ⟨?_, hnz.1, hnz.2, ?_, ?_⟩
    · intro hJ
      rw [hJ, h0] at hj
      exact absurd hj.symm (ENNReal.ofReal_pos.2 (mul_pos hc₁ hdg)).ne'
    · intro hs0
      rw [hs0, norm_zero] at hs
      exact hdg.ne hs
    · rw [hj, hd, mul_assoc]
  · left
    have hJ := hS.zero ν (fun hh => hnz hh.2)
    exact ⟨hJ, by rw [hJ, h0], hnz⟩

end GlobalTheory.SuppliedNorm
