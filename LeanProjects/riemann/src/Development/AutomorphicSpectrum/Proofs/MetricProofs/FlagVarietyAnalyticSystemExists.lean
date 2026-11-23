import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverDegreeOneRealisationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataFubiniStudyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyArithmeticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyModelBaseMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverRealisationPullbackStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataUniformisedStatement

noncomputable section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flagVarieties_flagSys : Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    ∃ (d : ℕ) (S : AnSys (d + 1) (Ψ × Fin N)) (Re : Realis S (PFl Ψ N)), d + 1 = antisymDegree Ψ N ∧
      Re.deg = 1 ∧ (∀ p, Re.ref p = yLineFl Ψ N p) ∧ (∀ p t, Re.line p t = yLineFl Ψ N p) ∧
      Nonempty (FlagSys Re N) := by
  intro hIn Ψ _ _ _ N hN
  obtain ⟨M, BM, hhom, hdy, hbd⟩ := GlobalTheory.T.flag_variety_model_base_metric Ψ N hN
  have hA := GlobalTheory.T.flag_variety_arithmetic Ψ N hN
  have hpos : 0 < antisymDegree Ψ N := by
    have h1 : 0 < Fintype.card Ψ := Fintype.card_pos
    have h2 : 0 < N.choose 2 := Nat.choose_pos hN
    exact Nat.mul_pos h1 h2
  obtain ⟨d, hd1⟩ : ∃ d, d + 1 = antisymDegree Ψ N := ⟨antisymDegree Ψ N - 1, Nat.sub_add_cancel hpos⟩
  have hAr : IsArithVar (mCoordIdeal (yFl Ψ N)) (d + 2) := by
    have hd2 : d + 2 = antisymDegree Ψ N + 1 := by omega
    rw [hd2]
    exact hA
  have h0 : (N - N).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hdeg : d + 1 = 0 + Fintype.card Ψ * (N.choose 2 + (N - N).choose 2) := by
    rw [h0, add_zero, zero_add]
    exact hd1
  have hhom' : ∀ p : Ψ × Fin N, BM.hom p = fsHerm (FlIdx Ψ N) (M.dy p) := fun p => (hhom p).trans (hdy p).symm
  obtain ⟨FA, hFAline⟩ := GlobalTheory.T.flag_analytic_data_fubini_study _ _ _ _ Ψ N N M 0 d BM hAr hdeg hbd hhom'
  obtain ⟨Cv, CR, hCv, hCRref, hCRline⟩ := GlobalTheory.T.flag_cover_degree_one_realisation _ _ _ _ Ψ N N M 0 d BM FA
  have hunif := GlobalTheory.T.flag_analytic_data_uniformised _ _ _ _ Ψ N N M 0 d BM FA (by simp) hd1
  refine ⟨d, FA.S.comap some, CR.Re, hd1, ?_, ?_, ?_, ?_⟩
  · rw [CR.deg_eq, hCv]
  · intro p
    rw [hCRref, FA.ref_some, hdy]
  · intro p t
    rw [hCRline, hFAline, hdy]
  · exact ⟨FlagSys.mk le_rfl hd1 hunif (fun τ a b hab hor =>
      (GlobalTheory.T.flag_cover_realisation_pullback hIn _ _ _ _ Ψ N N M 0 d BM FA _ _ _ _ M Cv CR hAr τ a b hab hor).some)⟩

end GlobalTheory.CompanionTheory.Ar.PB
