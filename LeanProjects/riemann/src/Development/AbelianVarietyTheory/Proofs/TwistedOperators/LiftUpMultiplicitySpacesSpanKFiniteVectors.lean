import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanishStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijectionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPairStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.EvenOnto.LiftUp

theorem liftUp_stage_span : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) ω f, c.Is → k < c.m → s.Is c k → s'.Is c (k + 1) → PreStep c k s s' ω f → ∃ T : PolF D s'.V.rank s.V.rank → SmT s.M → SmT s'.M, (∀ P v, T P v ∈ s'.KF) ∧ s'.KF ≤ Submodule.span ℂ {w | ∃ P v, w = T P v} ∧ GlobalTheory.PairLift.LiftsM c.θ s.M s'.M s.ν s.fd (fun P h g => conj (thetaKO ω g h (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M f P))) T := by
  intro hDS hHC hCD hCW D c k s s' ω f hc hk hs _hs' hp
  obtain ⟨X, hX, _h1, _h2, h3, h4, h5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hDS hHC
  have hIn : Inputs D X := GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries hDS hHC hCD hCW D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X hIn (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X hIn (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X hIn (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X hIn)))
  have hW := hp.weil
  have hstd : IsStdChar D c.ψ (-1) := hW.std
  have hadj : AdjLaw c.ψ s.V s'.V := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D c.ψ hstd s.V s'.V
  have h0 : adjO s.V s'.V 0 = 0 := by
    have := hadj.add 0 0
    simpa using this
  obtain ⟨ω', hW', hω'⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D c.ψ s.V s'.V (c.χ k) (c.χ k) ω hW
  obtain ⟨j, -, hj⟩ := GlobalTheory.T.fockVectors_conjAdjointPullback_bijection D c.ψ c.θ hstd hc.inf s.V s'.V (Fr.ofModel s.M) (Fr.ofModel s'.M)
  obtain ⟨hvac', hpt⟩ := hj f (isVacF_of_isVacVec hp.vac)
  have hω'e : IsWeilExp c.ψ s'.V s.V (c.a k) (c.a k) ω' :=
    ⟨c.χ k, c.χ k, hW', fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  have hne : dag s.V s'.V f ≠ 0 := by
    intro hz
    apply hp.vac.ne
    funext x
    have hx := congrFun hz (adjO s'.V s.V x)
    simp only [dag, hadj.invol, Pi.zero_apply] at hx
    simpa using hx
  have hf' : IsVacVec c.ψ c.θ s'.M s.M (dag s.V s'.V f) := ⟨hvac'.1, hne, hvac'.2⟩
  obtain ⟨It, hIt⟩ := (GlobalTheory.T.exists_realIntertwiners_upwardThetaPair hDS hHC D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf hp.par).2
  have hItW := hIt ω' (dag s.V s'.V f) hω'e hf'
  have hrule : ∀ τ, RulePar X (s'.par τ) (s.par τ) (c.a k τ) (c.a k τ) :=
    fun τ => ((GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions hDS hHC D c.t _ _ _ _ (hp.par τ)).2 X h3 h4 h5).2
  have hL := hPL _ _ _ _ hrule s'.V s.V s'.M s.M c.θ c.ψ hc.inf ω' hω'e (dag s.V s'.V f) It hf' hItW s.ν s.fd hs.haar hs.fund
    (dag s.V s'.V f) (isVacF_of_isVacVec hf')
  refine ⟨fun P v => It (j P) v, fun P v =>
    GlobalTheory.T.real_intertwiner_values_kFinite D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf' hItW (j P) v, ?_, ?_⟩
  · refine (GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf'
      hItW).trans (Submodule.span_mono ?_)
    rintro w ⟨P, v, -, rfl⟩
    exact ⟨j.symm P, v, by simp⟩
  · intro F hF
    obtain ⟨F', hF', hF'e⟩ := hL F hF
    refine ⟨F', hF', fun P v h => ?_⟩
    have key : ∀ g, conj (thetaKO ω g h (ptOf c.ψ c.θ s.M s'.M f P)) =
        thetaKO ω' h g (ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P)) := by
      intro g
      have e1 : ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P) = dag s.V s'.V (ptOf c.ψ c.θ s.M s'.M f P) := hpt P
      simp only [thetaKO]
      rw [e1, hω']
      simp [dag, h0]
    simp only [key]
    exact hF'e (j P) v h

end GlobalTheory.EvenOnto.LiftUp

end
