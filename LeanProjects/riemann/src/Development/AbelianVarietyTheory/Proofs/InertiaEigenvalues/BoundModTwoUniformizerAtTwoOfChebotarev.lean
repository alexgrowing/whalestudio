import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValLeOfNotMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCocycleChangeScalarsBack
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntiOfKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerFinrankEqDualStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleFormsSpanOddResidueChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerPresentationMatrixOfGaloisCohomology
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastEqOneOfMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.Dyadic

theorem bound_mod_two_of_hypothesis : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmC bkP := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hS := GlobalTheory.SelFun.oneMatrix_of_galoisCohomology h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hgw := GlobalTheory.T.residual_selmer_finrank_eq_dual h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hk4 := GlobalTheory.ScalarFrob.firstHalf h5 h6 h7 h4 D N X bkP
  refine GlobalTheory.StepTwo.TwoBound.thmC_of_parts D N X bkP (GlobalTheory.ChosenPrimes.stepAB h1 D N X) (fun i => GlobalTheory.ChooseForms.chooseH h8 D N X bkP i fun s hs =>
    ⟨GlobalTheory.ResSel.SpanOddPf.spanOdd D N X bkP i s hs, GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp D N X bkP i s hs, hgw i s hs⟩) fun i s hs => ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.StepTwo.StartInd.start_of_resBound D N X bkP i s hs (GlobalTheory.ScalarFrob.firstPlace h5 h6 h7 D N X bkP i s hs) (GlobalTheory.ResOrder.resBound h4 D N X bkP i s hs (hk4 i s hs)
      (GlobalTheory.ResRecip.reciprocity h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP i s hs (hk4 i s hs)) (hgw i s hs))
  · exact GlobalTheory.Growth.grow h4 D N X bkP hS i s hs
  · exact GlobalTheory.NewPrime.step h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP hS i s hs

end GlobalTheory.StepTwo.Dyadic
