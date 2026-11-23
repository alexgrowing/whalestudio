import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotDvdDifferentIdealOfStandardAddCharUnramified
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankSumLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_dvd_differentIdeal_of_standardAddChar_unramified : ∀ {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {v : HeightOneSpectrum (𝓞 F)}, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  first | exact @GlobalTheory.PsiDifferent.not_dvd_different_of_psiUnr | exact GlobalTheory.PsiDifferent.not_dvd_different_of_psiUnr | (intros; apply GlobalTheory.PsiDifferent.not_dvd_different_of_psiUnr <;> assumption)
