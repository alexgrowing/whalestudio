import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfAdmittedHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldsAtAuxiliaryPrimesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAOfBlochKatoTateDualityEulerCStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEulerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedFormsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2TopStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimAtAuxiliaryPrimePlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOver
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistedPlaceBound

theorem closing : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  intro hGAR hBKL hLTD hLEC D HW F Cm r ρ large₂ ep C Qp hC hQ hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hKill hJump hFon hG5x hPar
  have hUsed := GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm
  have hW : EmbeddingTypeJumps.admW (D := D) HW F := by
    intro i _ w hw Cf h
    exact GlobalTheory.T.wachHypothesis_crystallineLattices D HW F Cm hUsed.1 hUsed.2 (GlobalTheory.crysOnCond_all D HW F) (D.nd.l i) _ 1 Cf.LL h
  have hA : EmbeddingTypeJumps.admA (D := D) 160 := GlobalTheory.T.localLifting_of_blochKato_tateDuality_eulerChar hBKL hLTD hLEC D HW F Cm 160 le_rfl
  have hTB : EmbeddingTypeJumps.admTB (D := D) HW F := GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hBKL hLTD hLEC D HW F Cm
  have hBK : EmbeddingTypeJumps.admBK (D := D) := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBKL hLTD hLEC D
  have hLit : EmbeddingTypeJumps.LiteratureHypotheses (D := D) := by
    intro i hi
    refine ⟨hG5x i hi, fun w hw Cf => ⟨?_, GlobalTheory.T.blochKatoDim_at_auxiliary_prime_places hLTD hLEC D i hi w hw Cf⟩,
      GlobalTheory.BridgeTie.localCoefficientCompatibility D i, GlobalTheory.FontaineAdm.fontaineProperties_all_places D i, GlobalTheory.T.integral_tate_H2_top hLTD D i,
      GlobalTheory.T.unramifiedClassFieldBound_of_artin hGAR D i⟩
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.tate_duality_h2_of_all_coefficients _ _ _
      (GlobalTheory.TateTop.tateH2_of_duality_loc hLTD (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw)
      (GlobalTheory.HTW.Rec.goodO_finExt_integers (D.nd.l i) Cf.LL)
  have h01 := GlobalTheory.T.local_fields_at_auxiliary_primes D
  refine ⟨h01.1, h01.2, ?_⟩
  exact GlobalTheory.T.theoremB_of_admittedHypotheses D HW F r ρ large₂ ep 160 C Qp (by rw [max_eq_left (by norm_num)]; linarith) hQ hW hA
    hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hTB hBK hKill hJump hFon hLit hPar

end GlobalTheory.TwistedPlaceBound
