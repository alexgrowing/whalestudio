import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicRealPartProperties
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_realPart_properties : (∀ (v : Pl) (a b : Jd), finAt v (dg2 a b : G2) = dg2 (Ad3.R.lc v a) (Ad3.R.lc v b)) ∧ (∀ g h : G2, GL2Classical.realPart (g * h) = GL2Classical.realPart g * GL2Classical.realPart h) ∧ (∀ a b : Jd, GL2Classical.realPart (dg2 a b : G2) = dg2 (RationalIdeles.realPart a) (RationalIdeles.realPart b)) ∧ (∀ z : Jd, ∃ S : Finset Pl, ∀ v ∉ S, Ad3.R.lc v z ∈ unQ v) := by
  first | exact @GlobalTheory.CompanionTheory.CenTheta.realPart_multiplicative_and_diagonal | exact GlobalTheory.CompanionTheory.CenTheta.realPart_multiplicative_and_diagonal | (intros; apply GlobalTheory.CompanionTheory.CenTheta.realPart_multiplicative_and_diagonal <;> assumption)
