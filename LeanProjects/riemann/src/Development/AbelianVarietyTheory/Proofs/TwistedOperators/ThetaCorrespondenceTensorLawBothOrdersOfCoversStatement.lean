import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceTensorLawBothOrdersOfCovers
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCorrespondenceTensorLaw_both_orders_of_covers : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), ARi X lam lam' → ARiiiUp X lam lam' → ARiiiDown X lam lam' → ARiiiLine X lam lam' → TensLaw (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) (X.ds r s lam') (blattner lam) (blattner lam') ∧ TensLaw (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam') (X.ds p q lam) (blattner lam') (blattner lam) := by
  first | exact @GlobalTheory.ArchRec.TensLawOf.tensLaw_of | exact GlobalTheory.ArchRec.TensLawOf.tensLaw_of | (intros; apply GlobalTheory.ArchRec.TensLawOf.tensLaw_of <;> assumption)
