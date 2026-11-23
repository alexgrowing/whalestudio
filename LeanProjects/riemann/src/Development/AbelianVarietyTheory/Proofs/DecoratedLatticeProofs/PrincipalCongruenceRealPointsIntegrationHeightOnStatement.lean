import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceRealPointsIntegrationHeightOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_realPoints_integration_heightOne : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Formalism.L2.DIV.IsFrame β (frameLat A) → ∀ m : Measure (GA D A), m.IsHaarMeasure → MeasurableSet (prinInf A β Z) ∧ prinInf A β Z ⊆ openOff A (frameLat A) (under Z) ∧ (∀ g ∈ prinInf A β Z, hgtL A (frameLat A) a g = 1) ∧ ∃ mR : Measure (GinfC A), mR.IsHaarMeasure ∧ ∀ F : GA D A → ℂ, Continuous F → (∀ (b : GinfC A), ∀ κ ∈ prin A β Z, F ((b : GA D A) * κ) = F b) → ∫ g in prinInf A β Z, F g ∂m = ∫ b : GinfC A, F b ∂mR := by
  first | exact @GlobalTheory.Core.Rk.PrinMeas.prinInf_props | exact GlobalTheory.Core.Rk.PrinMeas.prinInf_props | (intros; apply GlobalTheory.Core.Rk.PrinMeas.prinInf_props <;> assumption)
