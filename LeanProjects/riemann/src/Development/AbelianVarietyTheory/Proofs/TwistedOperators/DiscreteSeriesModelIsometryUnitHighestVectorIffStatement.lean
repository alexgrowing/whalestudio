import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelIsometryUnitHighestVectorIff
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
theorem _root_.GlobalTheory.T.discreteSeriesModelIsometry_unit_highestVector_iff : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → Module.finrank ℂ ↥(hwSub R.HK.act (blattner lam)) = 1 → ∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v) := by
  first | exact @GlobalTheory.ArchRec.HighTie.highestUnit_iff | exact GlobalTheory.ArchRec.HighTie.highestUnit_iff | (intros; apply GlobalTheory.ArchRec.HighTie.highestUnit_iff <;> assumption)
