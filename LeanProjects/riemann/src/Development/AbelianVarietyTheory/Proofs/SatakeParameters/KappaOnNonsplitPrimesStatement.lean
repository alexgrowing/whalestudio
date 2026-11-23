import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KappaOnNonsplitPrimes
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_on_nonsplit_primes : ∀ D : D7, KappaOn (fun D p => ¬ SplitK D p) D := by
  first | exact @GlobalTheory.ThLoc.kappaNonSplit | exact GlobalTheory.ThLoc.kappaNonSplit | (intros; apply GlobalTheory.ThLoc.kappaNonSplit <;> assumption)
