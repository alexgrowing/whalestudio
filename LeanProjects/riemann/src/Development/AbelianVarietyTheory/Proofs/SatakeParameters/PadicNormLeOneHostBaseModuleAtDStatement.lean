import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormLeOneHostBaseModuleAtD
import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralEigenCombination
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_norm_le_one_host_base_module_at_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (φ : D.host.E →+* ℂ_[p]) (a : D.host.E), a ∈ D.host.AA0 → ‖φ a‖ ≤ 1 := by
  first | exact @GlobalTheory.IntegralAtPlace.norm_le_one | exact GlobalTheory.IntegralAtPlace.norm_le_one | (intros; apply GlobalTheory.IntegralAtPlace.norm_le_one <;> assumption)
