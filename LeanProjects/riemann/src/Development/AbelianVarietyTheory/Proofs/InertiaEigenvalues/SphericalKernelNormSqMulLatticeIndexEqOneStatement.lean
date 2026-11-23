import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalKernel_normSq_mul_latticeIndex_eq_one : ∀ (D : D7) (T : HSp D) (N : ℕ) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.FinZeta.Gv T v → ℂ), GlobalTheory.FinZeta.IsLocKer T N (GlobalTheory.LFun.val χ) v φ → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) → ∀ a : GlobalTheory.FinZeta.Gv T v, ‖φ a‖ ^ 2 * (latIndex T (GlobalTheory.FinZeta.embV T v a) : ℝ) ^ N = 1 := by
  first | exact @GlobalTheory.LocKerMod.sq_norm_mul_latIndex | exact GlobalTheory.LocKerMod.sq_norm_mul_latIndex | (intros; apply GlobalTheory.LocKerMod.sq_norm_mul_latIndex <;> assumption)
