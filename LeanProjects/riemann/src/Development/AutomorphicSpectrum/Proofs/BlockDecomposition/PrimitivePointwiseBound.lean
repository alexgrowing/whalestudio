import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.ComplexMatrixMajorantIntegrable

noncomputable section

open MeasureTheory Complex
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.SecTorus

def sc (c : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' (Matrix.diagonal ![c, 1])

def rc (c : ℝ) : M22 →ₗ[ℝ] M22 := LinearMap.pi fun i => (sc c).comp (LinearMap.proj i)

end GlobalTheory.CompanionTheory.SecTorus
