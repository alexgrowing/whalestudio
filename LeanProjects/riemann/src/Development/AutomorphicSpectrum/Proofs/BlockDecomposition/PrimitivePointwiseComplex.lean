import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable

noncomputable section

open MeasureTheory Matrix
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C

namespace GlobalTheory.CompanionTheory.SecTorusC

def sc (c : ℂ) : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) :=
  LinearMap.pi fun i => (if i = 0 then (Algebra.lmul ℝ ℂ c : ℂ →ₗ[ℝ] ℂ) else LinearMap.id).comp (LinearMap.proj i)

def rc (c : ℂ) : M22 →ₗ[ℝ] M22 := LinearMap.pi fun i => (sc c).comp (LinearMap.proj i)

end GlobalTheory.CompanionTheory.SecTorusC
