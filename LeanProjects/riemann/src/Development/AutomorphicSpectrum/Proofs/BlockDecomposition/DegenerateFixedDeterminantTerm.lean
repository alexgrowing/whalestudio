import Mathlib
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD

noncomputable section

open MeasureTheory Matrix Ad3 Ad3.LR

namespace GlobalTheory.CompanionTheory.GodementKFin

def euc : M23 ≃L[ℝ] EuclideanSpace ℝ (Fin 2 × Fin 3) :=
  (((LinearEquiv.curry ℝ ℝ (Fin 2) (Fin 3)).symm).trans
    (WithLp.linearEquiv 2 ℝ (Fin 2 × Fin 3 → ℝ)).symm).toContinuousLinearEquiv

def gau : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ euc
    (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin 2 × Fin 3)))

def zc (c : Fin 3) (X : M23) : ℂ := ((X 0 c : ℝ) : ℂ) + ((X 1 c : ℝ) : ℂ) * Complex.I

def mono (e : ℕ × ℕ × ℕ) (X : M23) : ℂ := zc 0 X ^ e.1 * zc 1 X ^ e.2.1 * zc 2 X ^ e.2.2

def mg (e : ℕ × ℕ × ℕ) : Sw := SchwartzMap.smulLeftCLM ℂ (mono e) gau

def Fs (n : ℕ) : Submodule ℂ Sw :=
  Submodule.span ℂ (mg '' ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) :
    Finset (ℕ × ℕ × ℕ)) : Set (ℕ × ℕ × ℕ)))

instance Fs_finiteDimensional (n : ℕ) : FiniteDimensional ℂ (Fs n) :=
  FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet _).image _)

end GlobalTheory.CompanionTheory.GodementKFin
