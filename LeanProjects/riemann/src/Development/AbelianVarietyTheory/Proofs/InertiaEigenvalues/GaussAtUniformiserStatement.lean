import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussAtUniformiser
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonNorm_uniformizer_isStableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → ∃ ϖ : A.Kˣ, (¬ ∃ y, A.NL y = ϖ) ∧ IsStableGauss A ψ x μ ϖ (-(G₁ * ((A.absK ϖ : ℂ))⁻¹)) := by
  first | exact @GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser | exact GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser | (intros; apply GlobalTheory.JR.WeilQuad.NonNorm.gauss_at_uniformiser <;> assumption)
