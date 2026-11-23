import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleTraceAddCharNormEqOneNearZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleTraceAddChar_norm_eq_one_near_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → {y : A.L | A.psiK ψ ((x : A.K) * A.NL y) = 1} ∈ 𝓝 (0 : A.L) := by
  first | exact @GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero | exact GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero | (intros; apply GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero <;> assumption)
