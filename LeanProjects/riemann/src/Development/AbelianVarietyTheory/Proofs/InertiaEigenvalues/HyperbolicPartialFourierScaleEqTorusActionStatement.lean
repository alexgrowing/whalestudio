import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierScaleEqTorusAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicPartialFourier_scale_eq_torusAction : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (x : A.K) (s : A.Kˣ) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => (A.absK (s : A.K) : ℂ) * Φ ((s : A.K) * p.1, (s : A.K) * p.2)) = Hyp.rg A (mS s) (Hyp.pt A ν ψ x Φ) := by
  first | exact @GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS | exact GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS | (intros; apply GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS <;> assumption)
