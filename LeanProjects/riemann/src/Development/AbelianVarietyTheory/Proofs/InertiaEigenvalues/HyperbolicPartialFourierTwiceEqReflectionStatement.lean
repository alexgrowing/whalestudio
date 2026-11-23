import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierTwiceEqReflection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ν : Measure A.K), SelfDual ν (Hyp.kx A ψ x) → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2) := by
  first | exact @GlobalTheory.JR.Hyp.pt_pt_eq_reflect | exact GlobalTheory.JR.Hyp.pt_pt_eq_reflect | (intros; apply GlobalTheory.JR.Hyp.pt_pt_eq_reflect <;> assumption)
