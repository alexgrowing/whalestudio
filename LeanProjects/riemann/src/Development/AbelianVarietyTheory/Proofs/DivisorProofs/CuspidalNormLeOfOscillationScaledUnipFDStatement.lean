import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalNormLeOfOscillationScaledUnipFD
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_norm_le_of_oscillation_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (B : ℝ),
      (∀ X ∈ GroundTheory.Automorphic.scaledUnipFD E a r M, ‖φ (unip X * x) - φ x‖ ≤ B) → ‖φ x‖ ≤ B := by
  first | exact @GlobalTheory.CuspTail.norm_le_of_osc_scaledUnipFD | exact GlobalTheory.CuspTail.norm_le_of_osc_scaledUnipFD | (intros; apply GlobalTheory.CuspTail.norm_le_of_osc_scaledUnipFD <;> assumption)
