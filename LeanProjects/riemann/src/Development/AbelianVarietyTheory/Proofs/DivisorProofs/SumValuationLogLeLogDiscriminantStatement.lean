import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumValuationLogLeLogDiscriminant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_valuation_log_le_log_discriminant : ∀ (D : D7) (T : Finset ℕ), (∀ p ∈ T, p.Prime) →
    ∑ p ∈ T, vDiff D.host.E p * Real.log p ≤ Real.log D.host.rdE := by
  first | exact @GlobalTheory.PlaceBd.sum_vDiff_mul_log_le_log_rdE | exact GlobalTheory.PlaceBd.sum_vDiff_mul_log_le_log_rdE | (intros; apply GlobalTheory.PlaceBd.sum_vDiff_mul_log_le_log_rdE <;> assumption)
