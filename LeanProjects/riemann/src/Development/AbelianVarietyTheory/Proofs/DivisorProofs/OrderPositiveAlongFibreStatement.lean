import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderPositiveAlongFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_positive_along_fibre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (z : X) (t : Γ(X, ⊤)),
    t ∈ GlobalTheory.SteinFibre.under z → t ≠ 0 → Order.coheight z = 1 →
      0 < Scheme.ord (algebraMap Γ(X, ⊤) X.functionField t) z := by
  first | exact @GlobalTheory.SteinFibre.ord_pos_of_mem_under | exact GlobalTheory.SteinFibre.ord_pos_of_mem_under | (intros; apply GlobalTheory.SteinFibre.ord_pos_of_mem_under <;> assumption)
