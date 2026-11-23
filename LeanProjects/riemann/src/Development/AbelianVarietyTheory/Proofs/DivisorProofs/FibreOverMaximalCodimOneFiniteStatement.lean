import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreOverMaximalCodimOneFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_over_maximal_codim_one_finite : ∀ (X : Scheme.{0}) [IsIntegral X] [IsNoetherian X] [Ring.DimensionLEOne Γ(X, ⊤)] (P : Ideal Γ(X, ⊤))
    (t : Γ(X, ⊤)), P.IsMaximal → t ∈ P → t ≠ 0 →
      {z : X | GlobalTheory.SteinFibre.under z = P ∧ Order.coheight z = 1}.Finite ∧
      ∀ x : X, GlobalTheory.SteinFibre.under x = P → ∃ z : X, GlobalTheory.SteinFibre.under z = P ∧ Order.coheight z = 1 ∧ z ⤳ x := by
  first | exact @GlobalTheory.SteinFibre.finite_coheight_one_and_exists_specializes | exact GlobalTheory.SteinFibre.finite_coheight_one_and_exists_specializes | (intros; apply GlobalTheory.SteinFibre.finite_coheight_one_and_exists_specializes <;> assumption)
