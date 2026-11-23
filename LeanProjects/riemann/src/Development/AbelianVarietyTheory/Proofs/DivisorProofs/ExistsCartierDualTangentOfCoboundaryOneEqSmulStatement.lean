import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualTangentOfCoboundaryOneEqSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDual_tangent_of_coboundaryOne_eq_smul : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (b : A) (z : A ⊗[O] A), cobOne O A b = a • z → ∃ u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}, ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  first | exact @GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul | exact GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul | (intros; apply GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul <;> assumption)
