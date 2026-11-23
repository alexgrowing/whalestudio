import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPoint
import Mathlib
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint : ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime), P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  first | exact @GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | exact GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | (intros; apply GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint <;> assumption)
