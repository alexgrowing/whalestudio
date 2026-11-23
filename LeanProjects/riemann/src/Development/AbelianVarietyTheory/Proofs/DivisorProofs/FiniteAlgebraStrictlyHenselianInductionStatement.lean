import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInduction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction : ∀ (A : Type) [CommRing A], SH A → ∀ (P : ∀ (T : Type) [CommRing T] [Algebra A T], Prop),
  (∀ (T T' : Type) [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T'], (T ≃ₐ[A] T') → P T → P T') →
  (∀ (T : Type) [CommRing T] [Algebra A T], Subsingleton T → P T) →
  (∀ (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] [Algebra A T₁] [Algebra A T₂], Module.Finite A T₁ → Module.Finite A T₂ →
    P T₁ → P T₂ → P (T₁ × T₂)) →
  (∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → SH T → P T) →
  ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → P T := by
  first | (exact @GlobalTheory.EtC.GmStep.FinSH.induction_principle) | (exact GlobalTheory.EtC.GmStep.FinSH.induction_principle) | (intros; apply GlobalTheory.EtC.GmStep.FinSH.induction_principle  <;> assumption)
