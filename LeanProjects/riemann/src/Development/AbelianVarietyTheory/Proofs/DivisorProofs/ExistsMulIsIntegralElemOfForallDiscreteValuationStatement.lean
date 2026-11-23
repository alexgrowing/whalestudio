import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulIsIntegralElemOfForallDiscreteValuation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open IsLocalRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_isIntegralElem_of_forall_dvr : ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B), Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) → ∀ (p : Ideal C), p.IsPrime → ∀ f : B, (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) → ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by
  first | exact @GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring | exact GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring | (intros; apply GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring <;> assumption)
