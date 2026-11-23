import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFreeEtaleLift
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_free_etale_lift_of_quotient_etale : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ f ∈ maximalIdeal R, ∀ (E : Type) [CommRing E] [Algebra (R ⧸ Ideal.span {f}) E] [Module.Finite (R ⧸ Ideal.span {f}) E] [Algebra.Etale (R ⧸ Ideal.span {f}) E], ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Module.Finite R B ∧ Module.Free R B ∧ Algebra.Etale R B ∧ Nonempty ((B ⧸ (Ideal.span {f}).map (algebraMap R B)) ≃ₐ[R ⧸ Ideal.span {f}] E) := by
  first | exact @GlobalTheory.EtaleLiftQuot.exists_finite_free_etale_lift | exact GlobalTheory.EtaleLiftQuot.exists_finite_free_etale_lift | (intros; apply GlobalTheory.EtaleLiftQuot.exists_finite_free_etale_lift <;> assumption)
