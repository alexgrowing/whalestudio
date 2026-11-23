import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfulRepMulVecInjective
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faithful_rep_mulVec_injective : ∀ (R Λ : Type) [CommRing R] [IsDomain R] [CommRing Λ] [IsDomain Λ] [Algebra R Λ] [Module.Finite R Λ] [FaithfulSMul R Λ] (h : ℕ) (ρ : Λ →ₐ[R] Matrix (Fin h) (Fin h) R) (a : Λ) (x : Fin h → R), a ≠ 0 → (ρ a).mulVec x = 0 → x = 0 := by
  first | exact @GlobalTheory.torsionFree_of_finite_domain_action' | exact GlobalTheory.torsionFree_of_finite_domain_action' | (intros; apply GlobalTheory.torsionFree_of_finite_domain_action' <;> assumption)
