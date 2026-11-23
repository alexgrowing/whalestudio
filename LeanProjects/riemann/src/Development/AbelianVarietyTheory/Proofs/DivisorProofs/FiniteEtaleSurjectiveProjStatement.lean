import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtaleSurjectiveProj
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftZero
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.Et.TrivTors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_etale_surjective_proj : ∀ (n : ℕ), n ≠ 0 → ∀ (V : Scheme.{0}), IsFinite (proj n V) ∧ Etale (proj n V) ∧ Surjective (proj n V) := by
  first | (exact @GlobalTheory.Et.TrivTors.proj_finite_etale_surjective) | (exact GlobalTheory.Et.TrivTors.proj_finite_etale_surjective) | (intros; apply GlobalTheory.Et.TrivTors.proj_finite_etale_surjective  <;> assumption)
