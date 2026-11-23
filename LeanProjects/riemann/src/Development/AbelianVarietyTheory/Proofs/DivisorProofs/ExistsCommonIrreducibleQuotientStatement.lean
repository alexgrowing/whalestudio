import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIrreducibleQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_irreducible_quotient : GlobalTheory.RealLift.MultOne → ∀ (R S : ℕ) (M M' : Formalism.BasicNotions.TH.GKMod R S) (Λ : Formalism.BasicNotions.TH.Ix R S → ℚ), GlobalTheory.RealLift.GenBy M Λ → GlobalTheory.RealLift.GenBy M' Λ → GlobalTheory.RealLift.Steep M Λ → GlobalTheory.RealLift.Steep M' Λ → ∃ (N : Formalism.BasicNotions.TH.GKMod R S) (π : M.V →ₗ[ℂ] N.V) (π' : M'.V →ₗ[ℂ] N.V), GlobalTheory.RealLift.IsQuot M N π ∧ GlobalTheory.RealLift.IsQuot M' N π' ∧ Formalism.MainNotions.SchurIrreducible.IrrGK N ∧ GlobalTheory.RealLift.ScalarEnd N := by
  first | exact @GlobalTheory.CommonQuot.common_quotient | exact GlobalTheory.CommonQuot.common_quotient | (intros; apply GlobalTheory.CommonQuot.common_quotient <;> assumption)
