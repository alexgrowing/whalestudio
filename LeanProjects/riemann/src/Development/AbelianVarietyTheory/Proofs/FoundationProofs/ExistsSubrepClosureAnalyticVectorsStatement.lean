import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubrepClosureAnalyticVectors
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subrep_closure_analytic_vectors : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (πU : URep T) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (E : V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (act Y x)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖E ((act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ (σ : URep T) (j : V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ (∀ g y, J (σ.π g y) = πU.π g (J y)) ∧ (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (act Y x)) 0) := by
  first | exact @GlobalTheory.AnalyticClosure.exists_subrep_closure | exact GlobalTheory.AnalyticClosure.exists_subrep_closure | (intros; apply GlobalTheory.AnalyticClosure.exists_subrep_closure <;> assumption)
