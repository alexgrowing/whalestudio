import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarRepCommuteAndAnnihilate
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_rep_commute_and_annihilate : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (R : Type) [CommRing R] [Algebra R Λ] (φ : R →+* O) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (∀ c : R, ρ (algebraMap R Λ c) = φ c • (1 : Matrix (Fin h) (Fin h) O)) → (∀ a b : Λ, Commute (Matrix.toLin' ((ρ a).map (algebraMap O C))) (Matrix.toLin' ((ρ b).map (algebraMap O C)))) ∧ ∀ (a : Λ) (f : Polynomial R), Polynomial.aeval a f = 0 → Polynomial.aeval (Matrix.toLin' ((ρ a).map (algebraMap O C))) (f.map ((algebraMap O C).comp φ)) = 0 := by
  first | exact @GlobalTheory.action_commute_and_killed_by_polynomials | exact GlobalTheory.action_commute_and_killed_by_polynomials | (intros; apply GlobalTheory.action_commute_and_killed_by_polynomials <;> assumption)
