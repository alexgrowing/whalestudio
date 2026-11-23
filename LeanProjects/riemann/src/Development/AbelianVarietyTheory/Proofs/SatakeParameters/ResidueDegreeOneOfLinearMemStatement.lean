import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueDegreeOneOfLinearMem
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_degree_one_of_linear_mem' : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (θ : B) (D a b : A), (P.comap (algebraMap A B)).IsMaximal → (∀ y : B, ∃ u v : A, algebraMap A B D * y = algebraMap A B u + algebraMap A B v * θ) → algebraMap A B D ∉ P → algebraMap A B b ∉ P → algebraMap A B a + algebraMap A B b * θ ∈ P → ∀ y : B, ∃ u : A, y - algebraMap A B u ∈ P := by
  first | exact @GlobalTheory.residue_degree_one_of_linear_mem | exact GlobalTheory.residue_degree_one_of_linear_mem | (intros; apply GlobalTheory.residue_degree_one_of_linear_mem <;> assumption)
