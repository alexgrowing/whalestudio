import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCompHomogeneousIsHomogeneous
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHomogeneous_eval_eq_norm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n d : ℕ) (f : MvPolynomial (Fin n) L), f.IsHomogeneous d → ∃ F : MvPolynomial (Fin n × Fin (Module.finrank K L)) K, F.IsHomogeneous (d * Module.finrank K L) ∧ ∀ y : Fin n × Fin (Module.finrank K L) → K, MvPolynomial.eval y F = Algebra.norm K (MvPolynomial.eval (fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j) f) := by
  first | exact @GlobalTheory.norm_comp_homogeneous_isHomogeneous | exact GlobalTheory.norm_comp_homogeneous_isHomogeneous | (intros; apply GlobalTheory.norm_comp_homogeneous_isHomogeneous <;> assumption)
