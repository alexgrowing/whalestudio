import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateSelfReciprocalCharpoly
import Mathlib
import Mathlib
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
import GroundTheory.LocalFields.FilteredSurj
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.conjugate_self_reciprocal_charpoly : ∀ (R : Type) [CommRing R] (s : R →+* R) (n : ℕ) (M : Matrix (Fin n) (Fin n) R), cT s M * M = 1 → GlobalTheory.UTr.IsCsr s M.charpoly := by
  first | exact @GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one | (intros; apply GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one <;> assumption)
