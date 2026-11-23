import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDvdOfAevalEqZero
import Mathlib
import Mathlib
import Formalism.SatakeDualWeyl.StatementF
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
import GroundTheory.LocalFields.FilteredSurj
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt : ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]), M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by
  first | exact @GlobalTheory.SepCharpoly.charpoly_dvd_of_aeval_eq_zero | (intros; apply GlobalTheory.SepCharpoly.charpoly_dvd_of_aeval_eq_zero <;> assumption)
